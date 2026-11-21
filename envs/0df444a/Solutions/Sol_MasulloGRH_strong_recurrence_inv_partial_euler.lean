-- Prove2me | solution 1 for MasulloGRH.strong_recurrence_inv_partial_euler
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:05:31.905923+00:00
-- url     : https://prove2.me/submissions/304f8a35-3f50-43ca-9790-590a0f7a9e39

import Definitions.Def_MasulloGRH_IdeleNorm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Set Filter
open scoped Topology

private theorem compact_returns {H : Type*} [AddCommGroup H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [CompactSpace H]
    (φ : ℝ →+ H) (hφ : Continuous φ)
    (U : Set H) (hU : U ∈ 𝓝 0) :
    ∃ F : Finset ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, ∃ r ∈ F, ∀ h : ℝ, |h| < δ → φ (t - r + h) ∈ U := by
  have hs : ((fun z : H × H => z.1 + z.2) ⁻¹' U) ∈ 𝓝 ((0 : H), (0 : H)) := by
    apply continuous_add.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨V, hV, W, hW, hprod⟩ := mem_nhds_prod_iff.mp hs
  obtain ⟨O, hOV, hO, hzero⟩ := mem_nhds_iff.mp hV
  let B (r : ℝ) : Set H := (fun x : H => x - φ r) ⁻¹' O
  have hopen (r : ℝ) : IsOpen (B r) := hO.preimage (continuous_id.sub continuous_const)
  have hcov : closure (range φ) ⊆ ⋃ r, B r := by
    intro x hx
    have hpre : IsOpen ((fun a : H => x - a) ⁻¹' O) :=
      hO.preimage (continuous_const.sub continuous_id)
    obtain ⟨y, hy, r, rfl⟩ := mem_closure_iff.mp hx _ hpre (show (x - x) ∈ O by simpa using hzero)
    exact mem_iUnion.mpr ⟨r, hy⟩
  obtain ⟨F, hF⟩ := (isClosed_closure.isCompact).elim_finite_subcover B hopen hcov
  have hp : φ ⁻¹' W ∈ 𝓝 0 := hφ.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hp
  refine ⟨F, δ, hδ, ?_⟩
  intro t
  obtain ⟨r, hr⟩ := mem_iUnion.mp (hF (subset_closure (mem_range_self t)))
  obtain ⟨hrF, htr⟩ := mem_iUnion.mp hr
  refine ⟨r, hrF, ?_⟩
  intro h hh
  have h₁ : φ t - φ r ∈ V := hOV htr
  have h₂ : φ h ∈ W := hball (by simpa [Metric.mem_ball, Real.dist_eq] using hh)
  simpa only [Set.mem_preimage, map_add, map_sub] using (hprod (show (φ t - φ r, φ h) ∈ V ×ˢ W from ⟨h₁, h₂⟩))


open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem finite_shift_volume (A : Set ℝ) (F : Finset ℝ)
    (hc : ∀ t : ℝ, ∃ r ∈ F, t - r ∈ A)
    (M : ℝ) (hM : ∀ r ∈ F, |r| ≤ M) (a b : ℝ) :
    b - a - 2 * M ≤ (F.card : ℝ) * (volume (Icc a b ∩ A)).toReal := by
  let B := Icc a b ∩ A
  let B' (r : ℝ) := (fun x : ℝ => x - r) ⁻¹' B
  have hcov : Icc (a + M) (b - M) ⊆ ⋃ r ∈ F, B' r := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := hc x
    refine mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, ?_⟩⟩
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hM r hr)
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hxr⟩
  have htr (r : ℝ) : volume (B' r) = volume B := by
    simp [B', sub_eq_add_neg, measure_preimage_add_right]
  have hbfin : volume B < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) (measure_Icc_lt_top)
  have hbnd : volume (Icc (a + M) (b - M)) ≤ (F.card : ℝ≥0∞) * volume B := by
    calc
      _ ≤ volume (⋃ r ∈ F, B' r) := measure_mono hcov
      _ ≤ _ := measure_biUnion_finset_le F B'
      _ = _ := by simp [htr]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hbfin.ne) hbnd
  rw [← Measure.real_def, Real.volume_real_Icc, ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  linarith [le_max_left (b - M - (a + M)) 0]

private noncomputable def ud (A : Set ℝ) :=
  limsup (fun T : ℝ => (volume (Icc (-T) T ∩ A)).toReal / (2*T)) atTop

theorem finite_shift_density (A : Set ℝ) (F : Finset ℝ)
    (hc : ∀ t : ℝ, ∃ r ∈ F, t - r ∈ A) :
    0 < ud {t : ℝ | 0 ≤ t ∧ t ∈ A} ∧ 0 < ud {t : ℝ | t ≤ 0 ∧ t ∈ A} := by
  obtain ⟨r, hr, _⟩ := hc 0
  have hn : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨r,hr⟩
  let M := ∑ r ∈ F, |r|
  have hM (r) (hr : r ∈ F) : |r| ≤ M :=
    Finset.single_le_sum (fun x _ => abs_nonneg x) hr
  have aux (X : Set ℝ)
      (hl : ∀ᶠ T : ℝ in atTop, T/2 ≤ (F.card : ℝ) * (volume (Icc (-T) T ∩ X)).toReal) :
      0 < ud X := by
    have hu : ∀ᶠ T : ℝ in atTop, (volume (Icc (-T) T ∩ X)).toReal / (2*T) ≤ 1 := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
      rw [div_le_iff₀ (by positivity)]
      have hm := ENNReal.toReal_mono (show volume (Icc (-T) T) ≠ ⊤ from measure_Icc_lt_top.ne)
        (measure_mono (inter_subset_left : Icc (-T) T ∩ X ⊆ Icc (-T) T))
      change (volume (Icc (-T) T ∩ X)).toReal ≤ volume.real (Icc (-T) T) at hm
      rw [Real.volume_real_Icc_of_le (by linarith)] at hm
      linarith
    have hlow : ∀ᶠ T : ℝ in atTop,
        1 / (4 * (F.card : ℝ)) ≤ (volume (Icc (-T) T ∩ X)).toReal / (2*T) := by
      filter_upwards [hl, eventually_gt_atTop (0:ℝ)] with T h hT
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith
    exact lt_of_lt_of_le (by positivity : 0 < 1 / (4 * (F.card : ℝ)))
      (le_limsup_of_frequently_le hlow.frequently (isBoundedUnder_of_eventually_le hu))
  constructor
  · apply aux
    filter_upwards [eventually_ge_atTop (4*M), eventually_ge_atTop (0:ℝ)] with T hT hT₀
    have h := finite_shift_volume A F hc M hM 0 T
    have heq : Icc (-T) T ∩ {t : ℝ | 0 ≤ t ∧ t ∈ A} = Icc 0 T ∩ A := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨_,hx⟩,h0,hA⟩
        exact ⟨⟨h0,hx⟩,hA⟩
      · rintro ⟨⟨h0,hx⟩, hA⟩
        exact ⟨⟨by linarith,hx⟩,h0,hA⟩
    rw [heq]
    linarith
  · apply aux
    filter_upwards [eventually_ge_atTop (4*M), eventually_ge_atTop (0:ℝ)] with T hT hT₀
    have h := finite_shift_volume A F hc M hM (-T) 0
    have heq : Icc (-T) T ∩ {t : ℝ | t ≤ 0 ∧ t ∈ A} = Icc (-T) 0 ∩ A := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hx,_⟩,h0,hA⟩
        exact ⟨⟨hx,h0⟩,hA⟩
      · rintro ⟨⟨hx,h0⟩, hA⟩
        exact ⟨⟨hx,by linarith⟩,h0,hA⟩
    rw [heq]
    linarith

private theorem phase_flow_density {H : Type*} [AddCommGroup H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] [CompactSpace H]
    (φ : ℝ →+ H) (hφ : Continuous φ) (K : Set ℂ) (hK : IsCompact K) (hKne : K.Nonempty)
    (P : ℂ × H → ℂ) (hP : Continuous P) (ε : ℝ) (hε : 0 < ε) :
    let A := {t : ℝ | sSup ((fun s : ℂ => ‖P (s, φ t) - P (s,0)‖) '' K) < ε}
    0 < ud {t : ℝ | 0 ≤ t ∧ t ∈ A} ∧ 0 < ud {t : ℝ | t ≤ 0 ∧ t ∈ A} := by
  let Ω : Set (ℂ × H) := {z | ‖P z - P (z.1,0)‖ < ε/2}
  have hΩ : IsOpen Ω := isOpen_lt (hP.sub (hP.comp (continuous_fst.prodMk continuous_const))).norm
    continuous_const
  have hsub : K ×ˢ ({0} : Set H) ⊆ Ω := by
    rintro ⟨s,z⟩ ⟨_,hz⟩
    have hz' : z = 0 := hz
    simpa [Ω,hz'] using (half_pos hε)
  obtain ⟨V,W,_,hW,hV,h0,hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hΩ hsub
  obtain ⟨F,δ,hδ,hF⟩ := compact_returns φ hφ W (hW.mem_nhds (h0 (mem_singleton 0)))
  apply finite_shift_density _ F
  intro t
  obtain ⟨r,hr,hh⟩ := hF t
  refine ⟨r,hr,?_⟩
  have hw : φ (t-r) ∈ W := by simpa using hh 0 (by simpa using hδ)
  apply lt_of_le_of_lt (csSup_le (hKne.image _) ?_) (half_lt_self hε)
  rintro _ ⟨s,hs,rfl⟩
  exact le_of_lt (hVW (show (s,φ (t-r)) ∈ V ×ˢ W from ⟨hV hs,hw⟩))



private theorem euler_model_density {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (a : ι → ℂ)
    (K : Set ℂ) (hK : IsCompact K) (hKne : K.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    let P (s : ℂ) := ∏ i, (1 - a i * (q i : ℂ) ^ (-s))
    let A := {t : ℝ | sSup ((fun s : ℂ => ‖P (s + t * Complex.I) - P s‖) '' K) < ε}
    0 < ud {t : ℝ | 0 ≤ t ∧ t ∈ A} ∧ 0 < ud {t : ℝ | t ≤ 0 ∧ t ∈ A} := by
  let H := ι → Additive Circle
  let φ : ℝ →+ H := {
    toFun := fun t i => Additive.ofMul (Circle.exp (-t * Real.log (q i)))
    map_zero' := by
      funext i
      change Circle.exp (-(0 : ℝ) * Real.log (q i)) = 1
      simp
    map_add' := by
      intro t u
      funext i
      change Circle.exp (-(t+u) * Real.log (q i)) =
        Circle.exp (-t * Real.log (q i)) * Circle.exp (-u * Real.log (q i))
      rw [← Circle.exp_add]
      congr 1
      ring }
  have hφ : Continuous φ := by
    apply continuous_pi
    intro i
    change Continuous (fun t : ℝ => Circle.exp (-t * Real.log (q i)))
    exact Circle.exp.continuous.comp (continuous_id.neg.mul continuous_const)
  let P (z : ℂ × H) := ∏ i, (1 - a i * (q i : ℂ)^(-z.1) * ((z.2 i).toMul : ℂ))
  have hqc (i : ι) : (q i : ℂ) ≠ 0 := by exact_mod_cast (hq i).ne'
  have hP : Continuous P := by
    apply continuous_finsetProd
    intro i _
    let _ : NeZero (q i : ℂ) := ⟨hqc i⟩
    have h₁ := continuous_const_cpow (q i : ℂ)
    have h₂ : Continuous (fun z : ℂ × H => ((z.2 i).toMul : ℂ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact continuous_const.sub ((continuous_const.mul (h₁.comp continuous_fst.neg)).mul h₂)
  have hPs (s : ℂ) (t : ℝ) : P (s, φ t) =
      ∏ i, (1 - a i * (q i : ℂ)^(-(s + (t : ℂ) * Complex.I))) := by
    apply Finset.prod_congr rfl
    intro i _
    change 1 - a i * (q i : ℂ)^(-s) * ((Circle.exp (-t * Real.log (q i)) : Circle) : ℂ) = _
    rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (hqc i), Complex.cpow_def_of_ne_zero (hqc i),
      ← Complex.ofReal_log (hq i).le, mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring
  have hP0 (s : ℂ) : P (s,0) = ∏ i, (1 - a i * (q i : ℂ)^(-s)) := by simpa using hPs s 0
  simpa only [hPs, hP0] using phase_flow_density φ hφ K hK hKne P hP ε hε


open MasulloGRH NumberField IsDedekindDomain

theorem solution
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : HeckeCharacter F) (_hχ : ∀ v ∈ S, χ.IsUnramifiedAt v)
    (a b : ℝ) (_ha : a < 0) (_hb : 0 < b)
    (K : Set ℂ) (hK : IsCompact K) (_hKI : K ⊆ {s : ℂ | a < s.re ∧ s.re < b}) (hKint : (interior K).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    0 < upperDensity {t : ℝ | 0 ≤ t ∧
      sSup ((fun s : ℂ => ‖∏ v ∈ S, eulerFactorInv χ v (s + t * Complex.I) -
        ∏ v ∈ S, eulerFactorInv χ v s‖) '' K) < ε} ∧
    0 < upperDensity {t : ℝ | t ≤ 0 ∧
      sSup ((fun s : ℂ => ‖∏ v ∈ S, eulerFactorInv χ v (s + t * Complex.I) -
        ∏ v ∈ S, eulerFactorInv χ v s‖) '' K) < ε} := by
  classical
  let q (v : S) : ℝ := (Ideal.absNorm v.1.asIdeal : ℕ)
  have hq (v : S) : 0 < q v := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v.1))
  have hprod (s : ℂ) :
      (∏ v : S, (1 - χ.primeValue v.1 * (q v : ℂ)^(-s))) = ∏ v ∈ S, eulerFactorInv χ v s := by
    rw [← Finset.prod_coe_sort S (fun v => eulerFactorInv χ v s)]
    simp [q,eulerFactorInv,primeNorm]
  have hm := euler_model_density q hq (fun v : S => χ.primeValue v.1) K hK
    (hKint.mono interior_subset) ε hε
  simpa only [hprod,ud,upperDensity,mem_ofPred_eq] using hm