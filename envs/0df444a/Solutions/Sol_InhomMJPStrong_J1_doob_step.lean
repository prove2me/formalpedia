-- Prove2me | solution 1 for InhomMJPStrong.J1.doob_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:47:56.028291+00:00
-- url     : https://prove2.me/submissions/dfb7f1f5-9e96-4cca-b262-6f0569b330f7

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
open InhomMJPStrong.J1

namespace J1Doob

lemma gammaPDF_one_toReal (r x : ℝ) (hr : 0 < r) :
    (gammaPDF 1 r x).toReal = if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x), gammaPDFReal]
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]

lemma ae_ne_zero : ∀ᵐ x : ℝ, x ≠ 0 := by
  have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
  exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx

lemma integrable_pow_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (expMeasure r) := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul' hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ)) (p := 1) (b := r)
    (by have : (0:ℝ) ≤ p := Nat.cast_nonneg p
        linarith) one_pos hr
  have h2 : Integrable (Set.indicator (Ioi 0)
      (fun x : ℝ => r * (x ^ (p : ℝ) * Real.exp (-r * x ^ (1 : ℝ))))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 (Integrable.const_mul h r)
  refine h2.congr ?_
  filter_upwards [ae_ne_zero] with x hx
  rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
  · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le, Real.rpow_natCast, Real.rpow_one,
      abs_of_pos hpos]
    ring_nf

lemma integral_id_exp {r : ℝ} (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = 1 / r := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h1 : ∫ x : ℝ, (gammaPDF 1 r x).toReal • x =
      ∫ x : ℝ, Set.indicator (Ioi 0) (fun x : ℝ => r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x)))) x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with x hx
    rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
    · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le]
      norm_num
      ring
  rw [h1, integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hr, Real.Gamma_two]
  rw [Real.rpow_two]
  field_simp

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The natural filtration `σ(g_j : j < l)`. -/
noncomputable def filt (g : ℕ → Ω → ℝ) (hg : ∀ i, Measurable (g i)) : Filtration ℕ mΩ where
  seq l := ⨆ j ∈ {j : ℕ | j < l}, MeasurableSpace.comap (g j) inferInstance
  mono' a b hab := biSup_mono fun j hj => lt_of_lt_of_le hj hab
  le' l := iSup₂_le fun j _ => (hg j).comap_le

lemma meas_filt (g : ℕ → Ω → ℝ) (hg : ∀ i, Measurable (g i)) {i l : ℕ} (hil : i < l) :
    Measurable[filt g hg l] (g i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun (j : ℕ) (_ : j ∈ {j : ℕ | j < l}) =>
    MeasurableSpace.comap (g j) inferInstance) i hil

/-- The centred partial sums. -/
noncomputable def Mp (g : ℕ → Ω → ℝ) (n : ℕ) (l : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range l, g i ω - (l : ℝ) / n

lemma adapted_M (g : ℕ → Ω → ℝ) (hg : ∀ i, Measurable (g i)) (n : ℕ) :
    StronglyAdapted (filt g hg) (Mp g n) := fun l => by
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.sub ?_ measurable_const
  exact Finset.measurable_sum _ fun i hi => meas_filt g hg (Finset.mem_range.1 hi)

variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma memLp_g {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (i k : ℕ) (hk : k ≠ 0) :
    MemLp (g i) k P := by
  have hint : Integrable (fun x : ℝ => |x| ^ k) (expMeasure n) := integrable_pow_exp hn k
  rw [← (hgLaw i).map_eq] at hint
  have h2 := (integrable_map_measure hint.aestronglyMeasurable (hgLaw i).aemeasurable).1 hint
  rw [← integrable_norm_rpow_iff (hgLaw i).aemeasurable.aestronglyMeasurable
    (by simpa using hk) (by simp)]
  refine h2.congr (ae_of_all _ fun ω => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast]

lemma memLp_M {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l k : ℕ) (hk : k ≠ 0) :
    MemLp (Mp g n l) k P :=
  (memLp_finset_sum (Finset.range l) fun i _ => memLp_g hn hgLaw i k hk).sub (memLp_const _)

lemma integrable_fM {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ}
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l k : ℕ) :
    Integrable (fun ω => (Mp g n l ω) ^ (2 * k)) P := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; simp
  have h := (memLp_M hn hgLaw l (2 * k) (by omega)).integrable_norm_pow (by omega)
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact (even_two_mul k).pow_abs _

lemma condExp_M {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ} (hg : ∀ i, Measurable (g i))
    (hgIndep : iIndepFun g P) (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (l : ℕ) :
    P[Mp g n (l + 1) | filt g hg l] =ᵐ[P] Mp g n l := by
  have hsplit : Mp g n (l + 1) = Mp g n l + fun ω => g l ω - 1 / n := by
    funext ω; simp only [Mp, Finset.sum_range_succ, Pi.add_apply]; push_cast; ring
  rw [hsplit]
  have hMint : Integrable (Mp g n l) P := (memLp_M hn hgLaw l 1 one_ne_zero).integrable (by norm_num)
  have hgint : Integrable (g l) P := (memLp_g hn hgLaw l 1 one_ne_zero).integrable (by norm_num)
  have hYint : Integrable (fun ω => g l ω - 1 / n) P := hgint.sub (integrable_const _)
  refine (condExp_add hMint hYint _).trans ?_
  have h1 : P[Mp g n l | filt g hg l] = Mp g n l :=
    condExp_of_stronglyMeasurable ((filt g hg).le l) (adapted_M g hg n l) hMint
  have hind : Indep (MeasurableSpace.comap (g l) inferInstance) (filt g hg l) P := by
    have hi := (iIndepFun_iff_iIndep _ g P).1 hgIndep
    have := indep_iSup_of_disjoint (fun i => (hg i).comap_le) hi
      (S := {l}) (T := {j | j < l}) (Set.disjoint_singleton_left.2 (lt_irrefl l))
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at this
    exact this
  have h2 : P[fun ω => g l ω - 1 / n | filt g hg l] =ᵐ[P] fun _ => P[fun ω => g l ω - 1 / n] :=
    condExp_indep_eq (hg l).comap_le ((filt g hg).le l)
      ((comap_measurable (g l)).sub_const _).stronglyMeasurable hind
  have h3 : P[fun ω => g l ω - 1 / n] = 0 := by
    rw [integral_sub hgint (integrable_const _), (hgLaw l).integral_eq, integral_id_exp hn]
    simp
  filter_upwards [h2] with ω hω
  simp only [Pi.add_apply, h1, hω, h3, add_zero]

lemma submart {n : ℕ} (hn : (0:ℝ) < n) {g : ℕ → Ω → ℝ} (hg : ∀ i, Measurable (g i))
    (hgIndep : iIndepFun g P) (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P) (k : ℕ) :
    Submartingale (fun l ω => (Mp g n l ω) ^ (2 * k)) (filt g hg) P := by
  refine submartingale_nat (fun l => ?_) (fun l => integrable_fM hn hgLaw l k) (fun l => ?_)
  · exact ((adapted_M g hg n l).measurable.pow_const _).stronglyMeasurable
  · have hMint : Integrable (Mp g n (l + 1)) P :=
      (memLp_M hn hgLaw (l + 1) 1 one_ne_zero).integrable (by norm_num)
    have hJ := ConvexOn.map_condExp_le ((filt g hg).le l) ((even_two_mul k).convexOn_pow)
      ((continuous_pow (2 * k)).lowerSemicontinuous.lowerSemicontinuousOn univ)
      (ae_of_all _ fun _ => mem_univ _) isClosed_univ hMint (integrable_fM hn hgLaw (l + 1) k)
    filter_upwards [hJ, condExp_M hn hg hgIndep hgLaw l] with ω h1 h2
    simp only [Function.comp] at h1
    rw [h2] at h1
    exact h1

lemma doob_meas (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (g : ℕ → Ω → ℝ) (hg : ∀ i, Measurable (g i))
    (hgIndep : iIndepFun g P) (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P)
    (beta : ℝ) (hbeta : 0 < beta) (k : ℕ) :
    P {ω | beta ≤ maxGap (fun l => InhomMJPStrong.J1.arrival (fun i => g i ω) l)
        (fun l => (l : ℝ) / (n : ℝ)) m} ≤
      ENNReal.ofReal
        ((∫ ω, (InhomMJPStrong.J1.arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P) /
          beta ^ (2 * k)) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hsub := submart hnr hg hgIndep hgLaw k
  have hnn : 0 ≤ fun l ω => (Mp g n l ω) ^ (2 * k) := fun l ω => (even_two_mul k).pow_nonneg _
  have hbk : 0 < beta ^ (2 * k) := pow_pos hbeta _
  have hmax := maximal_ineq hsub hnn (ε := (beta ^ (2 * k)).toNNReal) m
  rw [Real.coe_toNNReal _ hbk.le] at hmax
  set A := {ω | beta ^ (2 * k) ≤ (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      fun l => (Mp g n l ω) ^ (2 * k)} with hA
  have hI : ∫ ω in A, (Mp g n m ω) ^ (2 * k) ∂P ≤
      ∫ ω, (InhomMJPStrong.J1.arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P :=
    setIntegral_le_integral (integrable_fM hnr hgLaw m k)
      (ae_of_all _ fun ω => (even_two_mul k).pow_nonneg _)
  have hincl : {ω | beta ≤ maxGap (fun l => InhomMJPStrong.J1.arrival (fun i => g i ω) l)
        (fun l => (l : ℝ) / (n : ℝ)) m} ⊆ A := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    unfold InhomMJPStrong.J1.maxGap at hω
    split_ifs at hω with hne
    · obtain ⟨l0, hl0, heq⟩ := Finset.exists_mem_eq_sup' hne
        (fun l => |InhomMJPStrong.J1.arrival (fun i => g i ω) l - (l : ℝ) / n|)
      rw [heq] at hω
      rw [Finset.mem_Icc] at hl0
      show beta ^ (2 * k) ≤ _
      calc beta ^ (2 * k) ≤ |InhomMJPStrong.J1.arrival (fun i => g i ω) l0 - (l0 : ℝ) / n| ^ (2 * k) :=
            pow_le_pow_left₀ hbeta.le hω _
        _ = (Mp g n l0 ω) ^ (2 * k) := by
            rw [(even_two_mul k).pow_abs]; rfl
        _ ≤ _ := Finset.le_sup' (fun l => (Mp g n l ω) ^ (2 * k))
            (Finset.mem_range.2 (by omega))
    · exact absurd hω (not_le.2 hbeta)
  calc P {ω | beta ≤ maxGap (fun l => InhomMJPStrong.J1.arrival (fun i => g i ω) l)
        (fun l => (l : ℝ) / (n : ℝ)) m} ≤ P A := measure_mono hincl
    _ ≤ ENNReal.ofReal (∫ ω, (InhomMJPStrong.J1.arrival (fun i => g i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P)
          / ENNReal.ofReal (beta ^ (2 * k)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hbk)) (Or.inl ENNReal.ofReal_ne_top),
          mul_comm]
        exact hmax.trans (ENNReal.ofReal_le_ofReal hI)
    _ = _ := (ENNReal.ofReal_div_of_pos hbk).symm

end Main

end J1Doob

open InhomMJPStrong.J1 in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P)
    (beta : ℝ) (hbeta : 0 < beta) (k : ℕ) :
    let m := gridSize n eps
    let T : Ω → ℕ → ℝ := fun ω l => arrival (fun i => g i ω) l
    P {ω | beta ≤ maxGap (T ω) (fun l => (l : ℝ) / (n : ℝ)) m} ≤
      ENNReal.ofReal
        ((∫ ω, (T ω m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P) /
          beta ^ (2 * k)) := by
  intro m T
  set g' : ℕ → Ω → ℝ := fun i => (hgLaw i).aemeasurable.mk (g i) with hg'
  have hg'm : ∀ i, Measurable (g' i) := fun i => (hgLaw i).aemeasurable.measurable_mk
  have hae : ∀ i, g i =ᵐ[P] g' i := fun i => (hgLaw i).aemeasurable.ae_eq_mk
  have hI' : iIndepFun g' P := hgIndep.congr hae
  have hL' : ∀ i, HasLaw (g' i) (expMeasure (n : ℝ)) P := fun i => (hgLaw i).congr (hae i).symm
  have hall : ∀ᵐ ω ∂P, ∀ i, g i ω = g' i ω := ae_all_iff.2 hae
  have hT : ∀ᵐ ω ∂P, T ω = fun l => arrival (fun i => g' i ω) l := by
    filter_upwards [hall] with ω hω
    have : (fun i => g i ω) = fun i => g' i ω := funext hω
    show (fun l => arrival (fun i => g i ω) l) = _
    rw [this]
  have hset : {ω | beta ≤ maxGap (T ω) (fun l => (l : ℝ) / (n : ℝ)) m} =ᵐ[P]
      {ω | beta ≤ maxGap (fun l => arrival (fun i => g' i ω) l) (fun l => (l : ℝ) / (n : ℝ)) m} := by
    filter_upwards [hT] with ω hω
    simp only [eq_iff_iff]
    show beta ≤ maxGap (T ω) _ m ↔ _
    rw [hω]
    rfl
  have hint : ∫ ω, (T ω m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P =
      ∫ ω, (arrival (fun i => g' i ω) m - (m : ℝ) / (n : ℝ)) ^ (2 * k) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hT] with ω hω
    simp only [hω]
  rw [measure_congr hset, hint]
  exact J1Doob.doob_meas n hn m g' hg'm hI' hL' beta hbeta k
