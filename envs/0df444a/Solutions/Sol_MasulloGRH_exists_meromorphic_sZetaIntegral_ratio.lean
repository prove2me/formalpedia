-- Prove2me | solution 1 for MasulloGRH.exists_meromorphic_sZetaIntegral_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:45:31.349576+00:00
-- url     : https://prove2.me/submissions/04cafef8-eb2a-4f0f-b193-ac1675815ce5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_properSpace_adicCompletion
import Theorems.Thm_MasulloGRH_exists_small_good_subgroups
import Theorems.Thm_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
import Theorems.Thm_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn
import Theorems.Thm_MasulloGRH_sLocalFourier_schwartzBruhat_equiv
import Theorems.Thm_MasulloGRH_sZetaIntegral_mul_fourier_symm

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

/-!
# Meromorphy of the factor `ρ_S` of the `S`-local functional equation

The factor `ρ_S(c_s) = Z_S(f, c_s) / Z_S(\hat f, \hat{c_s})` is continued to the two half-planes
`σ + Re s < 1` and `σ + Re s > 0` with test functions whose zeta integrals are entire:

* `exists_compact_ne_zero`: for every quasi-character `d` there is a test function `f`, vanishing
  on the ideles outside a compact set, with `Z_S(f, d) ≠ 0` (a bump function near `1`; the
  construction is that of the proof of `MasulloGRH.sZetaIntegral_exists_real_ne_zero`);
* `differentiable_sZetaIntegral_of_isCompact`: for such `f`, `s ↦ Z_S(f, d_s)` is entire;
* `solution`: with `h` and `k` of this kind and `f₂ = T⁻¹ k` (`T` the Fourier automorphism), the
  quotients `Z_S(h, c_s) / Z_S(\hat h, \hat{c_s})` (meromorphic on `σ + Re s < 1`) and
  `Z_S(f₂, c_s) / Z_S(k, \hat{c_s})` (meromorphic on `σ + Re s > 0`) agree on the strip by Tate's
  symmetry lemma `MasulloGRH.sZetaIntegral_mul_fourier_symm`, and glue to a meromorphic function
  on `ℂ`.
-/

open MasulloGRH Topology

namespace Sol_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio

variable {F : Type*} [Field F] [NumberField F]

instance instSCAdic (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have := RiemannMasullo.properSpace_adicCompletion (K := F) v
  exact @secondCountable_of_proper _ _ this

instance instLCAdic (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v

instance instCompactInt (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  RiemannMasullo.compactSpace_adicCompletionIntegers v

omit [NumberField F] in
instance instSCInf (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

omit [NumberField F] in
theorem norm_natCast_inf (v : InfinitePlace F) (n : ℕ) : ‖(n : v.Completion)‖ = n := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
    (map_zero _) (n : v.Completion)
  rw [← h, map_natCast]; simp

omit [NumberField F] in
instance instProperInf (v : InfinitePlace F) : ProperSpace v.Completion := by
  let : NontriviallyNormedField v.Completion := NontriviallyNormedField.ofNormNeOne ⟨(2 : ℕ), by
    have := norm_natCast_inf v 2; intro h; rw [h] at this; norm_num at this, by
    rw [norm_natCast_inf]; norm_num⟩
  exact ProperSpace.of_locallyCompactSpace v.Completion

instance instT2Inf : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

instance instSCInfAdele : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

instance instT2G : T2Space (Multiplicative (SAdeleRing F Sf)) :=
  inferInstanceAs (T2Space (SAdeleRing F Sf))

instance instSCG : SecondCountableTopology (Multiplicative (SAdeleRing F Sf)) :=
  inferInstanceAs (SecondCountableTopology (SAdeleRing F Sf))

/-- The open subgroup `𝔸_∞ × ∏_{v ∈ S_f} 𝒪_v`. -/
def gammaSub : Subgroup (Multiplicative (SAdeleRing F Sf)) where
  carrier := {x | ∀ v : Sf, (Multiplicative.toAdd x).2 v ∈
    (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}
  mul_mem' := by
    intro a b ha hb v
    exact add_mem (ha v) (hb v)
  one_mem' := by
    intro v
    exact zero_mem _
  inv_mem' := by
    intro a ha v
    exact neg_mem (ha v)

theorem mem_gammaSub (x : Multiplicative (SAdeleRing F Sf)) :
    x ∈ gammaSub Sf ↔ ∀ v : Sf, (Multiplicative.toAdd x).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := Iff.rfl

theorem isOpen_adicInt (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_integer _

theorem isOpen_gammaSub : IsOpen ((gammaSub Sf : Set (Multiplicative (SAdeleRing F Sf)))) := by
  have : ((gammaSub Sf : Set (Multiplicative (SAdeleRing F Sf)))) =
      ⋂ v : Sf, (fun x : Multiplicative (SAdeleRing F Sf) => (Multiplicative.toAdd x).2 v) ⁻¹'
        ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F : Set _) := by
    ext x; simp [mem_gammaSub]
  rw [this]
  refine isOpen_iInter_of_finite fun v => ?_
  exact (isOpen_adicInt (v : HeightOneSpectrum (𝓞 F))).preimage
    ((continuous_apply v).comp (continuous_snd.comp continuous_toAdd))


theorem isCompactlyGenerated_gammaSub : IsCompactlyGeneratedSubgroup (gammaSub Sf) := by
  let U : Set (Multiplicative (SAdeleRing F Sf)) :=
    {x | (∀ w : InfinitePlace F, ‖(Multiplicative.toAdd x).1 w‖ ≤ 1) ∧
      ∀ v : Sf, (Multiplicative.toAdd x).2 v ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F}
  have hUeq : U = (Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)
      ×ˢ (Set.pi Set.univ fun v : Sf =>
        ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F : Set _)) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun w _ => by rw [Metric.mem_closedBall, dist_zero_right]; exact h1 w, fun v _ => h2 v⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun w => ?_, fun v => h2 v trivial⟩
      have := h1 w trivial
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this
  have hUc : IsCompact U := by
    rw [hUeq]
    refine IsCompact.prod ?_ ?_
    · exact isCompact_univ_pi fun w => isCompact_closedBall _ _
    · exact isCompact_univ_pi fun v => isCompact_iff_compactSpace.mpr (instCompactInt _)
  refine ⟨U, hUc, fun x hx => hx.2, ?_, ?_⟩
  · refine ⟨{x | ∀ w : InfinitePlace F, ‖(Multiplicative.toAdd x).1 w‖ < 1}, ?_, ?_⟩
    · refine Filter.eventually_all.2 fun w => ?_
      have hc : Continuous fun x : Multiplicative (SAdeleRing F Sf) =>
          ‖(Multiplicative.toAdd x).1 w‖ :=
        ((continuous_apply w).comp (continuous_fst.comp continuous_toAdd)).norm
      have h0 : ‖(Multiplicative.toAdd (1 : Multiplicative (SAdeleRing F Sf))).1 w‖ < 1 := by
        show ‖(0 : w.Completion)‖ < 1
        simp
      exact hc.continuousAt.eventually_lt continuousAt_const h0
    · rintro x ⟨hx1, hx2⟩
      exact ⟨fun w => (hx1 w).le, hx2⟩
  · refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.2) ?_
    intro x hx
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ w : InfinitePlace F, ‖(Multiplicative.toAdd x).1 w‖ ≤ n ∧ 0 < n := by
      refine ⟨⌈∑ w, ‖(Multiplicative.toAdd x).1 w‖⌉₊ + 1, fun w => ⟨?_, Nat.succ_pos _⟩⟩
      calc ‖(Multiplicative.toAdd x).1 w‖ ≤ ∑ w, ‖(Multiplicative.toAdd x).1 w‖ :=
            Finset.single_le_sum (f := fun w => ‖(Multiplicative.toAdd x).1 w‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
        _ ≤ ⌈∑ w, ‖(Multiplicative.toAdd x).1 w‖⌉₊ := Nat.le_ceil _
        _ ≤ _ := by exact_mod_cast Nat.le_succ _
    have hn0 : ∀ w : InfinitePlace F, (n : w.Completion) ≠ 0 := by
      intro w h
      have h1 := norm_natCast_inf w n
      rw [h, norm_zero] at h1
      have h2 : (n : ℝ) ≠ 0 := by exact_mod_cast (hn w).2.ne'
      exact h2 h1.symm
    let a : InfiniteAdeleRing F := fun w => (Multiplicative.toAdd x).1 w / (n : w.Completion)
    let y1 : Multiplicative (SAdeleRing F Sf) := Multiplicative.ofAdd (a, 0)
    let y2 : Multiplicative (SAdeleRing F Sf) := Multiplicative.ofAdd (0, (Multiplicative.toAdd x).2)
    have hy1 : y1 ∈ U := by
      refine ⟨fun w => ?_, fun v => zero_mem _⟩
      change ‖(Multiplicative.toAdd x).1 w / (n : w.Completion)‖ ≤ 1
      rw [norm_div, norm_natCast_inf]
      exact div_le_one_of_le₀ (hn w).1 (Nat.cast_nonneg _)
    have hy2 : y2 ∈ U := ⟨fun w => by show ‖(0 : w.Completion)‖ ≤ 1; simp, fun v => hx v⟩
    have hxy : x = y1 ^ n * y2 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_pow]
      refine Prod.ext ?_ ?_
      · funext w
        change (Multiplicative.toAdd x).1 w = n • ((Multiplicative.toAdd x).1 w / (n : w.Completion)) + 0
        rw [add_zero, nsmul_eq_mul, mul_div_cancel₀ _ (hn0 w)]
      · funext w
        change (Multiplicative.toAdd x).2 w = n • (0 : (w : HeightOneSpectrum (𝓞 F)).adicCompletion F) +
          (Multiplicative.toAdd x).2 w
        simp
    rw [hxy]
    exact mul_mem (pow_mem (Subgroup.subset_closure hy1) _) (Subgroup.subset_closure hy2)

theorem circle_norm_lt {δ : ℝ} (hδ0 : 0 < δ) (w : UnitAddCircle)
    (hw : Real.cos (2 * Real.pi * δ) < ((AddCircle.toCircle w : Circle) : ℂ).re) : ‖w‖ < δ := by
  induction w using QuotientAddGroup.induction_on with
  | H t =>
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re] at hw
    rw [AddCircle.norm_eq]
    simp only [inv_one, one_mul, mul_one]
    by_contra h
    push Not at h
    have hu := abs_sub_round t
    have hcos : Real.cos (2 * Real.pi / 1 * t) = Real.cos (2 * Real.pi * |t - round t|) := by
      have h1 : 2 * Real.pi / 1 * t = 2 * Real.pi * (t - round t) + (round t : ℤ) * (2 * Real.pi) := by
        ring
      rw [h1, Real.cos_add_int_mul_two_pi, ← Real.cos_abs (2 * Real.pi * (t - round t)), abs_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [hcos] at hw
    have : Real.cos (2 * Real.pi * |t - round t|) ≤ Real.cos (2 * Real.pi * δ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    linarith


/-- Smoothness and the support/positivity properties of the bump function. -/
theorem exists_bump {m n r s : ℕ} {d : Fin s → ℕ} (p : ElemGroup m n r s d)
    (Ω : Set (ElemGroup m n r s d)) (hΩ : Ω ∈ 𝓝 p) :
    ∃ G : ElemGroup m n r s d → ℝ, Continuous G ∧ (∀ z, 0 ≤ G z) ∧ 0 < G p ∧
      (∀ z, G z ≠ 0 → z ∈ Ω) ∧ IsRapidDecay (fun z => (G z : ℂ)) := by
  classical
  -- a product ball around `p` in the continuous coordinates
  let ι : (Fin m → ℝ) × (Fin n → UnitAddCircle) → ElemGroup m n r s d := fun q => (q.1, q.2, p.2.2)
  have hι : Continuous ι := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hιp : ι (p.1, p.2.1) = p := rfl
  have hpre : ι ⁻¹' Ω ∈ 𝓝 (p.1, p.2.1) := hι.continuousAt.preimage_mem_nhds (by rw [hιp]; exact hΩ)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set δ : ℝ := min (ε / 2) (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set c0 : ℝ := Real.cos (2 * Real.pi * δ) with hc0
  have hc0lt : c0 < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 2 * Real.pi * δ) le_rfl
      (by
        have : δ ≤ 1 / 4 := min_le_right _ _
        nlinarith [Real.pi_pos])
      (by positivity)
    rwa [Real.cos_zero] at h
  let φ : (Fin m → ℝ) → ℝ := fun x => Real.smoothTransition (ε ^ 2 - ∑ i, (x i - p.1 i) ^ 2)
  let ψ : (Fin n → UnitAddCircle) → ℝ := fun z =>
    ∏ j, Real.smoothTransition (((AddCircle.toCircle (z j - p.2.1 j) : Circle) : ℂ).re - c0)
  let χ : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) → ℝ := fun q => if q = p.2.2 then 1 else 0
  let G : ElemGroup m n r s d → ℝ := fun z => φ z.1 * ψ z.2.1 * χ z.2.2
  have hφc : Continuous φ := Real.smoothTransition.continuous.comp
    (continuous_const.sub (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).sub continuous_const).pow 2))
  have hψc : Continuous ψ := continuous_finsetProd _ fun j _ =>
    Real.smoothTransition.continuous.comp ((Complex.continuous_re.comp
      (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
        ((continuous_apply j).sub continuous_const)))).sub continuous_const)
  have hχc : Continuous χ := continuous_of_discreteTopology
  have hφnn : ∀ x, 0 ≤ φ x := fun x => Real.smoothTransition.nonneg _
  have hψnn : ∀ z, 0 ≤ ψ z := fun z => Finset.prod_nonneg fun j _ => Real.smoothTransition.nonneg _
  have hχnn : ∀ q, 0 ≤ χ q := fun q => by by_cases h : q = p.2.2 <;> simp [χ, h]
  have hφsupp : ∀ x, φ x ≠ 0 → dist x p.1 < ε := by
    intro x hx
    have hpos : 0 < ε ^ 2 - ∑ i, (x i - p.1 i) ^ 2 := by
      by_contra h
      exact hx (Real.smoothTransition.zero_of_nonpos (not_lt.mp h))
    refine (dist_pi_lt_iff hε).2 fun i => ?_
    rw [Real.dist_eq]
    have hi : (x i - p.1 i) ^ 2 ≤ ∑ i, (x i - p.1 i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (x i - p.1 i) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact abs_lt_of_sq_lt_sq (by linarith) hε.le
  have hψsupp : ∀ z, ψ z ≠ 0 → dist z p.2.1 < ε := by
    intro z hz
    refine (dist_pi_lt_iff hε).2 fun j => ?_
    have hj := (Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ j)
    have hpos : c0 < ((AddCircle.toCircle (z j - p.2.1 j) : Circle) : ℂ).re := by
      by_contra h
      exact hj (Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.mp h]))
    rw [dist_eq_norm]
    exact (circle_norm_lt hδ0 _ hpos).trans hδε
  refine ⟨G, (hφc.comp continuous_fst).mul (hψc.comp (continuous_fst.comp continuous_snd)) |>.mul
      (hχc.comp (continuous_snd.comp continuous_snd)), fun z => ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (hφnn _) (hψnn _)) (hχnn _)
  · have h1 : 0 < φ p.1 := by
      apply Real.smoothTransition.pos_of_pos
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, sub_zero]
      positivity
    have h2 : 0 < ψ p.2.1 := by
      apply Finset.prod_pos
      intro j _
      apply Real.smoothTransition.pos_of_pos
      have h0 : AddCircle.toCircle (0 : UnitAddCircle) = 1 := by
        have := AddCircle.toCircle_apply_mk (T := 1) 0
        rw [mul_zero, Circle.exp_zero] at this
        exact this
      simp only [sub_self, h0, Circle.coe_one, Complex.one_re]
      linarith
    have h3 : χ p.2.2 = 1 := by simp [χ]
    show 0 < φ p.1 * ψ p.2.1 * χ p.2.2
    rw [h3, mul_one]
    exact mul_pos h1 h2
  · intro z hz
    have hχz : χ z.2.2 ≠ 0 := fun h => hz (by simp [G, h])
    have hφz : φ z.1 ≠ 0 := fun h => hz (by simp [G, h])
    have hψz : ψ z.2.1 ≠ 0 := fun h => hz (by simp [G, h])
    have hq : z.2.2 = p.2.2 := by
      by_contra h
      exact hχz (by simp [χ, h])
    have hmem : (z.1, z.2.1) ∈ Metric.ball (p.1, p.2.1) ε := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (hφsupp _ hφz) (hψsupp _ hψz)
    have : ι (z.1, z.2.1) ∈ Ω := hball hmem
    have hz' : ι (z.1, z.2.1) = z := by
      show (z.1, z.2.1, p.2.2) = z
      rw [← hq]
    rwa [hz'] at this
  · -- rapid decay
    choose c hc using fun j : Fin n => QuotientAddGroup.mk_surjective (p.2.1 j)
    let Ψ : (Fin n → ℝ) → ℝ := fun t =>
      ∏ j, Real.smoothTransition (Real.cos (2 * Real.pi / 1 * (t j - c j)) - c0)
    let H : (Fin m → ℝ) × (Fin n → ℝ) → ℂ := fun xt => ((φ xt.1 * Ψ xt.2 : ℝ) : ℂ)
    have hψΨ : ∀ t : Fin n → ℝ, ψ (fun j => ((t j : ℝ) : UnitAddCircle)) = Ψ t := by
      intro t
      simp only [ψ, Ψ]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
      rw [← hc j]
      have : ((t j : ℝ) : UnitAddCircle) - ((c j : ℝ) : UnitAddCircle) =
          ((t j - c j : ℝ) : UnitAddCircle) := rfl
      rw [show (QuotientAddGroup.mk (c j) : UnitAddCircle) = ((c j : ℝ) : UnitAddCircle) from rfl,
        this, AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
    have hL : ∀ a b, elemLift (fun z => (G z : ℂ)) a b = if (a, b) = p.2.2 then H else 0 := by
      intro a b
      funext xt
      simp only [elemLift, G, χ]
      split_ifs with h
      · simp only [mul_one, H, hψΨ]
      · simp
    have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
      Real.smoothTransition.contDiff.comp (contDiff_const.sub (ContDiff.sum fun i _ =>
        ((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2))
    have hΨs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
      contDiff_prod fun j _ => Real.smoothTransition.contDiff.comp
        ((Real.contDiff_cos.comp (contDiff_const.mul
          ((contDiff_apply ℝ ℝ j).sub contDiff_const))).sub contDiff_const)
    have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H :=
      Complex.ofRealCLM.contDiff.comp ((hφs.comp contDiff_fst).mul (hΨs.comp contDiff_snd))
    have hper : ∀ (v : Fin n → ℤ) (z : (Fin m → ℝ) × (Fin n → ℝ)),
        H (z + ((0 : Fin m → ℝ), fun j => (v j : ℝ))) = H z := by
      intro v z
      have hΨper : Ψ (z.2 + fun j => (v j : ℝ)) = Ψ z.2 := by
        simp only [Ψ]
        refine Finset.prod_congr rfl fun j _ => ?_
        have h1 : 2 * Real.pi / 1 * ((z.2 + fun j => (v j : ℝ)) j - c j) =
            2 * Real.pi / 1 * (z.2 j - c j) + (v j : ℤ) * (2 * Real.pi) := by
          simp only [Pi.add_apply]; ring
        rw [h1, Real.cos_add_int_mul_two_pi]
      simp only [H, Prod.fst_add, Prod.snd_add, add_zero, hΨper]
    have htsupp : tsupport H ⊆ {xt | dist xt.1 p.1 ≤ ε} := by
      refine closure_minimal ?_ (isClosed_le (continuous_fst.dist continuous_const) continuous_const)
      intro xt hxt
      have : φ xt.1 ≠ 0 := by
        intro h
        apply hxt
        simp [H, h]
      exact (hφsupp _ this).le
    have hbound : ∀ i k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ xt, ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k H xt‖ ≤ C := by
      intro i k
      let Φ := fun xt : (Fin m → ℝ) × (Fin n → ℝ) => ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k H xt‖
      have hΦc : Continuous Φ := (continuous_fst.norm.pow i).mul
        (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
      let K := Metric.closedBall p.1 ε ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)
      have hK : IsCompact K :=
        (isCompact_closedBall _ _).prod (isCompact_univ_pi fun _ => isCompact_Icc)
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦc.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun xt => ?_⟩
      by_cases h0 : iteratedFDeriv ℝ k H xt = 0
      · rw [h0, norm_zero, mul_zero]; exact le_max_right _ _
      · have hsupp : xt ∈ tsupport H := support_iteratedFDeriv_subset k h0
        have hx : dist xt.1 p.1 ≤ ε := htsupp hsupp
        let v : Fin n → ℤ := fun j => ⌊xt.2 j⌋
        let xt' : (Fin m → ℝ) × (Fin n → ℝ) := (xt.1, fun j => Int.fract (xt.2 j))
        have hxt : xt = xt' + ((0 : Fin m → ℝ), fun j => (v j : ℝ)) := by
          refine Prod.ext ?_ ?_
          · simp [xt']
          · funext j
            exact (Int.fract_add_floor _).symm
        have hD : iteratedFDeriv ℝ k H xt = iteratedFDeriv ℝ k H xt' := by
          calc iteratedFDeriv ℝ k H xt
              = iteratedFDeriv ℝ k H (xt' + ((0 : Fin m → ℝ), fun j => (v j : ℝ))) := by
                rw [← hxt]
            _ = iteratedFDeriv ℝ k (fun z => H (z + ((0 : Fin m → ℝ), fun j => (v j : ℝ)))) xt' :=
                (iteratedFDeriv_comp_add_right _ _ _).symm
            _ = iteratedFDeriv ℝ k H xt' := by
                rw [show (fun z => H (z + ((0 : Fin m → ℝ), fun j => (v j : ℝ)))) = H from
                  funext fun z => hper v z]
        have hmem : xt' ∈ K := ⟨Metric.mem_closedBall.2 hx,
          fun j _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
        have h1 := hC xt' hmem
        calc ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k H xt‖ = Φ xt' := by simp only [Φ, hD, xt']
          _ ≤ ‖Φ xt'‖ := Real.le_norm_self _
          _ ≤ C := h1
          _ ≤ max C 0 := le_max_left _ _
    refine ⟨fun a b => ?_, fun i j k => ?_⟩
    · rw [hL a b]
      split_ifs
      · exact hH
      · exact contDiff_const
    · obtain ⟨C0, hC0, hC0b⟩ := hbound i k
      refine ⟨‖p.2.2.1‖ ^ j * C0, fun a b xt => ?_⟩
      rw [hL a b]
      split_ifs with hab
      · have ha : a = p.2.2.1 := congrArg Prod.fst hab
        rw [ha, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hC0b xt) (by positivity)
      · have : iteratedFDeriv ℝ k (0 : (Fin m → ℝ) × (Fin n → ℝ) → ℂ) xt = 0 := by
          rw [show (0 : (Fin m → ℝ) × (Fin n → ℝ) → ℂ) = fun _ => 0 from rfl,
            iteratedFDeriv_fun_zero]
          rfl
        rw [this, norm_zero, mul_zero]
        positivity


/-- The coordinatewise inverse on the `S`-adeles. -/
noncomputable def coordInv (x : SAdeleRing F Sf) : SAdeleRing F Sf :=
  ((show InfiniteAdeleRing F from fun w => (x.1 w)⁻¹), fun v => (x.2 v)⁻¹)

/-- The `S`-adeles all of whose coordinates are non-zero. -/
def unitReg : Set (SAdeleRing F Sf) := {x | (∀ w : InfinitePlace F, x.1 w ≠ 0) ∧ ∀ v : Sf, x.2 v ≠ 0}

theorem mul_coordInv (x : SAdeleRing F Sf) (hx : x ∈ unitReg Sf) : x * coordInv Sf x = 1 := by
  refine Prod.ext ?_ ?_
  · funext w
    show x.1 w * (x.1 w)⁻¹ = 1
    exact mul_inv_cancel₀ (hx.1 w)
  · funext v
    show x.2 v * (x.2 v)⁻¹ = 1
    exact mul_inv_cancel₀ (hx.2 v)

theorem mem_unitReg_of_unit (u : SIdeleGroup F Sf) : (u : SAdeleRing F Sf) ∈ unitReg Sf := by
  have h := u.mul_inv
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · have h1 := congrArg (fun y : SAdeleRing F Sf => y.1 w) h
    change (u : SAdeleRing F Sf).1 w * ((u⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w = 1 at h1
    rw [hw, zero_mul] at h1
    exact zero_ne_one h1
  · have h1 := congrArg (fun y : SAdeleRing F Sf => y.2 v) h
    change (u : SAdeleRing F Sf).2 v * ((u⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v = 1 at h1
    rw [hv, zero_mul] at h1
    exact zero_ne_one h1

theorem isOpen_unitReg : IsOpen (unitReg Sf) := by
  have : unitReg Sf = (⋂ w : InfinitePlace F, {x : SAdeleRing F Sf | x.1 w ≠ 0}) ∩
      ⋂ v : Sf, {x : SAdeleRing F Sf | x.2 v ≠ 0} := by
    ext x; simp [unitReg]
  rw [this]
  refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_iInter_of_finite fun v => ?_)
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const
  · exact isOpen_ne_fun ((continuous_apply v).comp continuous_snd) continuous_const

theorem isEmbedding_units_val :
    IsEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) := by
  refine Units.isEmbedding_val_mk' (f := coordInv Sf) ?_ ?_
  · intro x hx
    have hr : x ∈ unitReg Sf := by
      obtain ⟨u, rfl⟩ := hx
      exact mem_unitReg_of_unit Sf u
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.prodMk ?_ ?_
    · show ContinuousAt (fun x : SAdeleRing F Sf =>
        (fun w => (x.1 w)⁻¹ : (w : InfinitePlace F) → w.Completion)) x
      refine continuousAt_pi.2 fun w => ?_
      exact (continuousAt_inv₀ (hr.1 w)).comp
        ((continuous_apply w).comp continuous_fst).continuousAt
    · refine continuousAt_pi.2 fun v => ?_
      exact (continuousAt_inv₀ (hr.2 v)).comp
        ((continuous_apply v).comp continuous_snd).continuousAt
  · intro u
    have h := mul_coordInv Sf (u : SAdeleRing F Sf) (mem_unitReg_of_unit Sf u)
    calc coordInv Sf (u : SAdeleRing F Sf)
        = ((u⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf) *
            ((u : SAdeleRing F Sf) * coordInv Sf (u : SAdeleRing F Sf)) :=
          (Units.inv_mul_cancel_left u _).symm
      _ = ((u⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf) := by rw [h, mul_one]

theorem mem_range_units_val (x : SAdeleRing F Sf) (hx : x ∈ unitReg Sf) :
    x ∈ Set.range (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) :=
  ⟨⟨x, coordInv Sf x, mul_coordInv Sf x hx, by rw [mul_comm]; exact mul_coordInv Sf x hx⟩, rfl⟩

/-- A test function supported (on the ideles) in a compact set, with non-zero zeta integral. -/
theorem exists_compact_ne_zero (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c) :
    ∃ f : SAdelicSchwartz F Sf, ∃ K : Set (SIdeleGroup F Sf), IsCompact K ∧
      (∀ g : SIdeleGroup F Sf, g ∉ K → f.eval (g : SAdeleRing F Sf) = 0) ∧
      (Continuous fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf)) ∧
      sZetaIntegral f c ≠ 0 := by
  classical
  obtain ⟨hcont, hmul, hne⟩ := hc
  have hc1 : c 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h2 : c 1 * c 1 = c 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ (hne 1) h2
  -- the units of the `S`-adeles near `1` on which `Re c > 0`
  have hemb := isEmbedding_units_val Sf
  have hWc : IsOpen {g : SIdeleGroup F Sf | 0 < (c g).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
  obtain ⟨O, hOopen, hOpre⟩ := hemb.isInducing.isOpen_iff.mp hWc
  have h1O : (1 : SAdeleRing F Sf) ∈ O := by
    have : (1 : SIdeleGroup F Sf) ∈ {g : SIdeleGroup F Sf | 0 < (c g).re} := by
      simp [hc1]
    rw [← hOpre] at this
    exact this
  have h1R : (1 : SAdeleRing F Sf) ∈ unitReg Sf := mem_unitReg_of_unit Sf 1
  obtain ⟨KA, hKAn, hKAsub, hKAc⟩ :=
    local_compact_nhds ((hOopen.inter (isOpen_unitReg Sf)).mem_nhds ⟨h1O, h1R⟩)
  -- the group `G = 𝔸_{F,S}` written multiplicatively
  let e : Multiplicative (SAdeleRing F Sf) := Multiplicative.ofAdd 1
  let KG : Set (Multiplicative (SAdeleRing F Sf)) := {x | Multiplicative.toAdd x ∈ KA}
  have hKGn : KG ∈ 𝓝 e := hKAn
  have hmulT : Filter.Tendsto (fun q : Multiplicative (SAdeleRing F Sf) ×
      Multiplicative (SAdeleRing F Sf) => q.1 * q.2) (𝓝 (e, 1)) (𝓝 e) := by
    have := (continuous_mul (M := Multiplicative (SAdeleRing F Sf))).tendsto (e, 1)
    simpa using this
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hmulT hKGn)
  let Γ := gammaSub Sf
  have heΓ : e ∈ Γ := fun w => by
    show (1 : (w : HeightOneSpectrum (𝓞 F)).adicCompletion F) ∈ _
    exact one_mem _
  have hU0 : v ∩ (Γ : Set _) ∈ 𝓝 (1 : Multiplicative (SAdeleRing F Sf)) :=
    Filter.inter_mem hv ((isOpen_gammaSub Sf).mem_nhds (one_mem _))
  obtain ⟨kseq, -, hsmall, hgood, hpres⟩ :=
    exists_small_good_subgroups (Multiplicative (SAdeleRing F Sf))
  obtain ⟨N, hN⟩ := hsmall _ hU0
  let k := kseq N
  have hkΓ : k ≤ Γ := fun x hx => (hN hx).2
  obtain ⟨m, n, r, s, d, π, hπ⟩ :=
    hpres N Γ (isOpen_gammaSub Sf) (isCompactlyGenerated_gammaSub Sf) hkΓ
  have hstruct : IsStructuralPair Γ k :=
    ⟨isOpen_gammaSub Sf, isCompactlyGenerated_gammaSub Sf, hgood N, hkΓ⟩
  -- the bump function on `Γ / k`
  let W1 := interior u
  let S1 : Set Γ := {y | (y : Multiplicative (SAdeleRing F Sf)) ∈ W1}
  have hS1 : IsOpen S1 := isOpen_interior.preimage continuous_subtype_val
  let Ω : Set (ElemGroup m n r s d) := {z | Multiplicative.ofAdd z ∈ π '' S1}
  have hΩ : IsOpen Ω := (hπ.2.2.1 S1 hS1).preimage continuous_ofAdd
  let p : ElemGroup m n r s d := Multiplicative.toAdd (π ⟨e, heΓ⟩)
  have hpΩ : p ∈ Ω := ⟨⟨e, heΓ⟩, mem_interior_iff_mem_nhds.mpr hu, rfl⟩
  obtain ⟨Gb, hGcont, hGnn, hGpos, hGsupp, hGrap⟩ := exists_bump p Ω (hΩ.mem_nhds hpΩ)
  let gE : ElemSchwartz m n r s d := ⟨fun z => (Gb z : ℂ), Submodule.subset_span hGrap⟩
  let f : SAdelicSchwartz F Sf := SchwartzBruhat.ofElem Γ k π hstruct hπ gE
  let FrG : Multiplicative (SAdeleRing F Sf) → ℝ := fun y =>
    if h : y ∈ Γ then Gb (Multiplicative.toAdd (π ⟨y, h⟩)) else 0
  have hfeval : ∀ x, f.eval x = (FrG (Multiplicative.ofAdd x) : ℂ) := by
    intro x
    by_cases h : Multiplicative.ofAdd x ∈ Γ
    · simp [f, FrG, SAdelicSchwartz.eval, SchwartzBruhat.ofElem, SchwartzBruhat.toFun,
        extendPullback, h, gE, ElemSchwartz.toFun]
    · simp [f, FrG, SAdelicSchwartz.eval, SchwartzBruhat.ofElem, SchwartzBruhat.toFun,
        extendPullback, h]
  -- properties of `FrG`
  have hFrnn : ∀ y, 0 ≤ FrG y := by
    intro y
    by_cases h : y ∈ Γ
    · simp only [FrG, h, dif_pos]; exact hGnn _
    · simp only [FrG, h, dif_neg, not_false_eq_true, le_refl]
  have hΓclosed : IsClosed (Γ : Set (Multiplicative (SAdeleRing F Sf))) :=
    Subgroup.isClosed_of_isOpen _ (isOpen_gammaSub Sf)
  have hFrc : Continuous FrG := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases h : y ∈ Γ
    · have hoe := (isOpen_gammaSub Sf).isOpenEmbedding_subtypeVal
      have : ContinuousAt (FrG ∘ (Subtype.val : Γ → Multiplicative (SAdeleRing F Sf))) ⟨y, h⟩ := by
        have heq : FrG ∘ (Subtype.val : Γ → Multiplicative (SAdeleRing F Sf)) =
            fun y' : Γ => Gb (Multiplicative.toAdd (π y')) := by
          funext y'
          simp only [Function.comp, FrG, y'.2, dif_pos]
        rw [heq]
        exact (hGcont.comp (continuous_toAdd.comp hπ.2.1)).continuousAt
      exact (hoe.continuousAt_iff).mp this
    · have hev : FrG =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hΓclosed.isOpen_compl.mem_nhds h] with y' hy'
        exact dif_neg (show y' ∉ Γ from hy')
      exact continuousAt_const.congr hev.symm
  have hFrsupp : ∀ y, FrG y ≠ 0 → Multiplicative.toAdd y ∈ KA := by
    intro y hy
    by_cases h : y ∈ Γ
    · have hG0 : Gb (Multiplicative.toAdd (π ⟨y, h⟩)) ≠ 0 := by
        simpa only [FrG, dif_pos h] using hy
      obtain ⟨y', hy'W, hy'π⟩ := hGsupp _ hG0
      have hker : π (y'⁻¹ * ⟨y, h⟩) = 1 := by
        rw [map_mul, map_inv, hy'π]
        exact inv_mul_cancel _
      have hk : ((y'⁻¹ * ⟨y, h⟩ : Γ) : Multiplicative (SAdeleRing F Sf)) ∈ k :=
        (hπ.2.2.2.2 _).mp hker
      have hmemv := (hN hk).1
      have hprod' : ((y' : Multiplicative (SAdeleRing F Sf)),
          ((y'⁻¹ * ⟨y, h⟩ : Γ) : Multiplicative (SAdeleRing F Sf))) ∈ u ×ˢ v :=
        ⟨interior_subset (show (y' : Multiplicative (SAdeleRing F Sf)) ∈ interior u from hy'W),
          hmemv⟩
      have hprod := huv hprod'
      have hy_eq : (y' : Multiplicative (SAdeleRing F Sf)) *
          ((y'⁻¹ * ⟨y, h⟩ : Γ) : Multiplicative (SAdeleRing F Sf)) = y := by
        simp
      have : y ∈ KG := by
        rw [← hy_eq]
        exact hprod
      exact this
    · exact absurd (by simp only [FrG, dif_neg h]) hy
  -- the integrand
  have hHaar := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  let I : SIdeleGroup F Sf → ℂ := fun g => f.eval (g : SAdeleRing F Sf) * c g
  have hIeq : ∀ g, I g = (FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) : ℂ) * c g := by
    intro g; simp only [I, hfeval]
  have hFrGc : Continuous fun g : SIdeleGroup F Sf => FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) :=
    hFrc.comp (continuous_ofAdd.comp Units.continuous_val)
  have hIc : Continuous I := by
    have : I = fun g : SIdeleGroup F Sf =>
        (FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) : ℂ) * c g := funext hIeq
    rw [this]
    exact (Complex.continuous_ofReal.comp hFrGc).mul hcont
  have hKc : IsCompact ((Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) ⁻¹' KA) :=
    hemb.isInducing.isCompact_preimage' hKAc
      (fun x hx => mem_range_units_val Sf x (hKAsub hx).2)
  have hzero : ∀ g : SIdeleGroup F Sf, g ∉ (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) ⁻¹' KA →
      FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) = 0 := by
    intro g hg
    by_contra h
    exact hg (hFrsupp _ h)
  have hIsupp : HasCompactSupport I := by
    refine HasCompactSupport.intro hKc fun g hg => ?_
    rw [hIeq, hzero g hg]; simp
  have hIint : Integrable I (sMultiplicativeTamagawa F Sf) :=
    hIc.integrable_of_hasCompactSupport hIsupp
  let J : SIdeleGroup F Sf → ℝ := fun g => (I g).re
  have hJeq : ∀ g, J g = FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) * (c g).re := by
    intro g; simp only [J, hIeq, Complex.re_ofReal_mul]
  have hJc : Continuous J := Complex.continuous_re.comp hIc
  have hJsupp : HasCompactSupport J := by
    refine HasCompactSupport.intro hKc fun g hg => ?_
    rw [hJeq, hzero g hg, zero_mul]
  have hJnn : 0 ≤ J := by
    intro g
    rw [Pi.zero_apply, hJeq]
    by_cases h : FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) = 0
    · rw [h, zero_mul]
    · have hK := hFrsupp _ h
      have hO : (g : SAdeleRing F Sf) ∈ O := (hKAsub hK).1
      have hg : g ∈ {g : SIdeleGroup F Sf | 0 < (c g).re} := by
        rw [← hOpre]; exact hO
      exact mul_nonneg (hFrnn _) hg.le
  have hJ1 : J 1 ≠ 0 := by
    rw [hJeq, hc1, Complex.one_re, mul_one]
    have : FrG (Multiplicative.ofAdd ((1 : SIdeleGroup F Sf) : SAdeleRing F Sf)) = Gb p := by
      show FrG e = Gb p
      simp only [FrG, dif_pos heΓ, p]
    rw [this]
    exact hGpos.ne'
  have hpos : 0 < ∫ g, J g ∂(sMultiplicativeTamagawa F Sf) :=
    hJc.integral_pos_of_hasCompactSupport_nonneg_nonzero hJsupp hJnn hJ1
  have hre : ∫ g, J g ∂(sMultiplicativeTamagawa F Sf) =
      (∫ g, I g ∂(sMultiplicativeTamagawa F Sf)).re := by
    have := integral_re hIint
    simpa using this
  refine ⟨f, (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) ⁻¹' KA, hKc, fun g hg => ?_, ?_,
    fun hz => ?_⟩
  · rw [hfeval, hzero g hg, Complex.ofReal_zero]
  · have : (fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf)) =
        fun g : SIdeleGroup F Sf => ((FrG (Multiplicative.ofAdd (g : SAdeleRing F Sf)) : ℝ) : ℂ) :=
      funext fun g => hfeval _
    rw [this]
    exact Complex.continuous_ofReal.comp hFrGc
  · have hz' : (∫ g, I g ∂(sMultiplicativeTamagawa F Sf)) = 0 := hz
    rw [hre, hz', Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

end Sol_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio

namespace Sol_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio

open Filter

variable {F : Type*} [Field F] [NumberField F] {Sf : Finset (HeightOneSpectrum (𝓞 F))}

theorem coord_inf_ne_zero (g : SIdeleGroup F Sf) (w : InfinitePlace F) :
    (g : SAdeleRing F Sf).1 w ≠ 0 := by
  have h := congrArg (fun x : SAdeleRing F Sf => x.1 w) g.mul_inv
  simp only [Prod.fst_mul, Prod.fst_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem coord_fin_ne_zero (g : SIdeleGroup F Sf) (v : Sf) :
    (g : SAdeleRing F Sf).2 v ≠ 0 := by
  have h := congrArg (fun x : SAdeleRing F Sf => x.2 v) g.mul_inv
  simp only [Prod.snd_mul, Prod.snd_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem sIdeleNorm_pos' (g : SIdeleGroup F Sf) : 0 < sIdeleNorm Sf g := by
  unfold sIdeleNorm
  exact mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (coord_inf_ne_zero g w)) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (coord_fin_ne_zero g v))

theorem sIdeleNorm_mul' (g h : SIdeleGroup F Sf) :
    sIdeleNorm Sf (g * h) = sIdeleNorm Sf g * sIdeleNorm Sf h := by
  have h1 : ∀ w : InfinitePlace F, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w =
      (g : SAdeleRing F Sf).1 w * (h : SAdeleRing F Sf).1 w := fun w => rfl
  have h2 : ∀ v : Sf, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v =
      (g : SAdeleRing F Sf).2 v * (h : SAdeleRing F Sf).2 v := fun v => rfl
  unfold sIdeleNorm
  simp only [h1, h2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_sIdeleNorm' : Continuous (sIdeleNorm (F := F) Sf) := by
  have h1 : Continuous fun g : SIdeleGroup F Sf => (g : SAdeleRing F Sf) := Units.continuous_val
  show Continuous fun g : SIdeleGroup F Sf =>
    (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) * ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_)
    (continuous_finsetProd _ fun v _ => ?_)
  · exact ((continuous_apply w).comp (continuous_fst.comp h1)).norm.pow _
  · exact ((continuous_apply v).comp (continuous_snd.comp h1)).norm

theorem twist_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) (s : ℂ) :
    IsSIdeleQuasiCharacter Sf (sQuasiTwist Sf c s) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · unfold sQuasiTwist
    exact hcont.mul ((Complex.continuous_ofReal.comp continuous_sIdeleNorm').cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.mpr (sIdeleNorm_pos' g))
  · intro g h
    unfold sQuasiTwist
    rw [hmul, sIdeleNorm_mul', Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (sIdeleNorm_pos' g).le (sIdeleNorm_pos' h).le]
    ring
  · intro g
    unfold sQuasiTwist
    refine mul_ne_zero (hne g) ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos' g).ne') h.1

theorem twist_norm {c : SIdeleGroup F Sf → ℂ} {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (s : ℂ) (g : SIdeleGroup F Sf) :
    ‖sQuasiTwist Sf c s g‖ = sIdeleNorm Sf g ^ (σ + s.re) := by
  unfold sQuasiTwist
  rw [norm_mul, hσ, Complex.norm_cpow_eq_rpow_re_of_pos (sIdeleNorm_pos' g),
    Real.rpow_add (sIdeleNorm_pos' g)]

theorem dual_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) :
    IsSIdeleQuasiCharacter Sf (sQuasiDual Sf c) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · unfold sQuasiDual
    exact (Complex.continuous_ofReal.comp continuous_sIdeleNorm').mul (hcont.inv₀ hne)
  · intro g h
    unfold sQuasiDual
    rw [hmul, sIdeleNorm_mul', Complex.ofReal_mul, mul_inv]
    ring
  · intro g
    unfold sQuasiDual
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos' g).ne') (inv_ne_zero (hne g))

theorem dual_norm {c : SIdeleGroup F Sf → ℂ} {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (g : SIdeleGroup F Sf) :
    ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) := by
  unfold sQuasiDual
  rw [norm_mul, norm_inv, hσ, Complex.norm_of_nonneg (sIdeleNorm_pos' g).le,
    Real.rpow_sub (sIdeleNorm_pos' g), Real.rpow_one, div_eq_mul_inv]

theorem dual_twist (c : SIdeleGroup F Sf → ℂ) (s : ℂ) :
    sQuasiDual Sf (sQuasiTwist Sf c s) = sQuasiTwist Sf (sQuasiDual Sf c) (-s) := by
  funext g
  unfold sQuasiDual sQuasiTwist
  rw [mul_inv, Complex.cpow_neg]
  ring

/-- The `S`-idelic norm is bounded above and below by positive constants on a compact set. -/
theorem norm_bounds_of_isCompact {K : Set (SIdeleGroup F Sf)} (hK : IsCompact K) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g ∈ K, a ≤ sIdeleNorm Sf g ∧ sIdeleNorm Sf g ≤ b := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, 0, one_pos, fun g hg => by simp [h] at hg⟩
  · obtain ⟨x, -, hxmin⟩ := hK.exists_isMinOn h continuous_sIdeleNorm'.continuousOn
    obtain ⟨y, -, hymax⟩ := hK.exists_isMaxOn h continuous_sIdeleNorm'.continuousOn
    exact ⟨sIdeleNorm Sf x, sIdeleNorm Sf y, sIdeleNorm_pos' x,
      fun g hg => ⟨isMinOn_iff.mp hxmin g hg, isMaxOn_iff.mp hymax g hg⟩⟩

/-- `r ^ x |log r| ≤ exp((|x₀| + 1) L) L` for `a ≤ r ≤ b`, `|x - x₀| < 1`, `L = |log a| + |log b|`. -/
theorem rpow_mul_abs_log_le {a b r x0 x : ℝ} (ha : 0 < a) (hr1 : a ≤ r) (hr2 : r ≤ b)
    (hx : |x - x0| < 1) :
    r ^ x * |Real.log r| ≤
      Real.exp ((|x0| + 1) * (|Real.log a| + |Real.log b|)) * (|Real.log a| + |Real.log b|) := by
  have hr : 0 < r := ha.trans_le hr1
  have hL0 : 0 ≤ |Real.log a| + |Real.log b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hlog : |Real.log r| ≤ |Real.log a| + |Real.log b| := by
    rw [abs_le]
    have h1 := Real.log_le_log ha hr1
    have h2 := Real.log_le_log hr hr2
    constructor
    · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  have hxabs : |x| ≤ |x0| + 1 := by
    have := abs_sub_abs_le_abs_sub x x0
    linarith
  have hpow : r ^ x ≤ Real.exp ((|x0| + 1) * (|Real.log a| + |Real.log b|)) := by
    rw [Real.rpow_def_of_pos hr]
    apply Real.exp_le_exp.mpr
    calc Real.log r * x ≤ |Real.log r * x| := le_abs_self _
      _ = |Real.log r| * |x| := abs_mul _ _
      _ ≤ (|Real.log a| + |Real.log b|) * (|x0| + 1) :=
          mul_le_mul hlog hxabs (abs_nonneg _) hL0
      _ = (|x0| + 1) * (|Real.log a| + |Real.log b|) := mul_comm _ _
  exact mul_le_mul hpow hlog (abs_nonneg _) (Real.exp_pos _).le

/-- For a test function vanishing on the ideles outside a compact set, `s ↦ Z_S(f, c_s)` is
entire (differentiation under the integral sign). -/
theorem differentiable_sZetaIntegral_of_isCompact (f : SAdelicSchwartz F Sf)
    {K : Set (SIdeleGroup F Sf)} (hK : IsCompact K)
    (hfK : ∀ g : SIdeleGroup F Sf, g ∉ K → f.eval (g : SAdeleRing F Sf) = 0)
    (hfc : Continuous fun g : SIdeleGroup F Sf => f.eval (g : SAdeleRing F Sf))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) :
    Differentiable ℂ (fun s : ℂ => sZetaIntegral f (sQuasiTwist Sf c s)) := by
  have hHaar := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  obtain ⟨a, b, ha, hab⟩ := norm_bounds_of_isCompact hK
  have hr : ∀ g : SIdeleGroup F Sf, 0 < sIdeleNorm Sf g := sIdeleNorm_pos'
  have hcont_r : Continuous fun g : SIdeleGroup F Sf => ((sIdeleNorm Sf g : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_sIdeleNorm'
  let W : ℂ → SIdeleGroup F Sf → ℂ :=
    fun z g => f.eval (g : SAdeleRing F Sf) * sQuasiTwist Sf c z g
  let D : ℂ → SIdeleGroup F Sf → ℂ :=
    fun z g => W z g * Complex.log ((sIdeleNorm Sf g : ℝ) : ℂ)
  have hnormW : ∀ (z : ℂ) (g : SIdeleGroup F Sf),
      ‖W z g‖ = ‖f.eval (g : SAdeleRing F Sf)‖ * sIdeleNorm Sf g ^ (σ + z.re) := by
    intro z g
    simp only [W]
    rw [norm_mul, twist_norm hσ]
  have hcontW : ∀ z, Continuous (W z) := fun z => hfc.mul (twist_isQC hc z).1
  have hsuppW : ∀ z, HasCompactSupport (W z) := by
    intro z
    refine HasCompactSupport.intro hK fun g hg => ?_
    simp only [W, hfK g hg, zero_mul]
  have hint : ∀ z, Integrable (W z) (sMultiplicativeTamagawa F Sf) :=
    fun z => (hcontW z).integrable_of_hasCompactSupport (hsuppW z)
  intro s0
  let V : Set ℂ := Metric.ball s0 1
  have hV : V ∈ 𝓝 s0 := Metric.ball_mem_nhds s0 one_pos
  have hmeas : ∀ᶠ z in 𝓝 s0, AEStronglyMeasurable (W z) (sMultiplicativeTamagawa F Sf) :=
    Filter.Eventually.of_forall fun z => (hcontW z).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D s0) (sMultiplicativeTamagawa F Sf) :=
    (hcontW s0).aestronglyMeasurable.mul
      (Complex.measurable_log.comp hcont_r.measurable).aestronglyMeasurable
  let M : ℝ := Real.exp ((|σ + s0.re| + 1) * (|Real.log a| + |Real.log b|)) *
    (|Real.log a| + |Real.log b|)
  let bound : SIdeleGroup F Sf → ℝ := fun g => M * ‖f.eval (g : SAdeleRing F Sf)‖
  have hbound : Integrable bound (sMultiplicativeTamagawa F Sf) := by
    have h1 : Integrable (fun g : SIdeleGroup F Sf => ‖f.eval (g : SAdeleRing F Sf)‖)
        (sMultiplicativeTamagawa F Sf) := by
      refine hfc.norm.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro hK fun g hg => ?_
      simp only [hfK g hg, norm_zero]
    exact h1.const_mul M
  have hDbound : ∀ᵐ g ∂(sMultiplicativeTamagawa F Sf), ∀ z ∈ V, ‖D z g‖ ≤ bound g := by
    refine Filter.Eventually.of_forall fun g z hz => ?_
    have hlog : Complex.log ((sIdeleNorm Sf g : ℝ) : ℂ) =
        ((Real.log (sIdeleNorm Sf g) : ℝ) : ℂ) :=
      (Complex.ofReal_log (hr g).le).symm
    simp only [D, bound]
    rw [norm_mul, hnormW, hlog, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    by_cases hg : g ∈ K
    · have hz' : |(σ + z.re) - (σ + s0.re)| < 1 := by
        have h1 : |z.re - s0.re| ≤ ‖z - s0‖ := by
          rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
        have h2 : ‖z - s0‖ < 1 := by
          rw [← dist_eq_norm]; exact hz
        rw [show (σ + z.re) - (σ + s0.re) = z.re - s0.re by ring]
        linarith
      have h3 := rpow_mul_abs_log_le ha (hab g hg).1 (hab g hg).2 hz'
      calc ‖f.eval (g : SAdeleRing F Sf)‖ *
            (sIdeleNorm Sf g ^ (σ + z.re) * |Real.log (sIdeleNorm Sf g)|)
          ≤ ‖f.eval (g : SAdeleRing F Sf)‖ * M := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = M * ‖f.eval (g : SAdeleRing F Sf)‖ := mul_comm _ _
    · rw [hfK g hg, norm_zero, zero_mul, mul_zero]
  have hdiff : ∀ᵐ g ∂(sMultiplicativeTamagawa F Sf), ∀ z ∈ V,
      HasDerivAt (fun w => W w g) (D z g) z :=
    Filter.Eventually.of_forall fun g z _ => by
      have hg : ((sIdeleNorm Sf g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr g).ne'
      simp only [W, D, sQuasiTwist]
      simpa only [id_eq, mul_assoc, mul_one] using
        (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul (c g)).const_mul
          (f.eval (g : SAdeleRing F Sf))
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas (hint s0) hDmeas
    hDbound hbound hdiff).2
  exact key.differentiableAt

end Sol_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio

open MasulloGRH Sol_MasulloGRH_exists_meromorphic_sZetaIntegral_ratio Filter Topology in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) :
    ∃ ρ : ℂ → ℂ, MeromorphicOn ρ Set.univ ∧
      ∀ s : ℂ, 0 < σ + s.re → σ + s.re < 1 →
        ∃ f : SAdelicSchwartz F Sf,
          sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s)) ≠ 0 ∧
          sZetaIntegral f (sQuasiTwist Sf c s) =
            ρ s * sZetaIntegralFun Sf (sLocalFourier Sf f.eval)
              (sQuasiDual Sf (sQuasiTwist Sf c s)) := by
  classical
  -- the Fourier transform as an automorphism of the Schwartz–Bruhat space
  obtain ⟨-, T, hT, -⟩ := sLocalFourier_schwartzBruhat_equiv F Sf
  have hdc := dual_isQC hc
  have hdn : ∀ g : SIdeleGroup F Sf, ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) :=
    dual_norm hσ
  -- the two zeta integrals as functions of `s`
  let Zc : SAdelicSchwartz F Sf → ℂ → ℂ := fun f s => sZetaIntegral f (sQuasiTwist Sf c s)
  let Zd : SAdelicSchwartz F Sf → ℂ → ℂ := fun f s =>
    sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s))
  have hZd : ∀ (f : SAdelicSchwartz F Sf) (s : ℂ),
      Zd f s = sZetaIntegral (T f) (sQuasiTwist Sf (sQuasiDual Sf c) (-s)) := by
    intro f s
    show sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf (sQuasiTwist Sf c s)) = _
    rw [dual_twist, sZetaIntegral, hT f]
  have hU : IsOpen {s : ℂ | 0 < σ + s.re} :=
    isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)
  have hV : IsOpen {s : ℂ | σ + s.re < 1} :=
    isOpen_lt (continuous_const.add Complex.continuous_re) continuous_const
  have hVconv : Convex ℝ {s : ℂ | σ + s.re < 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
    have e : σ + (a * x.re + b * y.re) = a * (σ + x.re) + b * (σ + y.re) := by
      linear_combination (-σ) * hab
    rw [e]
    rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simp only [zero_mul, one_mul, zero_add]
      exact hy
    · have h1 := mul_lt_mul_of_pos_left hx ha0
      have h2 := mul_le_mul_of_nonneg_left hy.le hb
      linarith
  have hZcU : ∀ f : SAdelicSchwartz F Sf, DifferentiableOn ℂ (Zc f) {s : ℂ | 0 < σ + s.re} :=
    fun f => (sZetaIntegral_integrable_and_differentiableOn F Sf f c hc σ hσ).2
  have hZdV : ∀ f : SAdelicSchwartz F Sf, DifferentiableOn ℂ (Zd f) {s : ℂ | σ + s.re < 1} := by
    intro f
    have hd := (sZetaIntegral_integrable_and_differentiableOn F Sf (T f) (sQuasiDual Sf c) hdc
      (1 - σ) hdn).2
    have heq : Zd f =
        (fun s => sZetaIntegral (T f) (sQuasiTwist Sf (sQuasiDual Sf c) s)) ∘ (fun s : ℂ => -s) := by
      funext s
      exact hZd f s
    rw [heq]
    refine hd.comp differentiable_neg.differentiableOn ?_
    intro s hs
    simp only [Set.mem_ofPred_eq, Complex.neg_re] at hs ⊢
    linarith
  -- Tate's symmetry lemma on the strip
  have hsym : ∀ (f h : SAdelicSchwartz F Sf) (s : ℂ), 0 < σ + s.re → σ + s.re < 1 →
      Zc f s * Zd h s = Zc h s * Zd f s := fun f h s h0 h1 =>
    sZetaIntegral_mul_fourier_symm F Sf (sQuasiTwist Sf c s) (twist_isQC hc s) (σ + s.re)
      (twist_norm hσ s) h0 h1 f h
  -- a base point in the strip
  let s0 : ℂ := ((1 / 2 - σ : ℝ) : ℂ)
  have hs0 : σ + s0.re = 1 / 2 := by simp only [s0, Complex.ofReal_re]; ring
  -- two test functions with compact support on the ideles
  obtain ⟨h, Kh, hKh, hhK, hhc, hh0⟩ :=
    exists_compact_ne_zero Sf (sQuasiTwist Sf c s0) (twist_isQC hc s0)
  obtain ⟨k, Kk, hKk, hkK, hkc, hk0⟩ :=
    exists_compact_ne_zero Sf (sQuasiDual Sf (sQuasiTwist Sf c s0)) (dual_isQC (twist_isQC hc s0))
  let f2 : SAdelicSchwartz F Sf := T.symm k
  have hTf2 : T f2 = k := T.apply_symm_apply k
  -- `A = Z(h, c_s)` is entire, `B = Z(\hat h, \hat{c_s})` holomorphic on `σ + Re s < 1`,
  -- `C = Z(f₂, c_s)` holomorphic on `σ + Re s > 0`, `D = Z(k, \hat{c_s})` entire
  have hA : Differentiable ℂ (Zc h) :=
    differentiable_sZetaIntegral_of_isCompact h hKh hhK hhc c hc σ hσ
  have hD : Differentiable ℂ (Zd f2) := by
    have h1 := differentiable_sZetaIntegral_of_isCompact k hKk hkK hkc (sQuasiDual Sf c) hdc
      (1 - σ) hdn
    have heq : Zd f2 =
        (fun s => sZetaIntegral k (sQuasiTwist Sf (sQuasiDual Sf c) s)) ∘ (fun s : ℂ => -s) := by
      funext s
      rw [hZd f2 s, hTf2]
      rfl
    rw [heq]
    exact h1.comp differentiable_neg
  have hA0 : Zc h s0 ≠ 0 := hh0
  have hD0 : Zd f2 s0 ≠ 0 := by
    show sZetaIntegralFun Sf (sLocalFourier Sf f2.eval) (sQuasiDual Sf (sQuasiTwist Sf c s0)) ≠ 0
    rw [← hT f2, hTf2]
    exact hk0
  have hB0 : Zd h s0 ≠ 0 := by
    intro hz
    have := hsym h f2 s0 (by rw [hs0]; norm_num) (by rw [hs0]; norm_num)
    rw [hz, mul_zero] at this
    exact mul_ne_zero hA0 hD0 this
  -- the zeros of `B` and `D` are isolated
  have hDev : ∀ x : ℂ, ∀ᶠ z in 𝓝[≠] x, Zd f2 z ≠ 0 := by
    intro x
    rcases (hD.analyticAt x).eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · exfalso
      have han : AnalyticOnNhd ℂ (Zd f2) Set.univ := hD.differentiableOn.analyticOnNhd isOpen_univ
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ x) hz (Set.mem_univ s0)
      exact hD0 this
    · exact hz
  have hBev : ∀ x : ℂ, σ + x.re < 1 → ∀ᶠ z in 𝓝[≠] x, Zd h z ≠ 0 := by
    intro x hx
    rcases ((hZdV h).analyticAt (hV.mem_nhds hx)).eventually_eq_zero_or_eventually_ne_zero
      with hz | hz
    · exfalso
      have han : AnalyticOnNhd ℂ (Zd h) {s : ℂ | σ + s.re < 1} := (hZdV h).analyticOnNhd hV
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hVconv.isPreconnected
        hx hz (show σ + s0.re < 1 by rw [hs0]; norm_num)
      exact hB0 this
    · exact hz
  -- the glued function
  let ρ0 : ℂ → ℂ := fun s =>
    if 0 < σ + s.re then Zc f2 s / Zd f2 s else Zc h s / Zd h s
  have hρ0m : MeromorphicOn ρ0 Set.univ := by
    intro x _
    by_cases hx : 0 < σ + x.re
    · have hev : (fun z => Zc f2 z / Zd f2 z) =ᶠ[𝓝 x] ρ0 :=
        Filter.eventually_of_mem (hU.mem_nhds hx) fun z hz => (if_pos hz).symm
      have hm : MeromorphicAt (fun z => Zc f2 z / Zd f2 z) x :=
        ((hZcU f2).analyticAt (hU.mem_nhds hx)).meromorphicAt.div (hD.analyticAt x).meromorphicAt
      exact hm.congr (hev.filter_mono nhdsWithin_le_nhds)
    · have hx1 : σ + x.re < 1 := by linarith [not_lt.mp hx]
      have hm : MeromorphicAt (fun z => Zc h z / Zd h z) x :=
        (hA.analyticAt x).meromorphicAt.div ((hZdV h).analyticAt (hV.mem_nhds hx1)).meromorphicAt
      refine hm.congr ?_
      have hVev : ∀ᶠ z in 𝓝[≠] x, σ + z.re < 1 :=
        eventually_nhdsWithin_of_eventually_nhds (hV.mem_nhds hx1)
      filter_upwards [hBev x hx1, hDev x, hVev] with z hzB hzD hzV
      show Zc h z / Zd h z = if 0 < σ + z.re then Zc f2 z / Zd f2 z else Zc h z / Zd h z
      split_ifs with hz
      · rw [div_eq_div_iff hzB hzD]
        exact hsym h f2 z hz hzV
      · rfl
  -- at the (isolated) zeros of `D` in the strip, use another test function
  have hq : ∀ s : ℂ, IsSIdeleQuasiCharacter Sf (sQuasiDual Sf (sQuasiTwist Sf c s)) :=
    fun s => dual_isQC (twist_isQC hc s)
  let φ : ℂ → SAdelicSchwartz F Sf := fun s => (exists_compact_ne_zero Sf _ (hq s)).choose
  have hφ : ∀ s : ℂ, sZetaIntegral (φ s) (sQuasiDual Sf (sQuasiTwist Sf c s)) ≠ 0 :=
    fun s => (exists_compact_ne_zero Sf _ (hq s)).choose_spec.choose_spec.2.2.2
  have hφT : ∀ s : ℂ, Zd (T.symm (φ s)) s ≠ 0 := by
    intro s
    show sZetaIntegralFun Sf (sLocalFourier Sf (T.symm (φ s)).eval)
      (sQuasiDual Sf (sQuasiTwist Sf c s)) ≠ 0
    rw [← hT, T.apply_symm_apply]
    exact hφ s
  let ρ : ℂ → ℂ := fun s =>
    if Zd f2 s = 0 then Zc (T.symm (φ s)) s / Zd (T.symm (φ s)) s else ρ0 s
  refine ⟨ρ, ?_, ?_⟩
  · intro x hx
    refine (hρ0m x hx).congr ?_
    filter_upwards [hDev x] with z hz
    show ρ0 z = if Zd f2 z = 0 then Zc (T.symm (φ z)) z / Zd (T.symm (φ z)) z else ρ0 z
    rw [if_neg hz]
  · intro s h0 h1
    by_cases hDs : Zd f2 s = 0
    · refine ⟨T.symm (φ s), hφT s, ?_⟩
      have hρs : ρ s = Zc (T.symm (φ s)) s / Zd (T.symm (φ s)) s := if_pos hDs
      rw [hρs]
      exact (div_mul_cancel₀ (Zc (T.symm (φ s)) s) (hφT s)).symm
    · refine ⟨f2, hDs, ?_⟩
      have hρs : ρ s = Zc f2 s / Zd f2 s := by
        show (if Zd f2 s = 0 then Zc (T.symm (φ s)) s / Zd (T.symm (φ s)) s else ρ0 s) = _
        rw [if_neg hDs]
        exact if_pos h0
      rw [hρs]
      exact (div_mul_cancel₀ (Zc f2 s) hDs).symm
