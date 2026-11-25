-- Prove2me | solution 1 for GlobalTheory.finiteDimensional_eigenspace_sum_sq_invariantFields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:42.29779+00:00
-- url     : https://prove2.me/submissions/f5d329cc-a1c4-44ed-8000-8e33903df6bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RightTranslationCurveSqLeAndIntegralDerivEqZeroAStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalEigenspaceSumSqInvariantFieldsA
import Theorems.Thm_GlobalTheory_T_finiteDimensional_of_uniformly_almost_invariant_alt
import Theorems.Thm_GlobalTheory_T_right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by
  intro K _ _ _ _ _ L _ _ _ S hS e he he0 hU d hadd hsmul hder ι _ X hX lam
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  set μ : Measure K := haarProb K with hμ
  have hc : ∀ f : S, Continuous f.1 := fun f => hS f.1 f.2
  have hint : ∀ {F : Type} [NormedAddCommGroup F] {g : K → F}, Continuous g → Integrable g μ :=
    fun hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : ∀ f g : S, Integrable (fun x => (starRingEnd ℂ) (f.1 x) * g.1 x) μ :=
    fun f g => hint ((Complex.continuous_conj.comp (hc f)).mul (hc g))

  have hskew : ∀ (Y : L) (f : S), ((∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ) +
      ∫ x, (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x ∂μ = 0 := by
    intro Y f
    have c1 : Continuous fun x => (starRingEnd ℂ) (f.1 x) :=
      Complex.continuous_conj.comp (hc f)
    have c2 : Continuous fun x => (starRingEnd ℂ) ((d Y f).1 x) :=
      Complex.continuous_conj.comp (hc _)
    have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
      (fun x => (starRingEnd ℂ) (f.1 x) * (d Y f).1 x)
      (fun x => (starRingEnd ℂ) ((d Y f).1 x) * (d Y f).1 x
        + (starRingEnd ℂ) (f.1 x) * (d Y (d Y f)).1 x)
      (c1.mul (hc _)) ((c2.mul (hc _)).add (c1.mul (hc _)))
      (fun x t => (hder Y f x t).star.mul (hder Y (d Y f) x t))).2
    rw [integral_add (hi2 _ _) (hi2 _ _)] at h
    rw [← h, ← integral_complex_ofReal]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  have hsum : ∀ f : S, f ∈ Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam →
      ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ ≤ ‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by
    intro f hf
    rw [Module.End.mem_eigenspace_iff] at hf
    have h1 : ∑ i, ∫ x, (starRingEnd ℂ) (f.1 x) * (d (X i) (d (X i) f)).1 x ∂μ
        = lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_finsetSum _ (fun i _ => hi2 _ _), ← integral_complex_ofReal,
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have h2 := congrArg (fun g : S => g.1 x) hf
      simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
      simp only
      rw [← Finset.mul_sum, h2, mul_left_comm, Complex.conj_mul']
      simp
    have h3 : ((∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ : ℝ) : ℂ)
        = - (lam * ((∫ x, ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ)) := by
      rw [← h1, Complex.ofReal_sum, eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => hskew _ _
    have h4 := congrArg norm h3
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (a := ∫ x, ‖f.1 x‖ ^ 2 ∂μ)
        (integral_nonneg fun x => by positivity)] at h4
    rw [← h4]
    exact le_abs_self _
  obtain ⟨a, ha⟩ := (Fintype.linearCombination ℝ X).exists_rightInverse_of_surjective
    (by rw [Fintype.range_linearCombination, hX])
  have hac : Continuous a := a.continuous_of_finiteDimensional
  have hd0 : d 0 = 0 := by
    have := hsmul 0 0
    simpa using this
  have hdY : ∀ Y, d Y = ∑ i, ((a Y i : ℝ) : ℂ) • d (X i) := by
    intro Y
    have h1 : Y = ∑ i, a Y i • X i := by
      have := LinearMap.congr_fun ha Y
      simpa [Fintype.linearCombination_apply] using this.symm
    let D : L →+ Module.End ℂ S := ⟨⟨d, hd0⟩, hadd⟩
    calc d Y = D (∑ i, a Y i • X i) := congrArg d h1
      _ = ∑ i, D (a Y i • X i) := map_sum D _ _
      _ = _ := Finset.sum_congr rfl fun i _ => hsmul _ _
  have hbound : ∀ (Y : L) (f : S), ∫ x, ‖(d Y f).1 x‖ ^ 2 ∂μ ≤
      (∑ i, (a Y i) ^ 2) * ∑ i, ∫ x, ‖(d (X i) f).1 x‖ ^ 2 ∂μ := by
    intro Y f
    have ci : ∀ g : S, Continuous fun x => ‖g.1 x‖ ^ 2 := fun g => (hc g).norm.pow 2
    rw [← integral_finsetSum _ (fun i _ => hint (ci _)), ← integral_const_mul]
    refine integral_mono (hint (ci _))
      (hint (continuous_const.mul (continuous_finset_sum _ fun i _ => ci _))) fun x => ?_
    have h1 : ‖(d Y f).1 x‖ ≤ ∑ i, |a Y i| * ‖(d (X i) f).1 x‖ := by
      rw [hdY Y]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |a Y i|)
      (fun i => ‖(d (X i) f).1 x‖)
    simp only [sq_abs] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcont : Continuous fun Y : L => (∑ i, (a Y i) ^ 2) * ‖lam‖ := by fun_prop
  have hev : ∀ᶠ Y in 𝓝 (0 : L), (∑ i, (a Y i) ^ 2) * ‖lam‖ < 1 / 4 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hfin := GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt K μ
    ((Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam).map S.subtype)
    (by rintro _ ⟨f, -, rfl⟩; exact hc f) _ (hU r hr) (by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨Y, hY, rfl⟩
      have h := (GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt K μ (fun t => e (t • Y)) (he Y) (by simp [he0])
        f.1 (d Y f).1 (hc _) (hc _) (hder Y f)).1
      simp only [one_smul] at h
      have hn : 0 ≤ ∫ x, ‖f.1 x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
      have hs : 0 ≤ ∑ i, (a Y i) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
      calc _ ≤ _ := h
        _ ≤ _ := hbound Y f
        _ ≤ (∑ i, (a Y i) ^ 2) * (‖lam‖ * ∫ x, ‖f.1 x‖ ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left (hsum f hf) hs
        _ = ((∑ i, (a Y i) ^ 2) * ‖lam‖) * ∫ x, ‖f.1 x‖ ^ 2 ∂μ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hball Y hY).le hn)
  exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective _).symm.finiteDimensional
end GlobalTheory
