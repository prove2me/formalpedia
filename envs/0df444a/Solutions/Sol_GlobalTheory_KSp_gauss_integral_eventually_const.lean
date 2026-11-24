-- Prove2me | solution 1 for GlobalTheory.KSp.gauss_integral_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:17.794428+00:00
-- url     : https://prove2.me/submissions/ea6d5aca-b9f0-4c58-874e-ae2c804aaf28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussIntegralQuadraticCharEventuallyConst
import Theorems.Thm_GlobalTheory_KSp_setIntegral_addSubgroup_add
import Theorems.Thm_GlobalTheory_KSp_setIntegral_pair_char
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology Classical
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ f : X → ℂ, IsLocallyConstant f → f 0 = 1 → (∀ x y, f (x + y) = f x * f y * e x y) →
    ∃ (γ : ℂ) (K : Set X), IsCompact K ∧ ∀ L : AddSubgroup X, IsCompact (L : Set X) → IsOpen (L : Set X) →
      K ⊆ L → ∫ x in (L : Set X), f x ∂μ = γ := by
  intro X _ _ _ _ hG μ _ e he f hf hf0 hfe
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  obtain ⟨M, hMc, hMo, hMf⟩ := hG.small {x | f x = 1} ((hf.isOpen_fiber 1).mem_nhds hf0)
  have hMn : (M : Set X) ∈ 𝓝 (0 : X) := hMo.mem_nhds M.zero_mem
  obtain ⟨K₀, hK₀c, hK₀⟩ := he.big _ hMn
  have hecont : ∀ m, Continuous (fun y => e m y) := fun m =>
    (he.lc.comp_continuous (continuous_const.prodMk continuous_id)).continuous
  set M' : Set X := {y | ∀ m ∈ (M : Set X), e m y = 1} with hM'
  have hM'cl : IsClosed M' := by
    have : M' = ⋂ m ∈ (M : Set X), {y | e m y = 1} := by ext; simp [M']
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_eq (hecont m) continuous_const
  refine ⟨∫ x in M', f x ∂μ, (M : Set X) ∪ K₀, hMc.union hK₀c, ?_⟩
  intro L hLc hLo hKL
  have hML : (M : Set X) ⊆ L := Set.subset_union_left.trans hKL
  have hM'L : M' ⊆ L := fun y hy => hKL (Or.inr (hK₀ y hy))
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hMm : MeasurableSet (M : Set X) := hMo.measurableSet
  have hM'm : MeasurableSet M' := hM'cl.measurableSet
  haveI : IsFiniteMeasure (μ.restrict (L : Set X)) := isFiniteMeasure_restrict.mpr hLc.measure_lt_top.ne
  haveI : IsFiniteMeasure (μ.restrict (M : Set X)) := isFiniteMeasure_restrict.mpr hMc.measure_lt_top.ne
  set A := ∫ x in (L : Set X), f x ∂μ with hA
  have h1 : ∀ m ∈ (M : Set X), ∫ x in (L : Set X), f x * e x m ∂μ = A := by
    intro m hm
    rw [hA, ← setIntegral_addSubgroup_add μ L hLm (hML hm) f]
    congr 1; funext x
    rw [hfe, show f m = 1 from hMf hm]; ring
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hint : Integrable (Function.uncurry fun m x => f x * e x m)
      ((μ.restrict (M : Set X)).prod (μ.restrict (L : Set X))) := by
    refine Integrable.mono' (integrable_const C) ?_ ?_
    · exact (Continuous.mul (hf.continuous.comp continuous_snd)
        (he.lc.continuous.comp (continuous_snd.prodMk continuous_fst))).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (hMm.prod hLm) fun p hp => ?_
      show ‖f p.2 * e p.2 p.1‖ ≤ C
      rw [norm_mul, he.norm, mul_one]
      exact hC p.2 hp.2
  have h3 := integral_integral_swap hint
  rw [setIntegral_congr_fun hMm h1, setIntegral_const] at h3
  simp_rw [integral_const_mul, setIntegral_pair_char μ he M hMm] at h3
  have h4 : ∫ x in (L : Set X), f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0) ∂μ
      = ((μ.real (M : Set X) : ℝ) : ℂ) * ∫ x in M', f x ∂μ := by
    have : (fun x => f x * (if ∀ m ∈ (M : Set X), e m x = 1 then ((μ.real (M : Set X) : ℝ) : ℂ) else 0)) =
        Set.indicator M' (fun x => ((μ.real (M : Set X) : ℝ) : ℂ) * f x) := by
      funext x
      by_cases hx : x ∈ M'
      · rw [Set.indicator_of_mem hx, if_pos (show ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
      · rw [Set.indicator_of_notMem hx, if_neg (show ¬ ∀ m ∈ (M : Set X), e m x = 1 from hx)]; ring
    rw [this, integral_indicator hM'm, Measure.restrict_restrict hM'm, Set.inter_eq_left.mpr hM'L,
      integral_const_mul]
  rw [h4, Complex.real_smul] at h3
  have hpos : ((μ.real (M : Set X) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨(hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne', hMc.measure_lt_top.ne⟩
  exact mul_left_cancel₀ hpos h3
end GlobalTheory.KSp
