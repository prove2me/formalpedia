-- Prove2me | solution 1 for GlobalTheory.exists_integrable_density_of_bound_by_integral_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:37.134841+00:00
-- url     : https://prove2.me/submissions/b4ae21aa-5b56-4e57-a83a-e5a47d1a46c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  intro X _ _ _ _ μ K hK hμK S hS Λ C hlin hbd
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set ν := μ.restrict K with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμK.ne
  have hmem : ∀ f : S, MemLp (f : X → ℂ) 2 ν := by
    intro f
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hS f f.2).continuousOn
    exact MemLp.of_bound (hS f f.2).aestronglyMeasurable M
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall hM))
  let T : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (hmem f).toLp _
      map_add' := fun f g => MemLp.toLp_add (hmem f) (hmem g)
      map_smul' := fun c f => MemLp.toLp_const_smul c (hmem f) }
  have hT : ∀ f : S, T f = (hmem f).toLp _ := fun f => rfl
  have hΛ0 : Λ 0 = 0 := by
    have := hlin 0 S.zero_mem 0 S.zero_mem 1
    simpa using this
  let Λ' : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ f
      map_add' := fun f g => by
        have := hlin f f.2 g g.2 1
        simpa using this
      map_smul' := fun c f => by
        have := hlin f f.2 0 S.zero_mem c
        simpa [hΛ0] using this }
  have hΛ' : ∀ f : S, Λ' f = Λ f := fun f => rfl

  have hkey : ∀ f : S, ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ ≤ ((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖ := by
    intro f
    have h12 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν)
      (by norm_num) (hS f f.2).aestronglyMeasurable
    have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [hexp] at h12
    have hint : ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ = (eLpNorm (f : X → ℂ) 1 ν).toReal := by
      rw [integral_norm_eq_lintegral_enorm (hS f f.2).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]
    have hfin : eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top (hmem f).eLpNorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
    rw [hint, hT, Lp.norm_toLp]
    calc _ ≤ (eLpNorm (f : X → ℂ) 2 ν * ν Set.univ ^ (1 / 2 : ℝ)).toReal :=
          ENNReal.toReal_mono hfin h12
      _ = _ := by rw [ENNReal.toReal_mul, mul_comm]
  set B : ℝ := max C 0 * ((ν Set.univ) ^ (1/2 : ℝ)).toReal with hBdef
  have hB : ∀ f : S, ‖Λ' f‖ ≤ B * ‖T f‖ := by
    intro f
    have hI0 : 0 ≤ ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    rw [hΛ']
    calc ‖Λ f‖ ≤ C * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ := hbd f f.2
      _ ≤ max C 0 * ∫ x in K, ‖(f : X → ℂ) x‖ ∂μ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
      _ ≤ max C 0 * (((ν Set.univ) ^ (1/2 : ℝ)).toReal * ‖T f‖) :=
          mul_le_mul_of_nonneg_left (hkey f) (le_max_right _ _)
      _ = B * ‖T f‖ := by rw [hBdef, mul_assoc]
  have hker : LinearMap.ker T ≤ LinearMap.ker Λ' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have := hB f
    rw [hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let φ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ Λ' hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ f : S, φ₀ ⟨T f, LinearMap.mem_range_self T f⟩ = Λ f := by
    intro f
    have h1 : T.quotKerEquivRange.symm ⟨T f, LinearMap.mem_range_self T f⟩
        = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [φ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h1,
      Submodule.liftQ_apply, hΛ']
  have hφb : ∀ v, ‖φ₀ v‖ ≤ B * ‖v‖ := by
    rintro ⟨v, f, rfl⟩
    have := hφ₀ f
    rw [this, ← hΛ']
    exact hB f
  let φ : StrongDual ℂ (LinearMap.range T) := φ₀.mkContinuous B hφb
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range T) φ
  set a₀ : Lp ℂ 2 ν := (InnerProductSpace.toDual ℂ (Lp ℂ 2 ν)).symm g with ha₀
  have hrep : ∀ f : S, inner ℂ a₀ (T f) = Λ f := by
    intro f
    rw [ha₀, InnerProductSpace.toDual_symm_apply]
    have := hg ⟨T f, LinearMap.mem_range_self T f⟩
    rw [this]
    simp only [φ, LinearMap.mkContinuous_apply]
    exact hφ₀ f
  have hm : Measurable (a₀ : X → ℂ) := (Lp.stronglyMeasurable a₀).measurable
  refine ⟨K.indicator (fun x => starRingEnd ℂ (a₀ x)),
    (Complex.continuous_conj.measurable.comp hm).indicator hKm, ?_, ?_, ?_⟩
  · rw [integrable_indicator_iff hKm]
    have : Integrable (a₀ : X → ℂ) ν := (Lp.memLp a₀).integrable (by norm_num)
    exact this.mono (Complex.continuous_conj.comp_aestronglyMeasurable this.1)
      (Filter.Eventually.of_forall fun x => by simp)
  · intro x hx
    exact Set.indicator_of_notMem hx _
  · intro f hf
    have key := hrep ⟨f, hf⟩
    rw [L2.inner_def] at key
    have hae : ((T ⟨f, hf⟩ : Lp ℂ 2 ν) : X → ℂ) =ᵐ[ν] f := MemLp.coeFn_toLp (hmem ⟨f, hf⟩)
    rw [← key]
    have hfun : (fun x => f x * K.indicator (fun x => starRingEnd ℂ (a₀ x)) x)
        = K.indicator (fun x => f x * starRingEnd ℂ (a₀ x)) := by
      funext x
      by_cases hx : x ∈ K <;> simp [hx]
    rw [hfun, integral_indicator hKm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    simp [mul_comm]
end GlobalTheory
