-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.exists_schwartz_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:57.378796+00:00
-- url     : https://prove2.me/submissions/eaf41124-19e8-4246-b51b-203a19737ba2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_exists_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
namespace GlobalTheory.CompactAvgSchwartz
section Real
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem integrable_of_continuous_isFiniteMeasure {E : Type} [NormedAddCommGroup E] [MeasurableSpace S] [OpensMeasurableSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] {φ : S → E} (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.mono' (integrable_const C) hφ.aestronglyMeasurable_of_compactSpace
    (ae_of_all _ fun s => hC s (Set.mem_univ _))
private theorem hasFDerivAt_integral_of_continuous_fderiv {E : Type} [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S)
    [IsFiniteMeasure ν] (G : S → V → E) (hG : ∀ s, Differentiable ℝ (G s))
    (hc : Continuous fun p : S × V => G p.1 p.2) (hd : Continuous fun p : S × V => fderiv ℝ (G p.1) p.2)
    (x₀ : V) : HasFDerivAt (fun x => ∫ s, G s x ∂ν) (∫ s, fderiv ℝ (G s) x₀ ∂ν) x₀ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
    hd.continuousOn
  have hcs : ∀ x, Continuous fun s => G s x := fun x => hc.comp (continuous_id.prodMk continuous_const)
  have hds : Continuous fun s => fderiv ℝ (G s) x₀ := hd.comp (continuous_id.prodMk continuous_const)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x s => G s x)
    (F' := fun x s => fderiv ℝ (G s) x) (bound := fun _ => C) (Metric.closedBall_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hcs x).aestronglyMeasurable_of_compactSpace)
    (integrable_of_continuous_isFiniteMeasure ν (hcs x₀)) hds.aestronglyMeasurable_of_compactSpace
    (ae_of_all _ fun s x hx => hC (s, x) ⟨Set.mem_univ _, hx⟩) (integrable_const C)
    (ae_of_all _ fun s x _ => (hG s x).hasFDerivAt)
private theorem contDiff_iteratedFDeriv_schwartz_comp (f : SchwartzMap V ℂ) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : (V →L[ℝ] V) × V => iteratedFDeriv ℝ m (fun y => f (p.1 y)) p.2) := by
  induction m with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ V ℂ).symm.contDiff.comp
      (f.smooth'.comp isBoundedBilinearMap_apply.contDiff)
  | succ m ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have hf : ContDiff ℝ ∞ (Function.uncurry fun (p : (V →L[ℝ] V) × V) (y : V) =>
        iteratedFDeriv ℝ m (fun z => f (p.1 z)) y) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).symm.contDiff.comp
      (hf.fderiv contDiff_snd (by simp))
end Real
section Fin
variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] {a b : S → Y → Y} {g : Y → ℂ}
end Fin
end GlobalTheory.CompactAvgSchwartz
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution [FiniteDimensional ℝ V] [MeasurableSpace S] [OpensMeasurableSpace S] (ν : Measure S)
    [IsFiniteMeasure ν] (L Li : S → V →L[ℝ] V) (hL : Continuous L) (hLi : Continuous Li) (h : ∀ s x, Li s (L s x) = x)
    (f : SchwartzMap V ℂ) : ∃ F : SchwartzMap V ℂ, ∀ x, F x = ∫ s, f (L s x) ∂ν := by
  have hpair : Continuous fun p : S × V => (L p.1, p.2) := (hL.comp continuous_fst).prodMk continuous_snd
  have hA : ∀ (m : ℕ) (x : V), HasFDerivAt (fun x => ∫ s, iteratedFDeriv ℝ m (fun y => f (L s y)) x ∂ν)
      (∫ s, fderiv ℝ (iteratedFDeriv ℝ m (fun y => f (L s y))) x ∂ν) x := by
    intro m x
    refine hasFDerivAt_integral_of_continuous_fderiv ν (fun s => iteratedFDeriv ℝ m (fun y => f (L s y))) (fun s => ?_)
      ((contDiff_iteratedFDeriv_schwartz_comp f m).continuous.comp hpair) ?_ x
    · exact ((contDiff_iteratedFDeriv_schwartz_comp f m).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    · have e : (fun p : S × V => fderiv ℝ (iteratedFDeriv ℝ m (fun y => f (L p.1 y))) p.2) =
          fun p => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ
            (iteratedFDeriv ℝ (m + 1) (fun y => f (L p.1 y)) p.2) := by
        funext p
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).continuous.comp
        ((contDiff_iteratedFDeriv_schwartz_comp f (m + 1)).continuous.comp hpair)
  have key : ∀ (m : ℕ) (x : V), iteratedFDeriv ℝ m (fun x => ∫ s, f (L s x) ∂ν) x =
      ∫ s, iteratedFDeriv ℝ m (fun y => f (L s y)) x ∂ν := by
    intro m
    induction m with
    | zero =>
      intro x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact (ContinuousLinearEquiv.integral_comp_comm (continuousMultilinearCurryFin0 ℝ V ℂ).symm.toContinuousLinearEquiv _).symm
    | succ m ih =>
      intro x
      have hfun : iteratedFDeriv ℝ m (fun x => ∫ s, f (L s x) ∂ν) =
          fun x => ∫ s, iteratedFDeriv ℝ m (fun y => f (L s y)) x ∂ν := funext ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfun, (hA m x).fderiv]
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
      exact (ContinuousLinearEquiv.integral_comp_comm
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).symm.toContinuousLinearEquiv _).symm
  have hsmooth : ContDiff ℝ ∞ (fun x => ∫ s, f (L s x) ∂ν) := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
    rw [funext (key m)]
    exact fun x => (hA m x).differentiableAt
  refine ⟨⟨fun x => ∫ s, f (L s x) ∂ν, hsmooth, fun k n => ?_⟩, fun x => rfl⟩
  obtain ⟨M, -, hM⟩ := exists_bound L Li hL hLi h f k n
  refine ⟨M * ν.real Set.univ, fun x => ?_⟩
  rw [key n x]
  calc ‖x‖ ^ k * ‖∫ s, iteratedFDeriv ℝ n (fun y => f (L s y)) x ∂ν‖
      = ‖∫ s, (‖x‖ ^ k) • iteratedFDeriv ℝ n (fun y => f (L s y)) x ∂ν‖ := by
        rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ M * ν.real Set.univ := norm_integral_le_of_norm_le_const (ae_of_all _ fun s => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hM s x)
end GlobalTheory.CompactAvgSchwartz
