-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:09.587458+00:00
-- url     : https://prove2.me/submissions/c47e2099-7d32-4cba-a8ca-98956e5af5ad

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_quad_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_abs_det_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_measurePreserving_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_measurableEmbedding_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧
    ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by
  have first : ∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x := by
    intro τ x
    unfold gauss
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [quad_mulVec, quad_mulVec, hg w]
  refine ⟨first, fun τ => ?_⟩
  have hdet : ∀ w, (B.map (ρ w)).det ≠ 0 := by
    intro w
    have e : (B.map (ρ w)).det = ρ w B.det := (RingHom.map_det (ρ w) B).symm
    rw [e]
    exact (map_ne_zero (ρ w)).mpr hB
  have habs : ∀ w, |(gi w).det| = 1 := fun w => abs_det_eq_one (hdet w) (hg w)
  have hne : ∀ w, (gi w).det ≠ 0 := by
    intro w h0
    have := habs w
    rw [h0, abs_zero] at this
    exact zero_ne_one this
  have hmp : MeasurePreserving (fun (x : InfinitePlace F → ι → ℝ) w => gi w *ᵥ x w)
      volume volume :=
    volume_preserving_pi fun w => measurePreserving_mulVec (habs w)
  have hint := hmp.integral_comp (measurableEmbedding_mulVec hne) (gauss B ρ P τ)
  unfold cG
  rw [← hint]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (first τ x).symm)
end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
