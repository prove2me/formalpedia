-- Prove2me | solution 1 for GlobalTheory.MvPoly.span_ringOfIntegers_basis_integralPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:44.445819+00:00
-- url     : https://prove2.me/submissions/8025e1a3-c347-4450-95a4-9ea7cc4827fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
import Theorems.Thm_GlobalTheory_MvPoly_smul_mem_integralPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]
namespace GlobalTheory.MvPoly
theorem _root_.solution {W : Submodule K (MvPolynomial σ K)} {ι : Type*}
    (b : Basis ι ℤ (integralPart W)) :
    (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
      integralPart W := by
  refine le_antisymm (fun P hP => ?_) (fun P hP => ?_)
  · change P ∈ span (𝓞 K) _ at hP
    induction hP using span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact (b j).2
    | zero => simp
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => exact smul_mem_integralPart c hy
  · have h4 := Submodule.mem_map_of_mem (f := (integralPart W).subtype) (b.mem_span ⟨P, hP⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact span_subset_span ℤ (𝓞 K) _ h4
end GlobalTheory.MvPoly
