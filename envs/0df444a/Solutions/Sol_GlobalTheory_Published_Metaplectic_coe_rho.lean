-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.coe_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:00.425306+00:00
-- url     : https://prove2.me/submissions/1ec28f55-24c8-4559-9fd8-dd4b724c22d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory.Published
namespace Metaplectic
variable {ι : Type} [Fintype ι]
private lemma hasTemperateGrowth_eChar_dotProduct_phase (w : (ι → ℝ) × (ι → ℝ)) :
    (fun x : ι → ℝ => eChar (x ⬝ᵥ w.2 + ⅟(2 : ℝ) * (w.1 ⬝ᵥ w.2))).HasTemperateGrowth := by
  have hl : (fun x : ι → ℝ => x ⬝ᵥ w.2).HasTemperateGrowth := by
    have h : (fun x : ι → ℝ => x ⬝ᵥ w.2) = fun x => ∑ i, x i * w.2 i := rfl
    rw [h]
    exact Function.HasTemperateGrowth.sum fun i _ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasTemperateGrowth.mul
        (Function.HasTemperateGrowth.const _)
  exact hasTemperateGrowth_eChar.comp (hl.add (Function.HasTemperateGrowth.const _))
end Metaplectic
open Metaplectic
end GlobalTheory.Published
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Published.Metaplectic
theorem _root_.solution (w : (ι → ℝ) × (ι → ℝ)) (φ : 𝓢(ι → ℝ, ℂ)) : ⇑(rho w φ) = GlobalTheory.WeilM.schr eChar w φ := by
  funext x
  simp only [rho, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eChar_dotProduct_phase w), SchwartzMap.compSubConstCLM_apply]
  simp [GlobalTheory.WeilM.schr]
end GlobalTheory.Published.Metaplectic
