-- Prove2me | solution 1 for GlobalTheory.T.fourier_prod_single_coordinate_functions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:31.158678+00:00
-- url     : https://prove2.me/submissions/9d944648-86f6-45b0-b7c8-b836e64533f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctionsStatement
import Theorems.Thm_GlobalTheory_fourier_prod_coord_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  first | exact @GlobalTheory.fourier_prod_coord_complex | exact GlobalTheory.fourier_prod_coord_complex | (intros; apply GlobalTheory.fourier_prod_coord_complex <;> assumption)
end _root_.GlobalTheory.T
