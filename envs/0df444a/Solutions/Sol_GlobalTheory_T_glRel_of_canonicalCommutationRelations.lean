-- Prove2me | solution 1 for GlobalTheory.T.glRel_of_canonicalCommutationRelations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:29.709955+00:00
-- url     : https://prove2.me/submissions/84dc9d47-f16f-40d1-9b10-cf2ca43c9fbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlRelOfCanonicalCommutationRelationsStatement
import Theorems.Thm_GlobalTheory_Mem_Lift_glRel_of_isCCR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
end _root_.GlobalTheory.T
