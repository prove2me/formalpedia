-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.evPt_eq_upt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:38.197614+00:00
-- url     : https://prove2.me/submissions/faa3f409-671b-422a-8916-b37d8bf276b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : evPt τ B = upt (tauPt τ B) := by
  funext p
  simp only [evPt, upt, tauPt]
  split_ifs <;> simp [Matrix.one_apply, *]
end GlobalTheory.AlgWtHW
