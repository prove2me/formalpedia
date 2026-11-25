-- Prove2me | solution 1 for GlobalTheory.UTrans.CharDet.refl_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:31.974659+00:00
-- url     : https://prove2.me/submissions/7161a61b-a89d-461b-a59e-b8aa6ef2e100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.CharDet
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.CharDet
theorem _root_.solution (x : Fin n → E) : tv σ G x ((1 - 1) / hf σ G x x) = 1 := by
  ext a b
  simp [tv]
end GlobalTheory.UTrans.CharDet
