-- Prove2me | solution 1 for GlobalTheory.TraceConj.colRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:14.290202+00:00
-- url     : https://prove2.me/submissions/985b9644-9ad4-40c8-8a71-01c7c70ba9b4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceConj
variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}
namespace GlobalTheory.TraceConj
theorem _root_.solution (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := rfl
end GlobalTheory.TraceConj
