-- Prove2me | solution 1 for GlobalTheory.MainTerm.toW_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:07.659215+00:00
-- url     : https://prove2.me/submissions/e0575a57-16bf-4552-812c-9d159bd48911

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HPullWUpGTwoGroupEmbeddingEqRename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution {C : Type} [Field C] {I : Fin 2 → Type} {g g' : Fin 2} (h : g' ≠ g) (u : I g → C)
    (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]
end GlobalTheory.MainTerm
