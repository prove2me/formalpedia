-- Prove2me | solution 1 for GlobalTheory.MainTerm.toW_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:00.690796+00:00
-- url     : https://prove2.me/submissions/53804693-da76-46c8-8d6a-0e0c28845e09

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
theorem _root_.solution {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by
  simp [toW]
end GlobalTheory.MainTerm
