-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.val_unipEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:34.978558+00:00
-- url     : https://prove2.me/submissions/53ee9649-f96b-435e-9bc1-45229f3d82ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (x : Idx e → R) :
    ((((unipEquiv e).symm x : unipRad R e) : GL n R) : Matrix n n R) = 1 + mat e x := rfl
end GlobalTheory.SmGL.UnipHaar
