-- Prove2me | solution 1 for GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:34.712721+00:00
-- url     : https://prove2.me/submissions/4465d707-41a5-4199-a171-319f39268f76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCoboundaryOfMixedOverlaps
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCoboundaryOfMixedOverlapsStatement
import Theorems.Thm_GlobalTheory_KS_isCob_of_mixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  first | exact @GlobalTheory.KS.isCob_of_mixed | exact GlobalTheory.KS.isCob_of_mixed | (intros; apply GlobalTheory.KS.isCob_of_mixed <;> assumption)
end _root_.GlobalTheory.T
