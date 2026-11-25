-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isEquivariant_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:39:49.380799+00:00
-- url     : https://prove2.me/submissions/36c13799-65f7-46d0-8875-4218111fb5ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
namespace GlobalTheory.EigenSplit
theorem _root_.solution (ρ : O →+* Module.End R N) : IsEquivariant ρ ρ LinearMap.id :=
  fun _ _ => rfl
end GlobalTheory.EigenSplit
