-- Prove2me | solution 1 for GlobalTheory.EigenSplit.IsEquivariant.eigenMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:41:26.322468+00:00
-- url     : https://prove2.me/submissions/ac4b8f7a-23be-4a1e-9534-75a4a311c4cb

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
namespace IsEquivariant
theorem _root_.solution {ρ : O →+* Module.End R N}
    {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R)
    (hi : Function.Injective f) : Function.Injective (hf.eigenMap χ) :=
  fun _ _ hxy => Subtype.ext (hi (congrArg Subtype.val hxy))
end IsEquivariant
end GlobalTheory.EigenSplit
