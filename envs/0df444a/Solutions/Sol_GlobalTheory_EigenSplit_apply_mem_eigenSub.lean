-- Prove2me | solution 1 for GlobalTheory.EigenSplit.apply_mem_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:58.631769+00:00
-- url     : https://prove2.me/submissions/a9b4ea16-ec69-42b1-be1a-bc4404d1363a

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
theorem _root_.solution {ρ : O →+* Module.End R N} {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) (a : O) : ρ a x ∈ eigenSub ρ χ := by
  rw [mem_eigenSub.1 hx a]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.EigenSplit
