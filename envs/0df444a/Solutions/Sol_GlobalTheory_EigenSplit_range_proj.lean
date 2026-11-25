-- Prove2me | solution 1 for GlobalTheory.EigenSplit.range_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:39.538377+00:00
-- url     : https://prove2.me/submissions/2dd07ab3-e56b-4c32-8b12-262494c3be75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isProj_proj

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
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
namespace GlobalTheory.EigenSplit
theorem _root_.solution (i : ι) : LinearMap.range (proj h ρ i) = eigenSub ρ (σ i) :=
  (isProj_proj h ρ i).range
end GlobalTheory.EigenSplit
