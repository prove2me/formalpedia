-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isProj_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:32.336846+00:00
-- url     : https://prove2.me/submissions/b13aadf1-43ed-4b80-9943-092a50a00442

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
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
namespace GlobalTheory.EigenSplit
theorem _root_.solution (i : ι) : LinearMap.IsProj (eigenSub ρ (σ i)) (proj h ρ i) :=
  ⟨proj_mem h ρ i, fun _ hx => proj_of_mem h hx⟩
end GlobalTheory.EigenSplit
