-- Prove2me | solution 1 for GlobalTheory.EigenSplit.projective_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:07.10351+00:00
-- url     : https://prove2.me/submissions/6acf2876-e2f8-4ad1-bb1b-8d0411373995

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
variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h
variable (ρ)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Module.Projective R N] (i : ι) :
    Module.Projective R (eigenSub ρ (σ i)) := by
  classical
  exact Module.Projective.of_split _ _ (projTo_comp_subtype h ρ i)
end GlobalTheory.EigenSplit
