-- Prove2me | solution 1 for GlobalTheory.EigenSplit.finite_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:48.772463+00:00
-- url     : https://prove2.me/submissions/808da947-a08c-4a5b-83c3-3fccac4878cb

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
theorem _root_.solution [Module.Finite R N] (i : ι) : Module.Finite R (eigenSub ρ (σ i)) := by
  classical
  exact Module.Finite.of_surjective (projTo h ρ i) fun y =>
    ⟨y, LinearMap.congr_fun (projTo_comp_subtype h ρ i) y⟩
end GlobalTheory.EigenSplit
