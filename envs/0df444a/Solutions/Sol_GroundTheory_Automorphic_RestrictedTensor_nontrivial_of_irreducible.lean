-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:47.106887+00:00
-- url     : https://prove2.me/submissions/06dfbd2c-f46e-41f5-a0b4-b1307641c688

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ M₁ V₁} (h : ρ.IsIrreducible) :
    Nontrivial V₁ := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
end GroundTheory.Automorphic.RestrictedTensor
