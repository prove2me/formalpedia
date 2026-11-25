-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.nontrivial_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:24.846385+00:00
-- url     : https://prove2.me/submissions/8b50b9ea-c567-4833-bf53-e5f704bd614a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Irreducible

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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
omit [∀ v, Module ℂ (V v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ H W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
end GroundTheory.Automorphic.RestrictedTensor
