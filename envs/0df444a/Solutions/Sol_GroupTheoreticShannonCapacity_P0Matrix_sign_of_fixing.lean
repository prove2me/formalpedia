-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.sign_of_fixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:05.58879+00:00
-- url     : https://prove2.me/submissions/9daa67a4-83b5-4400-b1fe-8bc9bc606a9d

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hfix : ∀ i ∈ Sᶜ, σ i = i) :
    Equiv.Perm.sign σ = Equiv.Perm.sign (fixingPermEquiv n S ⟨σ, hfix⟩) := by
  -- fixingPermEquiv = permCongr orderEmbEquiv ∘ subtypePerm
  -- sign is preserved by both (via sign_subtypePerm and sign_permCongr)
  have hS_eq : ∀ x, σ x ∈ S ↔ x ∈ S := fun x => (perm_mem_of_fixing n σ S hfix x).symm
  have hmoved : ∀ x, σ x ≠ x → x ∈ S := by
    intro x hne
    by_contra hx
    have hxc : x ∈ Sᶜ := Finset.mem_compl.mpr hx
    exact hne (hfix x hxc)
  -- The proof uses sign_subtypePerm and sign_permCongr
  unfold fixingPermEquiv
  simp only [Equiv.trans_apply, Equiv.Perm.sign_permCongr]
  convert (Equiv.Perm.sign_subtypePerm σ hS_eq hmoved).symm
  rfl
end GroupTheoreticShannonCapacity.P0Matrix
