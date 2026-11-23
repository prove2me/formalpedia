-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.sum_fixing_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:05.633579+00:00
-- url     : https://prove2.me/submissions/56b81599-b226-432c-8c81-3cf67cb3b3bc

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_sign_of_fixing
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_prod_of_fixing

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∑ σ ∈ Finset.filter (fun σ => ∀ i ∈ Sᶜ, σ i = i) Finset.univ,
      (Equiv.Perm.sign σ : ℝ) * ∏ i ∈ S, M (σ i) i =
    (principalSubmatrix n M S).det := by
  -- Use the Leibniz formula
  rw [Matrix.det_apply']
  -- Reindex using fixingPermEquiv via Finset.sum_bij
  symm
  apply Finset.sum_bij (fun τ _ => ((fixingPermEquiv n S).symm τ).val)
  · -- Map goes into filter
    intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((fixingPermEquiv n S).symm τ).prop
  · -- Injective
    intro τ₁ _ τ₂ _ heq
    have heq' : (fixingPermEquiv n S).symm τ₁ = (fixingPermEquiv n S).symm τ₂ :=
      Subtype.ext heq
    exact (fixingPermEquiv n S).symm.injective heq'
  · -- Surjective
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨fixingPermEquiv n S ⟨σ, hσ⟩, Finset.mem_univ _, ?_⟩
    simp only [Equiv.symm_apply_apply, Subtype.coe_mk]
  · -- Equal function values
    intro τ _
    have hσ := ((fixingPermEquiv n S).symm τ).prop
    have heq : (⟨((fixingPermEquiv n S).symm τ).val, hσ⟩ :
        {σ : Equiv.Perm (Fin n) // ∀ i ∈ Sᶜ, σ i = i}) = (fixingPermEquiv n S).symm τ := rfl
    congr 1
    · -- Signs match
      rw [sign_of_fixing n _ S hσ, heq, Equiv.apply_symm_apply]
    · -- Products match
      rw [prod_of_fixing n M _ S hσ, heq, Equiv.apply_symm_apply]
end GroupTheoreticShannonCapacity.P0Matrix
