-- Prove2me | solution 1 for GroundTheory.Automorphic.diagonalGL_mem_elementarySubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:58.454936+00:00
-- url     : https://prove2.me/submissions/c432a9a4-fa9e-4e03-bb24-3be3a07c8626

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
import Theorems.Thm_GroundTheory_Automorphic_coe_diagonalGL
import Theorems.Thm_GroundTheory_Automorphic_diagonal_update_mem_elementarySubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_diagonalGL

set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution {d : n → Rˣ} (hd : ∏ k, d k = 1) :
    diagonalGL d ∈ elementarySubgroup n R := by
  classical
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have : d = 1 := funext fun k => isEmptyElim k
    rw [this, map_one]
    exact one_mem _
  have hmem : ∀ i ∈ Finset.univ.erase i₀,
      Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹ ∈
        (elementarySubgroup n R).comap (diagonalGL (n := n) (R := R)) := fun i hi =>
    diagonal_update_mem_elementarySubgroup i i₀ (Finset.ne_of_mem_erase hi) (d i)
  have hprod := Subgroup.prod_mem _ hmem
  have heq : ∏ i ∈ Finset.univ.erase i₀, (Pi.mulSingle i (d i) * Pi.mulSingle i₀ (d i)⁻¹) = d := by
    funext k
    rw [Finset.prod_apply]
    simp only [Pi.mul_apply, Pi.mulSingle_apply]
    by_cases hk : k = i₀
    · subst hk
      have h1 : ∀ i ∈ Finset.univ.erase k,
          ((if k = i then d i else 1) * if k = k then (d i)⁻¹ else 1) = (d i)⁻¹ := by
        intro i hi
        rw [if_neg (Finset.ne_of_mem_erase hi).symm, if_pos rfl, one_mul]
      rw [Finset.prod_congr rfl h1, Finset.prod_inv_distrib]
      have h2 := Finset.mul_prod_erase Finset.univ d (Finset.mem_univ k)
      rw [hd] at h2
      rw [eq_comm, ← mul_eq_one_iff_eq_inv]
      exact h2
    · have h1 : ∀ i ∈ Finset.univ.erase i₀,
          ((if k = i then d i else 1) * if k = i₀ then (d i)⁻¹ else 1) =
            if k = i then d i else 1 := by
        intro i _
        rw [if_neg hk, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_ite_eq]
      rw [if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
  rw [heq] at hprod
  exact hprod
end GroundTheory.Automorphic
