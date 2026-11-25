-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_isSymm_mul_eq_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:43.073841+00:00
-- url     : https://prove2.me/submissions/2e812e5c-d41f-4e35-93ba-89ffa548c7a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_cyclic_decomposition
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_comm
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_add_left
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_C_smul_left
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_sumForm_X_smul
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_sumForm_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_isSymm_of_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
open scoped Matrix
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F) :
    ∃ S : GL (Fin n) F, (S : Matrix (Fin n) (Fin n) F).IsSymm ∧
      (S : Matrix (Fin n) (Fin n) F) * A = Aᵀ * S := by
  classical
  obtain ⟨ι, hι, q, hq0, -, ⟨e⟩⟩ := exists_cyclic_decomposition A
  set φ := Matrix.toLin' A
  let E : (Fin n → F) → CycSum q := fun v => e (Module.AEval'.of φ v)
  have hEadd : ∀ v w, E (v + w) = E v + E w := fun v w => by simp [E]
  have hEsmul : ∀ (c : F) v, E (c • v) = C c • E v := fun c v => by
    simp only [E, map_smul]
    rw [← Module.AEval.C_smul, map_smul]
  have hEA : ∀ v, E (A.mulVec v) = (X : F[X]) • E v := fun v => by
    simp only [E]
    rw [← Matrix.toLin'_apply, ← Module.AEval'.X_smul_of, map_smul]
  have hEinj : ∀ w, E w = 0 → w = 0 := fun w h => by
    have : Module.AEval'.of φ w = 0 := by
      rw [← e.map_eq_zero_iff]
      exact h
    simpa using this
  have hEsurj : ∀ x, ∃ v, E v = x := fun x =>
    ⟨(Module.AEval'.of φ).symm (e.symm x), by simp [E]⟩
  refine exists_isSymm_of_form A (fun v w => sumForm q hq0 (E v) (E w))
    (fun v w => sumForm_comm q hq0 _ _)
    (fun v v' w => by simp only [hEadd, sumForm_add_left])
    (fun c v w => by simp only [hEsmul, sumForm_C_smul_left])
    (fun v w => by simp only [hEA, sumForm_X_smul])
    (fun w hw => ?_)
  by_contra hw0
  obtain ⟨x, hx⟩ := exists_sumForm_ne_zero q hq0 (fun h => hw0 (hEinj w h))
  obtain ⟨v, rfl⟩ := hEsurj x
  exact hx (hw v)
end GroundTheory.Automorphic.ContragredientTranspose
