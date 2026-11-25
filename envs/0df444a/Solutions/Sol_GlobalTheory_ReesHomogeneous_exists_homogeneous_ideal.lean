-- Prove2me | solution 1 for GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:35.817827+00:00
-- url     : https://prove2.me/submissions/545553d4-3cdc-4595-941a-15ebceb118ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebra
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.ReesHomogeneous
namespace GlobalTheory.ReesHomogeneous
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, coeff m G = (coeff m F).1.coeff e) → G ∈ J e) := by
  intro R _ I n J H
  refine ⟨reesIdeal I J H, ?_, ?_⟩
  · intro F hF d d' e
    show piece I e (homogeneousComponent d' (homogeneousComponent d F)) ∈ J e
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d F)]
    split_ifs
    · exact hF d e
    · simp
  · intro t F hFt
    have hG : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R),
        (∀ m, coeff m G = (coeff m F).1.coeff e) → G = piece I e F := by
      intro e G hG
      ext m
      rw [hG, coeff_piece]
    constructor
    · intro hF e G hGc
      rw [hG e G hGc]
      have := hF t e
      rwa [homogeneousComponent_eq_self hFt] at this
    · intro h d e
      show piece I e (homogeneousComponent d F) ∈ J e
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule t F).2 hFt)]
      split_ifs
      · exact h e _ fun m => coeff_piece e F m
      · simp
end GlobalTheory.ReesHomogeneous
