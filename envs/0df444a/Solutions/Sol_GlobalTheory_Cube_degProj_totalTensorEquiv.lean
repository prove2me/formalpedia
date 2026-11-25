-- Prove2me | solution 1 for GlobalTheory.Cube.degProj_totalTensorEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:11.368176+00:00
-- url     : https://prove2.me/submissions/39c9c37a-91c9-47cf-8648-e525fbae5250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_degProj_apply
import Theorems.Thm_GlobalTheory_Cube_card_parts
import Theorems.Thm_GlobalTheory_Cube_totalTensorEquiv_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
namespace GlobalTheory.Cube
theorem _root_.solution (n : ℕ) (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    degProj (extTensor A B) n (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, TensorProduct.map (degProj A x.1) (degProj B x.2) :
        Module.End K _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    funext w
    rw [LinearMap.sum_apply, map_sum, Finset.sum_apply, degProj_apply,
      card_parts]
    have h : ∀ p : ℕ × ℕ, totalTensorEquiv A B
        (TensorProduct.map (degProj A p.1) (degProj B p.2) (x ⊗ₜ y)) w =
        if ((part (inlEmb ι κ) w).card, (part (inrEmb ι κ) w).card) = p then
          totalTensorEquiv A B (x ⊗ₜ y) w else 0 := fun p => by
      rw [TensorProduct.map_tmul, totalTensorEquiv_tmul, totalTensorEquiv_tmul, degProj_apply,
        degProj_apply]
      by_cases h1 : (part (inlEmb ι κ) w).card = p.1
      · by_cases h2 : (part (inrEmb ι κ) w).card = p.2
        · rw [if_pos h1, if_pos h2]
          exact (if_pos (Prod.ext h1 h2)).symm
        · rw [if_neg h2, tmul_zero]
          exact (if_neg fun h => h2 (congrArg Prod.snd h)).symm
      · rw [if_neg h1, zero_tmul]
        exact (if_neg fun h => h1 (congrArg Prod.fst h)).symm
    rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_ite_eq]
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
end GlobalTheory.Cube
