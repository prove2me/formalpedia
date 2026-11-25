-- Prove2me | solution 1 for GlobalTheory.map_xProd_pow_smul_of_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:40.809277+00:00
-- url     : https://prove2.me/submissions/f43f563e-31ec-47e1-9774-7c24cefbc51f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeGradedPiece
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBaseChangeGrCubeIso
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
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι R₀ R : Type} [CommRing R₀] [CommRing R] {N₀ N : Type}
    [AddCommGroup N₀] [Module (MvPolynomial ι R₀) N₀] [AddCommGroup N]
    [Module (MvPolynomial ι R) N] (ψ : N₀ → N)
    (hX : ∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y)
    (s : Finset ι) (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
  classical
  have h1 : ∀ y, ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [xProd, xProd, Finset.prod_insert ha, Finset.prod_insert ha, mul_smul, mul_smul, hX, ih]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h1, ih]
end GlobalTheory
