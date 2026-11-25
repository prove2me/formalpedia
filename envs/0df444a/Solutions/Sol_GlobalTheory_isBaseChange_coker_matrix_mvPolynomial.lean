-- Prove2me | solution 1 for GlobalTheory.isBaseChange_coker_matrix_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:39.038374+00:00
-- url     : https://prove2.me/submissions/34421564-c545-42b0-ba4d-08d6e47e4891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeCokerMatrixMvPolynomial
import Theorems.Thm_GlobalTheory_exists_isBaseChange_coker
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
theorem _root_.solution :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l
end GlobalTheory
