-- Prove2me | solution 1 for GlobalTheory.ProjCoh.nonempty_grH_zero_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:24.292834+00:00
-- url     : https://prove2.me/submissions/04867105-4a5f-46c0-91f0-e2441faaafe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_topCech_zero_bijective
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_exists_basis_grCube_polyGrading
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)
namespace GlobalTheory.ProjCoh
theorem _root_.solution :
    Nonempty (grH (Fin (0 + 1)) (polyGrading (Fin (0 + 1)) R) n 0 ≃ₗ[R] R) := by
  obtain ⟨b, -⟩ := exists_basis_grCube_polyGrading (Fin (0 + 1)) R n
  let u : Unique {a : {a : Fin (0 + 1) → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ Finset.univ} :=
    { default := ⟨⟨fun _ => n, by simp⟩, Finset.subset_univ _⟩
      uniq := fun a => Subtype.ext (Subtype.ext (funext fun i => by
        obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
        simpa using a.1.2)) }
  exact ⟨(LinearEquiv.ofBijective _ (topCech_zero_bijective _ (Fintype.card_fin _))).symm.trans
    ((b Finset.univ).repr.trans (Finsupp.uniqueLinearEquiv R R default))⟩
end GlobalTheory.ProjCoh
