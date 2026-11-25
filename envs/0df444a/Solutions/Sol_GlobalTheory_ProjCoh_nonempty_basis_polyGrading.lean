-- Prove2me | solution 1 for GlobalTheory.ProjCoh.nonempty_basis_polyGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:19.803887+00:00
-- url     : https://prove2.me/submissions/c301c04c-86ef-4346-b074-dcc87db581fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
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
    Nonempty (Module.Basis {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = n} R
      (polyGrading (Fin (N + 1)) R n)) := by
  obtain ⟨b, -⟩ := exists_basis_grCube_polyGrading (Fin (N + 1)) R n
  have h : ∀ a : Fin (N + 1) → ℤ, Finset.univ.filter (fun i => a i < 0) ⊆ ∅ ↔ ∀ i, 0 ≤ a i :=
    fun a => by simp [Finset.filter_eq_empty_iff]
  exact ⟨((b ∅).map (homLocEmptyEquiv (Fin (N + 1)) _ n).symm).reindex
    { toFun := fun a => ⟨fun i => (a.1.1 i).toNat, by
        rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg ((h _).1 a.2 i), a.1.2]⟩
      invFun := fun a => ⟨⟨fun i => a.1 i, a.2⟩, (h _).2 fun i => Int.natCast_nonneg _⟩
      left_inv := fun a => Subtype.ext (Subtype.ext
        (funext fun i => Int.toNat_of_nonneg ((h _).1 a.2 i)))
      right_inv := fun a => rfl }⟩
end GlobalTheory.ProjCoh
