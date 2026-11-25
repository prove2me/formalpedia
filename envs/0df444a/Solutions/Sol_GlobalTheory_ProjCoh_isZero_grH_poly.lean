-- Prove2me | solution 1 for GlobalTheory.ProjCoh.isZero_grH_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:07.499534+00:00
-- url     : https://prove2.me/submissions/ebbe501a-fea9-48df-b42f-6976c8e0dd4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_cube_exactAt
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff_cube


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)
namespace GlobalTheory.ProjCoh
theorem _root_.solution {p : ℕ} (h0 : p ≠ 0) (hp : p ≠ N) :
    IsZero (grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff_cube _ q).2 (cube_exactAt R N n (by omega)))
end GlobalTheory.ProjCoh
