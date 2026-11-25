-- Prove2me | solution 1 for GlobalTheory.ProjCoh.choose_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:54.946793+00:00
-- url     : https://prove2.me/submissions/7b1b9e15-8d3a-4ea1-8857-5f83bae3946b

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
namespace GlobalTheory.ProjCoh
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    Ring.choose (n + N) N = ((n + N).toNat.choose N : ℤ) + (-1) ^ N * (-n - 1).toNat.choose N := by
  rcases lt_or_ge (n + N) 0 with h | h
  · have e := Ring.choose_neg (-(n + N)) N
    rw [neg_neg, show -(n + N) + N - 1 = ((-n - 1).toNat : ℤ) by omega, Ring.choose_natCast] at e
    rw [e, Nat.choose_eq_zero_of_lt (n := (n + N).toNat) (by omega), Units.smul_def,
      Int.coe_negOnePow_natCast]
    simp
  · rw [Nat.choose_eq_zero_of_lt (n := (-n - 1).toNat) (by omega), ← Ring.choose_natCast,
      Int.toNat_of_nonneg h]
    simp
end GlobalTheory.ProjCoh
