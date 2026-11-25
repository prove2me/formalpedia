-- Prove2me | solution 1 for GlobalTheory.ProjCoh.topCech_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:51.967882+00:00
-- url     : https://prove2.me/submissions/479dfc58-1231-474c-9197-0fc394bf8cbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading

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
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
namespace GlobalTheory.ProjCoh
theorem _root_.solution (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1)
    (x : A.obj Finset.univ) :
    topCech A hN x = 0 ↔ ∃ y, Cube.d A (N + 1) y = CubeTop.topTerm A hN x :=
  cechClass_succ_eq_zero_iff A N _
end GlobalTheory.ProjCoh
