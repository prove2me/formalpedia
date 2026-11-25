-- Prove2me | solution 1 for GlobalTheory.ProjCoh.grAug_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:00.553119+00:00
-- url     : https://prove2.me/submissions/7e3ca0bd-d233-4507-960a-d906a71f3705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_cube_exactAt
import Theorems.Thm_GlobalTheory_grAug_bijective_iff


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
theorem _root_.solution (hN : 1 ≤ N) :
    Function.Bijective (grAug (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n) :=
  (grAug_bijective_iff _ n).2 ⟨cube_exactAt R N n (by omega), cube_exactAt R N n (by omega)⟩
end GlobalTheory.ProjCoh
