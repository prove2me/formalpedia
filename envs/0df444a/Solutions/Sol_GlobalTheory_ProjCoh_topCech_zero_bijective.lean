-- Prove2me | solution 1 for GlobalTheory.ProjCoh.topCech_zero_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:54.47291+00:00
-- url     : https://prove2.me/submissions/3663f721-7875-4864-a31a-cb22c3234712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_ProjCoh_topCech_surjective

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
theorem _root_.solution (A : Cube.{0} ι R) (hN : Fintype.card ι = 0 + 1) :
    Function.Bijective (topCech A hN) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, topCech_surjective A hN⟩
  have h := congrFun (congrArg Subtype.val ((cechClass_zero_eq_zero_iff A _).1 hx))
    ⟨Finset.univ, hN⟩
  exact (Cube.res_self A _ x).symm.trans h
end GlobalTheory.ProjCoh
