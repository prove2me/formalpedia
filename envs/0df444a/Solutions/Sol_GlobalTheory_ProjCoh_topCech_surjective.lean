-- Prove2me | solution 1 for GlobalTheory.ProjCoh.topCech_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:27.625585+00:00
-- url     : https://prove2.me/submissions/a1ea2f04-b6c2-4c9b-bd89-2927952d3bd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
import Theorems.Thm_GlobalTheory_CubeTop_topTerm_surjective


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
theorem _root_.solution (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1) :
    Function.Surjective (topCech A hN) := fun y => by
  obtain ⟨x, rfl⟩ := cechClass_surjective A N y
  obtain ⟨z, hz⟩ := CubeTop.topTerm_surjective A hN x.1
  exact ⟨z, congrArg (cechClass A N) (Subtype.ext hz)⟩
end GlobalTheory.ProjCoh
