-- Prove2me | solution 1 for GlobalTheory.CubeTop.topTerm_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:45.239796+00:00
-- url     : https://prove2.me/submissions/cdbcd19c-5a61-49a1-bec2-97832ba8f791

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
omit [LinearOrder ι]
namespace GlobalTheory.CubeTop
theorem _root_.solution (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    Function.Surjective (topTerm A hn) := by
  intro x
  refine ⟨x ⟨Finset.univ, hn⟩, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  exact Cube.res_self A _ _
end GlobalTheory.CubeTop
