-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.proj_of_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:13.594156+00:00
-- url     : https://prove2.me/submissions/036fe86d-276d-4760-bdb8-5b927addffb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_phi_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) {J K : Matrix n n B} (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (h2 : h * 2 = 1)
    (X : Matrix n n B) (hX : phi c J X = 0) : proj c J K h X = X := by
  unfold proj
  rw [(phi_eq_zero_iff c hJK hKJ X).1 hX, ← two_smul B X, smul_smul, h2, one_smul]
end GlobalTheory.EisBL.NilAlg
