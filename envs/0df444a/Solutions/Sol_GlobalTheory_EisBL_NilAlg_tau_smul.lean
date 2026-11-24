-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.tau_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:44.946431+00:00
-- url     : https://prove2.me/submissions/cda1a639-6221-421f-9271-695d62d4707c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

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
omit [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (J K : Matrix n n B) (h : B) (hh : c h = h) (X : Matrix n n B) :
    tau c J K (h • X) = h • tau c J K X := by
  unfold tau
  have : (h • X).map c = h • X.map c := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hh]
  rw [this, Matrix.mul_smul, Matrix.smul_mul, transpose_smul, smul_neg]
end GlobalTheory.EisBL.NilAlg
