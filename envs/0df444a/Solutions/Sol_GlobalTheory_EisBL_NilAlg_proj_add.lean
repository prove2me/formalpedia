-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.proj_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:07.909992+00:00
-- url     : https://prove2.me/submissions/be4359a9-f74d-4f7e-8194-deb360154c69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_add

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
theorem _root_.solution (c : B →+* B) (J K : Matrix n n B) (h : B) (X Y : Matrix n n B) :
    proj c J K h (X + Y) = proj c J K h X + proj c J K h Y := by
  unfold proj
  rw [tau_add, ← smul_add]
  congr 1
  abel
end GlobalTheory.EisBL.NilAlg
