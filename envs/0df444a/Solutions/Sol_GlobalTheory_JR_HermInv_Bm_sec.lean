-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.Bm_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:11.533368+00:00
-- url     : https://prove2.me/submissions/e8ca8ac9-e868-43c5-865e-80bfe86d70c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_pow_ev
import Theorems.Thm_GlobalTheory_JR_HermInv_sec_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (a : Inv r K) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, of_apply, sec_snd]
  rw [show (sec a).1 = companion a.1 from rfl, comp_pow_ev a.1 j j.2]
  simp [ev, one_apply, Fin.ext_iff, eq_comm]
end GlobalTheory.JR.HermInv
