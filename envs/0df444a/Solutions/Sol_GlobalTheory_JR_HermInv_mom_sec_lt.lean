-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mom_sec_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:04.260456+00:00
-- url     : https://prove2.me/submissions/c4c2079e-44e6-4a4b-b76f-743e68cc2b8c

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
theorem _root_.solution (a : Inv r K) (i : Fin r) : mom (sec a) i = a.2.1 i := by
  simp only [mom]
  rw [show (sec a).1 = companion a.1 from rfl, sec_snd, comp_pow_ev a.1 i i.2]
  simp only [dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp [show (sec a).2.2.1 = a.2.1 from rfl]
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp
end GlobalTheory.JR.HermInv
