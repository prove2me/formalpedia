-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.part2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:15.776557+00:00
-- url     : https://prove2.me/submissions/1b002b2b-7a7b-4716-95b7-e684230e4638

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff
import Theorems.Thm_GlobalTheory_JR_HermInv_charpoly_actU
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_actU

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
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    HasInv (actU g X) a := by
  obtain ⟨h1, h2, h3⟩ := (hasInv_iff X a).1 h
  exact (hasInv_iff _ a).2 ⟨fun i => by rw [charpoly_actU]; exact h1 i, fun i => by rw [mom_actU]; exact h2 i, h3⟩
end GlobalTheory.JR.HermInv
