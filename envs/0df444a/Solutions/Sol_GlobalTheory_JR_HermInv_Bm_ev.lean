-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.Bm_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:46.895467+00:00
-- url     : https://prove2.me/submissions/cf389f87-5fd6-46b2-8779-d4991f311edf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

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
theorem _root_.solution (Y : Gl r K) : Bm Y *ᵥ ev r K 0 = Y.2.1 := by
  funext i
  simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨0, i.pos⟩]
  · simp [Bm]
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp
end GlobalTheory.JR.HermInv
