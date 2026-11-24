-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mulVec_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:47.641264+00:00
-- url     : https://prove2.me/submissions/6c74c9ab-8c93-4717-b048-23e0378168c5

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
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution {K : Type} [CommRing K] (M : Matrix (Fin r) (Fin r) K) (j : Fin r) :
    M *ᵥ ev r K j = fun i => M i j := by
  funext i
  simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp
end GlobalTheory.JR.HermInv
