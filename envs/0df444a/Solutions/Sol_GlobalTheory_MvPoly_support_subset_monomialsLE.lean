-- Prove2me | solution 1 for GlobalTheory.MvPoly.support_subset_monomialsLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:55.456259+00:00
-- url     : https://prove2.me/submissions/e4b4dd1f-650f-49b2-806f-b106258ce4e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_degree_le_totalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [Fintype σ] [DecidableEq σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ} :
    P.support ⊆ monomialsLE σ d ↔ P.totalDegree ≤ d :=
  ⟨fun h ↦ Finset.sup_le fun _ hα ↦ mem_monomialsLE.mp (h hα),
    fun h _ hα ↦ mem_monomialsLE.mpr ((degree_le_totalDegree hα).trans h)⟩
end GlobalTheory.MvPoly
