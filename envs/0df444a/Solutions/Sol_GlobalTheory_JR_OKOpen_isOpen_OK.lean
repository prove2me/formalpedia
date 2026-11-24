-- Prove2me | solution 1 for GlobalTheory.JR.OKOpen.isOpen_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:31:09.79829+00:00
-- url     : https://prove2.me/submissions/582584ef-5bcc-4742-ad03-2573dbe0ae33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsOpenFiniteEtaleHermitianPairOK
import Theorems.Thm_GlobalTheory_JR_OKOpen_continuous_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKOpen
namespace GlobalTheory.JR.OKOpen
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  have hset : A.OK = ⋂ i : Fin (Module.finrank F A.K + 1),
      (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Et.OK, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h i; exact h i
    · intro h i
      by_cases hi : i ≤ Module.finrank F A.K
      · exact h ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
        simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (continuous_coeff A i)
end GlobalTheory.JR.OKOpen
