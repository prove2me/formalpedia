-- Prove2me | solution 1 for GlobalTheory.JR.EtInv.eq_zero_of_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:01.158091+00:00
-- url     : https://prove2.me/submissions/eceb7f5c-e1a2-4864-8b12-90177f556523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isNilpotent_of_trace_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
variable {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K]
namespace GlobalTheory.JR.EtInv
theorem _root_.solution [CharZero F] [IsReduced K] (a : K)
    (h : ∀ x : K, Algebra.trace F K (x * a) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F K
  have hn : IsNilpotent (Algebra.leftMulMatrix b a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact (IsNilpotent.eq_zero ⟨m, Algebra.leftMulMatrix_injective b hm⟩)
end GlobalTheory.JR.EtInv
