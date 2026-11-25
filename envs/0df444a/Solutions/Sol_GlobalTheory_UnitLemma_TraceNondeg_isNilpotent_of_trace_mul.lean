-- Prove2me | solution 1 for GlobalTheory.UnitLemma.TraceNondeg.isNilpotent_of_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:54.075735+00:00
-- url     : https://prove2.me/submissions/f936037c-1135-4e11-9078-502d2d34bb46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isNilpotent_of_trace_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TraceNondeg
namespace GlobalTheory.UnitLemma.TraceNondeg
theorem _root_.solution {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by
  classical
  let b := Module.finBasis F A
  have hn : IsNilpotent (Algebra.leftMulMatrix b w) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact ⟨m, Algebra.leftMulMatrix_injective b hm⟩
end GlobalTheory.UnitLemma.TraceNondeg
