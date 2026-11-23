-- Prove2me | solution 1 for GlobalTheory.germIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:56.627797+00:00
-- url     : https://prove2.me/submissions/0bf42f0b-4fa9-47ce-9bc1-8b602777a916

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_X_mem_germIdeal
import Theorems.Thm_GlobalTheory_exists_eq_sum_X_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] GlobalTheory.constDerivEval_X

set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  cases nonempty_fintype σ
  refine le_antisymm (fun g hg => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨h, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => by
      obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
      simpa using hg
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact X_mem_germIdeal i
end GlobalTheory
