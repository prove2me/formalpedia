-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.exterior_exterior_norm_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:24:16.788828+00:00
-- url     : https://prove2.me/submissions/fff97f64-474a-4772-b993-266647d3f2b6

import Mathlib
import Definitions.Def_OAIQ098G192
import Definitions.Def_OAIQ098G214
import Definitions.Def_OAIQ098G379
import Theorems.Thm_OAI_SharpPlanar_Numerical_exteriorIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_norm_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g
import Theorems.Thm_OAI_SharpPlanar_rowTable_bounds_g
import Theorems.Thm_OAI_SharpPlanar_sharp_S_tail_g
import Theorems.Thm_OAI_SharpPlanar_tailScalar_summable_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
lemma exteriorIndex_bound (i : Fin 48 × Fin 2) : 4 < (exteriorIndex i).1.val ∧ (exteriorIndex i).1.val ≤ 100 := by revert i; decide +kernel
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
lemma tailScalar_eq (x : X) (N : ℕ) : tailScalar x N = rowTailNorm x N := by
  unfold tailScalar rowTailNorm
  rw [(tailScalar_summable_g x N).tsum_prod]
  change _ = ∑' n : {n : Node // n ∈ {n : Node | N<n.val}}, (fun n : Node => |x (n,false)|+|x (n,true)|) n.val
  rw [tsum_subtype {n : Node | N<n.val} (fun n : Node => |x (n,false)|+|x (n,true)|)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp [add_comm]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_tail (N : ℕ) (hN : ∀ i, N<(e i).1.val) (x : X) :
    ‖finiteRestriction e he x‖ ≤ rowTailNorm x N := by
  rw [l1Finite_norm_g,← tailScalar_eq]
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable_g x N)
    (fun k => by split_ifs <;> positivity) he
  simpa only [Function.comp_apply, hN, ite_true, if_true, tsum_fintype,finiteRestriction_apply,tailScalar] using hh
end
end SharpPlanar
namespace SharpPlanar.Numerical
open scoped BigOperators
lemma exterior_exterior_norm_g_oai : ‖RE.comp (S.comp IE)‖ ≤ (28:ℝ)/100 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have h := finiteRestriction_tail exteriorIndex exteriorIndex_injective_g 4
    (fun i => (exteriorIndex_bound i).1) (S (IE x))
  have ht := sharp_S_tail_g (IE x) 4
  rw [finiteEmbedding_norm_g _ exteriorIndex_injective_g] at ht
  exact h.trans (ht.trans (mul_le_mul_of_nonneg_right rowTable_bounds_g.2.1.le (norm_nonneg _)))
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.exterior_exterior_norm_g_oai := @OAI.SharpPlanar.Numerical.exterior_exterior_norm_g_oai
