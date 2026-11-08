-- Prove2me | solution 1 for OAI.SharpPlanar.bernsteinBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:11:22.838114+00:00
-- url     : https://prove2.me/submissions/1798c1ac-f4b7-4266-8110-a3122761af4b

import Mathlib
import Definitions.Def_OAIQ098G1643
import Definitions.Def_OAIQ098G1653
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals
open scoped BigOperators

lemma sumBox_contains {ι : Type*} [Fintype ι] {a : ι → RBox} {x : ι → ℝ}
    (ha : ∀ i, (a i).Contains (x i)) : (sumBox a).Contains (∑ i, x i) := by
  constructor
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).1)
  · simpa only [sumBox,Int.cast_sum,Finset.mul_sum] using Finset.sum_le_sum (fun i _ => (ha i).2)

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
open scoped BigOperators
lemma bernsteinBox_contains_g_oai {T : Fin 29 → RBox} {t : ℕ → ℝ}
    (hT : ∀ r : Fin 29,(T r).Contains (t r.val)) (k : Fin 29) :
    (bernsteinBox T k).Contains (powerToBernstein 28 t k.val) := by
  have hh := sumBox_contains (fun r : Fin (k.val+1) =>
    RBox.contains_scale_g (hT ⟨r.val,by omega⟩) (k.val.choose r.val) ((28).choose r.val)
      (by exact_mod_cast Nat.choose_pos (by omega : r.val≤28)))
  change (bernsteinBox T k).Contains _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold powerToBernstein
  simp only [Int.cast_natCast]
  change (∑ r ∈ Finset.range (k.val+1),_)=(∑ i : Fin (k.val+1), (k.val.choose i.val:ℝ)/(Nat.choose 28 i.val:ℝ)*t i.val)
  exact (Fin.sum_univ_eq_sum_range (fun r : ℕ => (k.val.choose r:ℝ)/(Nat.choose 28 r:ℝ)*t r) (k.val+1)).symm
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.bernsteinBox_contains_g_oai := @OAI.SharpPlanar.bernsteinBox_contains_g_oai
