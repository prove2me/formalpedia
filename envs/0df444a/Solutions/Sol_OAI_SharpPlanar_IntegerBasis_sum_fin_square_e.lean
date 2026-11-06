-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.sum_fin_square_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:06:19.759561+00:00
-- url     : https://prove2.me/submissions/c2b56e4a-9c2e-4e2f-9e54-821c691ee561

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis

lemma sum_fin_square_e_oai (N : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin N, ∑ k : Fin N, f (N*i.val+k.val)) =
      ∑ v : Fin (N*N), f v.val := by
  calc
    _ = ∑ x : Fin N × Fin N, f (N*x.1.val+x.2.val) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      convert (finProdFinEquiv.sum_comp (fun v : Fin (N*N) => f v.val)) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      exact Nat.add_comm _ _

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.sum_fin_square_e_oai := @OAI.SharpPlanar.IntegerBasis.sum_fin_square_e_oai
