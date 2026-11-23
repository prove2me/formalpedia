-- Prove2me | solution 1 for KernelRank.differentialOperator_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:07:19.918387+00:00
-- url     : https://prove2.me/submissions/905bfde2-6069-4648-903c-de225ab7e80e

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential

set_option autoImplicit true
open Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (q : ℂ[X]) {f g : ℝ → ℂ}
    (h : Set.EqOn f g (Set.Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator q f t = differentialOperator q g t := by
  unfold differentialOperator
  exact Finset.sum_congr rfl fun k _ => by rw [iteratedDerivWithin_congr h ht]
end KernelRank
