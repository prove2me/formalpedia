-- Prove2me | solution 1 for KernelRank.sum_update_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:14:13.185808+00:00
-- url     : https://prove2.me/submissions/623daf19-3977-4e99-8a04-14dbb10c24a1

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_sum_comp_update

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (i₀ : ι) (v : ℕ) :
    (∑ i, Function.update c i₀ v i) + c i₀ = (∑ i, c i) + v :=
  sum_comp_update (fun n => n) c i₀ v
end KernelRank
