-- Prove2me | solution 1 for OAI.SevenEighths.PNT.prime_residueClass_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:48.318031+00:00
-- url     : https://prove2.me/submissions/8541d7aa-d3bb-4856-bdb4-67b56da5efeb

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_PrimeMass
import Theorems.Thm_OAI_SevenEighths_PNT_retained_ratio_tendsto
import Theorems.Thm_OAI_SevenEighths_PNT_residueClass_ratio_tendsto


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.PNT
open Filter ArithmeticFunction
open scoped Topology BigOperators
namespace OAI.SevenEighths.PNT
theorem _root_.solution {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      cumsum (fun n => if n.Prime then vonMangoldt.residueClass a n else 0) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) :=
  retained_ratio_tendsto Nat.Prime (vonMangoldt.residueClass_nonneg a)
    (vonMangoldt.residueClass_apply_zero a) (residueClass_ratio_tendsto a ha)
    (vonMangoldt.summable_residueClass_non_primes_div a)
end OAI.SevenEighths.PNT
