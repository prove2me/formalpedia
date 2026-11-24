-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.chainUnion_remove_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:41.906729+00:00
-- url     : https://prove2.me/submissions/9c00d2d0-d8d3-4c91-bfa5-1710718c6d20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (m k t : ℕ) (q : Fin m) (hq : (q : ℕ) = t + 1) :
    (fun i j => chainUnion m k t i j ∧ ¬ (Sum.isRight i = true ∧ j = Sum.inl q)) =
      chainPat m k (t + 1) := by
  funext i j
  apply propext
  rcases i with a | w <;> rcases j with b | v <;>
    simp only [chainUnion, chainPat, Fin.lt_def, Sum.isRight_inl, Sum.isRight_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Bool.false_eq_true, false_and, and_false, true_and, and_true,
      not_false_eq_true, Fin.ext_iff] <;> omega
end GlobalTheory.CompanionTheory.TyFin
