-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:13.418959+00:00
-- url     : https://prove2.me/submissions/3e103686-aca5-4584-8fe5-b994fb7896b8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_deriv_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution :
    ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
      ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) →
      (∀ p, DifferentiableOn ℂ (H p) U) →
        ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U) := by
  intro P _ U hU H hc hd r
  have hdiff : ∀ (r : ℕ) (p : P), DifferentiableOn ℂ (iteratedDeriv r (H p)) U := by
    intro r p
    induction r with
    | zero => simpa [iteratedDeriv_zero] using hd p
    | succ r ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  induction r with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ r ih =>
    simp only [iteratedDeriv_succ]
    exact continuousOn_deriv_family P U hU (fun p => iteratedDeriv r (H p)) ih (hdiff r)
end GlobalTheory.CompanionTheory.HolFamily
