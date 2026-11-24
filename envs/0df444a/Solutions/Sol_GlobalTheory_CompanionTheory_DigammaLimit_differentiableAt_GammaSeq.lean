-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.differentiableAt_GammaSeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:21.587334+00:00
-- url     : https://prove2.me/submissions/e1582ec4-b210-4fc1-a55a-16af27daf66c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_add_natCast_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hP : ∀ j ∈ Finset.range (n + 1), z + (j : ℂ) ≠ 0 := fun j _ => add_natCast_ne_zero hz j
  simp only [GammaSeq]
  refine DifferentiableAt.div ?_ ?_ (Finset.prod_ne_zero_iff.2 hP)
  · exact (differentiableAt_id.const_cpow (Or.inl hn')).mul_const _
  · exact DifferentiableAt.fun_finset_prod fun j _ => by fun_prop
end GlobalTheory.CompanionTheory.DigammaLimit
