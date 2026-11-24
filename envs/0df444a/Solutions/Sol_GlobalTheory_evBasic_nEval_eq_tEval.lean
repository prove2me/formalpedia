-- Prove2me | solution 1 for GlobalTheory.evBasic_nEval_eq_tEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:31.916417+00:00
-- url     : https://prove2.me/submissions/c459b6bc-e955-4ca4-8c8c-0b8237d0d853

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Theorems.Thm_GlobalTheory_evBasic_tEval_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
variable {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : Type} [CommRing S] [Algebra R₀ S]
namespace GlobalTheory
theorem _root_.solution (f : MvPowerSeries ι R₀) (a : ι → S) (N : ℕ)
    (ha : ∀ i, a i ^ N = 0) : nEval f a = tEval N f a := by
  classical
  unfold nEval
  split_ifs with h
  · exact evBasic_tEval_indep f a (Nat.find_spec h) ha
  · exact absurd ⟨N, ha⟩ h
end GlobalTheory
