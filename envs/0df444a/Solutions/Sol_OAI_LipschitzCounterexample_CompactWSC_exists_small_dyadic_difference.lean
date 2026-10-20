-- Prove2me | solution 1 for OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:22:02.040168+00:00
-- url     : https://prove2.me/submissions/9baf4fbf-e3ae-4467-a3a8-9f06b0ed4fc0

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBlocks

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
universe uE uF uH
open scoped BigOperators
variable {E : Type uE} [AddCommGroup E] [Module ℝ E]
variable {F : Type uF} [AddCommGroup F] [Module ℝ F]


theorem solution (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) {C ε : ℝ} (_hε : 0 < ε) (d : ℕ) (hd : 4*C < (d : ℝ)*ε)
    (hu : ∀ k < 2^d, Q (u k) ≤ C) :
    ∃ n k, n < d ∧ k+2^(n+1) ≤ 2^d ∧
      Q (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε := by
  by_contra H
  push Not at H
  have key : ∀ n, n ≤ d → ∀ k, k + 2^n ≤ 2^d → Q (dyadicMean u n k) ≤ C - n * ε / 4 := by
    intro n
    induction n with
    | zero =>
      intro _ k hk
      simp only [dyadicMean_zero, Nat.cast_zero, zero_mul, zero_div, sub_zero]
      exact hu k (by simp at hk; omega)
    | succ n ih =>
      intro hn k hk
      have hp : 2^(n+1) = 2^n + 2^n := by ring
      have hk' := hk
      rw [hp] at hk'
      have hk1 : k + 2^n ≤ 2^d := le_trans (by rw [← add_assoc]; exact Nat.le_add_right _ _) hk'
      have hk2 : k + 2^n + 2^n ≤ 2^d := by rw [add_assoc]; exact hk'
      have h1 := ih (by omega) k hk1
      have h2 := ih (by omega) (k + 2^n) hk2
      have h3 := H n k (by omega) hk
      rw [dyadicMean_succ, hmid]
      push_cast
      linarith
  have := key d le_rfl 0 (by simp)
  have h0 := hQ (dyadicMean u d 0)
  nlinarith

