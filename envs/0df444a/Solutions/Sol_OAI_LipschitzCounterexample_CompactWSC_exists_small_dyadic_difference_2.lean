-- Prove2me | solution 2 for OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:25:50.490115+00:00
-- url     : https://prove2.me/submissions/f9ee3333-e276-48b5-b2e8-ddc8ec02aa21

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/HilbertBlocks.lean:L76-L93
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.LipschitzEquivalence.HilbertBlocks ----
namespace OAI

universe uE uF uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

variable {E : Type uE} [AddCommGroup E] [Module ℝ E]

variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

theorem dyadic_energy_bound (Q : E → ℝ)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) (N : ℕ) (C ε : ℝ)
    (hu : ∀ k < N, Q (u k) ≤ C)
    (hgap : ∀ n k, k+2^(n+1) ≤ N →
      ε ≤ Q (dyadicMean u n k-dyadicMean u n (k+2^n)))
    (n k : ℕ) (hk : k+2^n ≤ N) :
    Q (dyadicMean u n k) ≤ C-(n : ℝ)*ε/4 := by
  induction n generalizing k with
  | zero => simpa using hu k (by simpa using hk)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ := ih k (by omega)
    have h₂ := ih (k+2^n) (by omega)
    have hg := hgap n k hk
    rw [dyadicMean_succ, hmid]
    push_cast
    linarith

theorem exists_small_dyadic_difference (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) {C ε : ℝ} (_hε : 0 < ε) (d : ℕ) (hd : 4*C < (d : ℝ)*ε)
    (hu : ∀ k < 2^d, Q (u k) ≤ C) :
    ∃ n k, n < d ∧ k+2^(n+1) ≤ 2^d ∧
      Q (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε := by
  by_contra! h
  have hgap : ∀ n k, k+2^(n+1) ≤ 2^d →
      ε ≤ Q (dyadicMean u n k-dyadicMean u n (k+2^n)) := by
    intro n k hk
    have hn : n < d := by
      have hp : 2^(n+1) ≤ 2^d := by omega
      have : n+1 ≤ d := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hp
      omega
    exact h n k hn hk
  have hb := dyadic_energy_bound Q hmid u (2^d) C ε hu hgap d 0 (by simp)
  have hnonneg := hQ (dyadicMean u d 0)
  linarith

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

end LipschitzCounterexample.CompactWSC
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.CompactWSC
open scoped BigOperators


theorem solution.{uE} : type_of% @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference.{uE} := @_root_.OAI.LipschitzCounterexample.CompactWSC.exists_small_dyadic_difference.{uE}
