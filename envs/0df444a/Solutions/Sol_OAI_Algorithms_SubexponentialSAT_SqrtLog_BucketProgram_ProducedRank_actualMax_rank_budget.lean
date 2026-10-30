-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:48:23.379354+00:00
-- url     : https://prove2.me/submissions/c1d48f7f-1250-4567-a94c-84cb63eb32d9

import Mathlib
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S054
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_ProducedRank_actualRank_sum_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank budget used by attained-signature counting.  The number of
serialized raw rows is deliberately absent: only their rational rank enters. -/
namespace SubexponentialSAT.SqrtLog.LayoutBudget

open scoped BigOperators

/-- Clear the exact rational spectral/packing budget without rounding rank. -/
theorem rank_budget_rat (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * (r : ℚ) * (L : ℚ)^2 * κ ≤ n := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hd : (0 : ℚ) < 32 * B * r * (L : ℚ)^2 := by positivity
  have hm : (M : ℚ) ≤ B * n := by exact_mod_cast hM
  have hdiv : (κ : ℚ) ≤ (2 * M) / (32 * B * r * (L : ℚ)^2) := by
    convert hκ using 1 ; push_cast ; ring
  have hmul := (le_div_iff₀ hd).mp hdiv
  have hc : (16 * (r : ℚ) * (L : ℚ)^2 * κ) * B ≤ (n : ℚ) * B := by
    nlinarith
  nlinarith

theorem rank_budget_nat (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * r * L^2 * κ ≤ n := by
  exact_mod_cast rank_budget_rat n M B r L κ hB hr hL hM hκ

theorem rank_budget_real (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * (r : ℝ) * (L : ℝ)^2 * κ ≤ n := by
  exact_mod_cast rank_budget_nat n M B r L κ hB hr hL hM hκ

/-- Direct interface from the sum of actual per-head ranks to the cost
assembly's real-valued premise, using the shared executable schedule. -/
theorem scheduled_total_rank_le_real {G : Type*} [Fintype G]
    (n M B : ℕ) (κ : G → ℕ) (hB : 0 < B) (hM : M ≤ B * n)
    (hκ : (∑ g, (κ g : ℚ)) ≤ 2 * Asymptotic.layoutEpsilon n B * M) :
    16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2 *
      (∑ g, (κ g : ℝ)) ≤ n := by
  have hr : 0 < Asymptotic.layoutR n := by
    have := Asymptotic.layoutR_ge_two n
    omega
  have hs : ((∑ g, κ g : ℕ) : ℚ) ≤
      2 * (1 / (32 * B * Asymptotic.layoutR n * Asymptotic.L n ^ 2 : ℕ) : ℚ) * M := by
    simpa only [Nat.cast_sum, Asymptotic.layoutEpsilon] using hκ
  simpa only [Nat.cast_sum] using
    rank_budget_real n M B (Asymptotic.layoutR n) (Asymptotic.L n)
      (∑ g, κ g) hB hr (Asymptotic.L_pos n) hM hs

end SubexponentialSAT.SqrtLog.LayoutBudget

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRankBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single proof-only rank parameter for finitely many nodes or queries.
The maximum is used only in the analysis of attained signatures; it does not
require a runtime row-basis computation or bound the number of stored rows. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

/-- A finite maximum preserves an exact real-valued rank budget. -/
theorem finite_rank_budget {X : Type*} (nodes : Finset X) (rank : X → ℕ)
    (a b : ℝ) (hb : 0 ≤ b)
    (h : ∀ x ∈ nodes, a * (rank x : ℝ) ≤ b) :
    a * ((nodes.sup rank : ℕ) : ℝ) ≤ b := by
  rcases nodes.eq_empty_or_nonempty with he | hn
  · simpa only [he, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero, mul_zero] using hb
  · obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup nodes hn rank
    rw [hmax]
    exact h x hx

/-- Node- or query-dependent masses and ranks may share one exact cost
parameter whenever every mass obeys the same scheduled budget. -/
theorem scheduled_maxTotalRank_le_real {X G : Type*} [Fintype G]
    (nodes : Finset X) (n B : ℕ) (mass : X → ℕ) (rank : X → G → ℕ)
    (hB : 0 < B) (hM : ∀ x ∈ nodes, mass x ≤ B * n)
    (hrank : ∀ x ∈ nodes, (∑ g, (rank x g : ℚ)) ≤
      2 * Asymptotic.layoutEpsilon n B * mass x) :
    16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2 *
      (maxTotalRank nodes rank : ℝ) ≤ n := by
  apply finite_rank_budget nodes (fun x => ∑ g, rank x g)
    (16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2) n (by positivity)
  intro x hx
  simpa only [Nat.cast_sum] using
    LayoutBudget.scheduled_total_rank_le_real n (mass x) B (rank x)
      hB (hM x hx) (hrank x hx)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual produced matrices, attained head tables and Cartesian inventory
share one proof-only maximum rank. Selection is in the emitted original-ID
order, and the canonical rank bound is discharged by literal pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LeafHeadSetupProgram

variable {r Q D n : ℕ}

/-- The finite maximum of the actual matrix ranks satisfies the scheduled
resource budget. It is independent of the full row count retained on tape. -/
theorem actualMax_rank_budget_oai {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (hselected : ∀ t∈nodes,∀ (g : Fin r) (v : Fin n),
      v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
    (m B : ℕ) (hB : 0 < B) (hD : D ≤ B*m)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < Asymptotic.layoutEpsilon m B)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (Asymptotic.layoutEpsilon m B:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-Asymptotic.layoutEpsilon m B)*(D:ℚ) ≤
      P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    16 * (Asymptotic.layoutR m : ℝ) * (Asymptotic.L m : ℝ)^2 *
      (CostAssembly.maxTotalRank nodes (actualRank P owner
        (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low) : ℝ) ≤ (m : ℝ) := by
  apply CostAssembly.scheduled_maxTotalRank_le_real nodes m B (fun _=>D)
    (actualRank P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low)
    hB (fun _ _=>hD)
  intro t ht
  exact actualRank_sum_le P owner head hhead R denom hdenom units t rows low
    (hselected t ht) (Asymptotic.layoutEpsilon m B) hr hQ hR hsize hε hwidth hcover

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget_oai.{u_1}
