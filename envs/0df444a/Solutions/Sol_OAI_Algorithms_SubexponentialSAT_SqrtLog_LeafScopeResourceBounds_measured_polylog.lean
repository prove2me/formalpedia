-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:53:52.969888+00:00
-- url     : https://prove2.me/submissions/6049ed52-c364-4423-9eb9-8d8287a3e72d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S075

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

/-- Sparse clauses have only logarithmic binary length. The upper bound here
is intentionally elementary; it is enough for the linear precision budget. -/
theorem sparse_clause_size_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    Nat.size m ≤ (q+1)*L n+1 := by
  have hn : n ≤ 2^L n := by
    have hh : n+16 < 2^L n := by simpa [L] using (Nat.lt_log2_self (n:=n+16))
    omega
  have hL : L n ≤ 2^L n := (Nat.lt_two_pow_self).le
  have hpow : m ≤ 2^((q+1)*L n) := by
    calc
      m ≤ n*B := hm
      _ ≤ 2^L n*(2^L n)^q := Nat.mul_le_mul hn (hB.trans (Nat.pow_le_pow_left hL q))
      _ = 2^((q+1)*L n) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  apply Nat.size_le.mpr
  exact hpow.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open Asymptotic

theorem code_logSize_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.logSize m ≤ (q+2)*L n := by
  have hL : 1 ≤ L n := L_pos n
  by_cases hz : m=0
  · subst m
    simp only [SparseCode.logSize, Nat.log_zero_right, zero_add]
    nlinarith
  have hs := sparse_clause_size_le n m B q hm hB
  have he : SparseCode.logSize m=Nat.size m := by
    rw [LeafParametersProgram.size_eq_log2_add_one hz]
    simp [SparseCode.logSize, Nat.log2_eq_log_two]
  rw [he]
  nlinarith

theorem code_distanceDenom_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.distanceDenom m B ≤ 20000*(q+2)^2*L n^(2*q+2) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.distanceDenom
  calc
    _ ≤ 20000*(L n^q)^2*((q+2)*L n)^2 := by gcongr
    _ = _ := by ring

theorem code_degreeBound_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.degreeBound m B ≤ 320000*(q+2)^3*L n^(2*q+3) := by
  have hl := code_logSize_le n m B q hm hB
  unfold SparseCode.degreeBound SparseCode.gapDenom
  calc
    _ ≤ 8*(200*(L n^q)*((q+2)*L n))^2*((q+2)*L n) := by gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem occurrence_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).occurrence =
      Finset.univ.sup (Incidence.degree (completedScope scopes mask)) := by
  apply Nat.le_antisymm
  · rw [totals_occurrence_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i hi
    simp only [List.get_eq_getElem] at hi
    let v : Free mask := ⟨i, by simp [hi]⟩
    simpa only [Nat.zero_add, completed_degree] using
      (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v))
  · apply Finset.sup_le
    intro v _
    have h := (totals_occurrence_le_iff scopes 0 mask zero
      (variableTotals scopes 0 mask zero).occurrence).mp le_rfl
    simpa only [Nat.zero_add, completed_degree] using h.2 v.val (free_bit mask v)

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem arity_le_iff (mask : List Bool) (scopes : List (List ℕ)) (a b : ℕ) :
    Arity.arity mask scopes a ≤ b ↔
      a ≤ b ∧ ∀ row ∈ scopes, (row.filter (Scope.low mask)).length ≤ b := by
  induction scopes generalizing a with
  | nil => simp [Arity.arity]
  | cons row rows ih =>
    change Arity.arity mask rows (max (row.filter (Scope.low mask)).length a) ≤ b ↔ _
    rw [ih]
    simp [ and_assoc, and_comm]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsStatistics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Upper bounds for the actual measured statistics. The mask is the forward
reverse of the physical descending high-prefix stream. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram LeafStatisticsSemantics

theorem forwardMask_get (scopes : List (List ℕ)) (cut n : ℕ)
    (i : Fin (forwardMask scopes cut n).length) :
    (forwardMask scopes cut n).get i = decide (cut < degree scopes i.val) := by
  simp only [forwardMask, HighIncidenceProgram.Order.highPrefix_range,
    ← List.map_reverse, List.reverse_reverse, List.get_eq_getElem,
    List.getElem_map, List.getElem_range]

theorem measured_occurrence_le (scopes : List (List ℕ)) (cut n : ℕ) :
    (measured scopes (forwardMask scopes cut n)).occurrence ≤ max 1 cut := by
  rw [measured, occurrence_exact]
  apply Finset.sup_le
  intro v _
  rw [completed_degree]
  apply max_le_max_left
  have h := free_bit (forwardMask scopes cut n) v
  rw [forwardMask_get] at h
  simpa using h

theorem measured_arity_le (scopes : List (List ℕ)) (mask : List Bool) (A : ℕ)
    (ha : ∀ row ∈ scopes, row.length ≤ A) :
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered = 0 then 0 else 1) ≤ max A 1 := by
  apply max_le
  · apply le_trans _ (le_max_left A 1)
    apply (arity_le_iff mask scopes 0 A).mpr
    exact ⟨Nat.zero_le _, fun row hr => (List.length_filter_le _ _).trans (ha row hr)⟩
  · split_ifs <;> omega

theorem cut_le_of_mass (scopes : List (List ℕ)) (nb tb : List Bool) (C : ℕ)
    (hn : 0 < BinaryArithmetic.toNat nb)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤ BinaryArithmetic.toNat nb * C) :
    HighIncidenceProgram.Prepare.cut scopes nb tb ≤ C * BinaryArithmetic.toNat tb := by
  apply (ceilDiv_le_iff_le_mul hn).mpr
  calc
    _ ≤ (BinaryArithmetic.toNat nb * C) * BinaryArithmetic.toNat tb := Nat.mul_le_mul_right _ hS
    _ = _ := by ring

theorem measured_occurrence_of_mass (scopes : List (List ℕ)) (nb tb : List Bool) (C : ℕ)
    (hn : 0 < BinaryArithmetic.toNat nb)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤ BinaryArithmetic.toNat nb * C) :
    (measured scopes (forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb)
      (BinaryArithmetic.toNat nb))).occurrence ≤ max 1 (C * BinaryArithmetic.toNat tb) :=
  (measured_occurrence_le _ _ _).trans (max_le_max_left 1 (cut_le_of_mass scopes nb tb C hn hS))

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsPolylog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit, pointwise polylogarithmic resource envelopes. No sequence of
matrices is chosen before the ambient cutoff: all raw scope tables satisfying
the concrete slot budget share these same constants. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic LeafStatisticsProgram

theorem code_bounds (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.degreeBound m B ≤ slotCoefficient q * L n^(2*q+3) ∧
    SparseCode.distanceDenom m B ≤ slotCoefficient q * L n^(2*q+3) := by
  constructor
  · exact (CostAssembly.code_degreeBound_le n m B q hm hB).trans
      (Nat.mul_le_mul_right _ (by dsimp [slotCoefficient]; omega))
  · apply (CostAssembly.code_distanceDenom_le n m B q hm hB).trans
    apply Nat.mul_le_mul
    · dsimp [slotCoefficient]; omega
    · exact Nat.pow_le_pow_right (L_pos n) (by omega)

theorem raw_mass_polylog (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
    (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n) (S : ℕ)
    (hS : S ≤ (3*n*SparseCode.degreeBound m B +
      (HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k) :
    S ≤ n * (massCoefficient k q * L n^(2*q+3)) := by
  obtain ⟨hD,hP⟩ := code_bounds n m B q hm hB
  have hK : HashSelect.loopCap n m+1 ≤ 7*n := by
    dsimp [HashSelect.loopCap]; omega
  have hU : 1 ≤ slotCoefficient q * L n^(2*q+3) := by
    have hpow := Nat.one_le_pow (2*q+3) (L n) (L_pos n)
    have hc : 1 ≤ slotCoefficient q := by dsimp [slotCoefficient]; omega
    nlinarith
  calc
    S ≤ (3*n*SparseCode.degreeBound m B +
      (HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k := hS
    _ ≤ (3*n*(slotCoefficient q*L n^(2*q+3)) +
      (7*n)*(slotCoefficient q*L n^(2*q+3))+n*(slotCoefficient q*L n^(2*q+3)))*k := by
        apply Nat.mul_le_mul_right
        apply Nat.add_le_add
        · exact Nat.add_le_add (Nat.mul_le_mul_left _ hD) (Nat.mul_le_mul hK hP)
        · nlinarith
    _ ≤ n * (massCoefficient k q * L n^(2*q+3)) := by
      dsimp [massCoefficient]
      nlinarith only [Nat.zero_le (n*(slotCoefficient q*L n^(2*q+3)))]

theorem raw_arity_polylog (n m B k q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q)
    (A : ℕ) (hA : A ≤ (SparseCode.degreeBound m B + SparseCode.distanceDenom m B+1)*k) :
    A ≤ massCoefficient k q * L n^(2*q+3) := by
  obtain ⟨hD,hP⟩ := code_bounds n m B q hm hB
  have hpow := Nat.one_le_pow (2*q+3) (L n) (L_pos n)
  have hc : 1 ≤ slotCoefficient q := by dsimp [slotCoefficient]; omega
  have hU : 1 ≤ slotCoefficient q * L n^(2*q+3) := by nlinarith
  calc
    A ≤ (SparseCode.degreeBound m B + SparseCode.distanceDenom m B+1)*k := hA
    _ ≤ (3*(slotCoefficient q*L n^(2*q+3)))*k := by
      apply Nat.mul_le_mul_right
      omega
    _ ≤ massCoefficient k q * L n^(2*q+3) := by
      dsimp [massCoefficient]
      nlinarith only [Nat.zero_le (slotCoefficient q*L n^(2*q+3)),
        Nat.zero_le (k*(slotCoefficient q*L n^(2*q+3)))]

/-- Both native statistics have a common fixed envelope, including the neutral
singleton factors. `nb` and `tb` are the actual binary Prepare inputs. -/
theorem measured_polylog_oai (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
    (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n)
    (scopes : List (List ℕ)) (nb tb : List Bool)
    (hnb : BinaryArithmetic.toNat nb = n)
    (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤
      (3*n*SparseCode.degreeBound m B+(HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k)
    (hA : ∀ row ∈ scopes, row.length ≤ (SparseCode.degreeBound m B+SparseCode.distanceDenom m B+1)*k) :
    let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
    (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
      statCoefficient k q * L n^resourceExponent q := by
  have hs := raw_mass_polylog n m B k q hn hm hB hsize _ hS
  have ha := fun row hr => raw_arity_polylog n m B k q hm hB row.length (hA row hr)
  have hp : 1 ≤ L n^(2*q+3) := Nat.one_le_pow _ _ (L_pos n)
  have hl : 1 ≤ L n := L_pos n
  have hc : 1 ≤ massCoefficient k q := by
    change 0 < massCoefficient k q
    dsimp [massCoefficient, slotCoefficient]
    positivity
  have ht : Nat.sqrt (L n)+1 ≤ 2*L n := by have := Nat.sqrt_le_self (L n); omega
  have hpow : L n^resourceExponent q = L n^(2*q+3) * L n := by
    unfold resourceExponent
    convert pow_succ (L n) (2*q+3) using 1
    all_goals try with_reducible_and_instances rfl
  have hone : 1 ≤ statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    change 0 < statCoefficient k q * (L n^(2*q+3)*L n)
    dsimp [statCoefficient]
    positivity
  have hout : (massCoefficient k q * L n^(2*q+3)) * (Nat.sqrt (L n)+1) ≤
      statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    calc
      _ ≤ (massCoefficient k q * L n^(2*q+3)) * (2*L n) := Nat.mul_le_mul_left _ ht
      _ ≤ _ := by dsimp [statCoefficient]; nlinarith only [Nat.zero_le (L n^(2*q+3)*L n)]
  have hsmall : massCoefficient k q * L n^(2*q+3) ≤ statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    calc
      _ ≤ (massCoefficient k q * L n^(2*q+3))*L n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (massCoefficient k q * L n^(2*q+3)) hl
      _ = massCoefficient k q * (L n^(2*q+3)*L n) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [statCoefficient]; omega)
  constructor
  · have hh := measured_occurrence_of_mass scopes nb tb
      (massCoefficient k q * L n^(2*q+3)) (by simpa [hnb] using hn) (by simpa [hnb] using hs)
    rw [hnb,htb] at hh
    exact hh.trans (max_le hone hout)
  · exact (measured_arity_le scopes _ _ ha).trans (max_le hsmall hone)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.measured_polylog_oai
