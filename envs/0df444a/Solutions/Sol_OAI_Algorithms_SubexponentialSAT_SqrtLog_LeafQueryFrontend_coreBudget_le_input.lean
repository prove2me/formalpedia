-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget_le_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:05:33.659007+00:00
-- url     : https://prove2.me/submissions/8d3fffd1-9249-4d4e-bbe5-3b0a4674aa29

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S183

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CoreMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Applying a runtime mask to an encoded clause

The mask and clause occupy separate Boolean stacks.  Selection consumes one
mask bit per literal, treating a missing bit as false and leaving excess mask
bits unread.  Payloads are copied as framed bit strings without interpreting
their contents.
-/

namespace SubexponentialSAT.CoreMaskProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram

theorem selected_encoded_length_le (mask : List Bool) (records : List (List Bool)) :
    (Encoding.encodeList id (select mask records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records generalizing mask with
  | nil => simp [select]
  | cons item rest ih =>
      simp only [select]
      split
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left (ih mask.tail) (2 * item.length + 2)
      · exact (ih mask.tail).trans (by rw [Encoding.length_encodeList_cons]; omega)

end SubexponentialSAT.CoreMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

theorem indexPrefix_length_le (js : List ℕ) (E : ℕ) (h : ∀ j ∈ js, j < E) :
    (indexPrefix js).length ≤ js.length*(2*E+2) := by
  induction js with
  | nil => simp [indexPrefix]
  | cons j js ih =>
      have hj := h j (by simp)
      have ht := ih (fun k hk => h k (by simp [hk]))
      simp [indexPrefix,Encoding.length_frame] at ht ⊢
      nlinarith

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

theorem encode_map (scopes : List (List ℕ)) :
    Encoding.encodeList id (scopes.map scopeBytes) = scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons C Cs ih =>
      simpa [scopeBits, Encoding.encodeList] using
        congrArg (fun tail => true :: (Encoding.frame (scopeBytes C) ++ tail)) ih

theorem select_prefix (records : List (List Bool)) (e : ℕ) :
    CoreMaskProgram.select (unary e) records = records.take e := by
  induction records generalizing e with
  | nil => simp [CoreMaskProgram.select]
  | cons x xs ih =>
      cases e with
      | zero => simpa [CoreMaskProgram.select, unary] using ih 0
      | succ e => simp [CoreMaskProgram.select, unary, List.replicate_succ, ih]

theorem prefix_length_le (scopes : List (List ℕ)) (e : ℕ) :
    (scopeBits (scopes.take e)).length ≤ (scopeBits scopes).length := by
  have h := CoreMaskProgram.selected_encoded_length_le (unary e) (scopes.map scopeBytes)
  simpa only [select_prefix, ← List.map_take, encode_map] using h

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Serialized scope adapter and complete bit cost for the nested counter.
The counter counts supplied entries; the caller's normalization invariant is
what identifies this with distinct factor-variable incidence mass. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem encode_map_nat (xs : List ℕ) :
    encode (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, encode, Encoding.encodeList, id_eq, ih]

theorem encoded_scopeRecords (scopes : List (List ℕ)) :
    encode ((scopeRecords scopes).map encode) = SubexpIncidenceSlotProgram.scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons xs xss ih =>
      simpa only [scopeRecords, List.map_cons, encode, Encoding.encodeList,
        id_eq, encode_map_nat, SubexpIncidenceSlotProgram.scopeBits,
        SubexpIncidenceSlotProgram.scopeBytes, SubexpIncidencePlanScan.scopeBytes] using
        congrArg (fun tail => true :: (Encoding.frame
          (Encoding.encodeList Encoding.encodeNat xs) ++ tail)) ih

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls
open Subexp.IncidencePlanSpec

theorem indices_length_le (scopes : List (List ℕ)) (e v : ℕ) :
    (indices scopes e v).length ≤ e * (2 * e + 2) := by
  have hp : (scopes.take e).length ≤ e := List.length_take_le e scopes
  have hi := SubexpIncidencePlanScan.indexPrefix_length_le
    (incidenceFrom v 0 (scopes.take e)).reverse e (by
      intro j hj
      have h := incidenceFrom_bounds v 0 j (scopes.take e) (by simpa using hj)
      omega)
  have hc := SubexpIncidencePlanScan.incidenceFrom_length_le v 0 (scopes.take e)
  simp only [List.length_reverse] at hi
  exact hi.trans (Nat.mul_le_mul_right _ (hc.trans hp))

theorem budget_le (scopes : List (List ℕ)) (e v B : ℕ)
    (hl : (scopeBits scopes).length ≤ B) (he : e ≤ B) (hv : v ≤ B) :
    budget scopes e v ≤ 1000 * (B + 1)^2 := by
  have hp : (scopes.take e).length ≤ B := (List.length_take_le e scopes).trans he
  have hlen := (prefix_length_le scopes e).trans hl
  have hs := SubexpIncidencePlanScan.scanBudget_le v 0 (scopes.take e)
  have hs' : SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) ≤
      (144 * B + 308) * B := hs.trans (Nat.mul_le_mul (by omega) hlen)
  have hi := (indices_length_le scopes e v).trans
    (Nat.mul_le_mul he (by omega : 2 * e + 2 ≤ 2 * B + 2))
  dsimp [budget]
  nlinarith

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] query count compare
  SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

theorem queryBudget_le (scopes : List (List ℕ)) (n cut v : ℕ) (hv : v ≤ n) :
    queryBudget scopes v cut ≤ uniformQueryBudget scopes n cut := by
  have hb := SubexpIncidenceSlotProgram.budget_le scopes scopes.length v
    ((scopeBits scopes).length + scopes.length + n)
    (by change (scopeBits scopes).length ≤ _; omega) (by omega) (by omega)
  have hd : degree scopes v ≤ scopes.length := by
    simpa only [degree, Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices] using
      SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
  dsimp [queryBudget, uniformQueryBudget]
  omega


theorem scanBudget_le (scopes : List (List ℕ)) (n cut : ℕ) :
    scanBudget scopes n cut + 1 ≤ n * (uniformQueryBudget scopes n cut + 2) + 3 := by
  have h := CounterForPrograms.budgetSum_le (fun i => queryBudget scopes i cut)
    0 n (uniformQueryBudget scopes n cut) (by
      intro i hi hlt
      exact queryBudget_le scopes n cut i (by omega))
  dsimp [scanBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem records_bits (scopes : List (List ℕ)) :
    Encoding.encodeList id (records scopes) = scopeBits scopes :=
  Mass.encoded_scopeRecords scopes

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed polynomial cost and dimension bound for the complete prefix.
The bound is polynomial in encoded scope length, numeric ambient n and t,
and the lengths of their binary input words; it does not assume precomputed
statistics or claim polynomiality solely in the binary lengths of n,t. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem mass_le_input (scopes : List (List ℕ)) : mass scopes ≤ (scopeBits scopes).length := by
  induction scopes with
  | nil => simp [mass, scopeBits, SubexpIncidenceSlotProgram.scopeBits, Encoding.encodeList]
  | cons xs xss ih =>
      have hx := Encoding.length_encodeList_lower Encoding.encodeNat xs
      simp only [mass, List.map_cons, List.sum_cons] at *
      change xs.length + (xss.map List.length).sum ≤
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (xs :: xss)).length
      rw [Encoding.length_encodeList_cons]
      change (xss.map List.length).sum ≤
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xss).length at ih
      omega

theorem count_le_input (scopes : List (List ℕ)) : scopes.length ≤ (scopeBits scopes).length := by
  exact (Nat.le_succ _).trans (Encoding.length_encodeList_lower _ _)

theorem capacity_le_input (scopes : List (List ℕ)) (n t : List Bool) :
    capacity scopes n t ≤ 3 * inputCapacity scopes n t := by
  have := mass_le_input scopes
  have := count_le_input scopes
  dsimp [capacity, inputCapacity]
  omega

theorem cut_le_product (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    cut scopes n t ≤ mass scopes * BinaryArithmetic.toNat t := by
  apply (ceilDiv_le_iff_le_mul hn).mpr
  have h := Nat.le_mul_of_pos_left (mass scopes * BinaryArithmetic.toNat t) hn
  simpa [Nat.mul_comm] using h

theorem unarySized_le (value size R : ℕ) (hR : 2 ≤ R) (hv : value ≤ R^2) (hs : size ≤ R) :
    unarySized value size ≤ 100 * R^3 := by
  have h := Nat.mul_le_mul (Nat.add_le_add_right hv 1) (Nat.add_le_add_right hs 1)
  have hsq : 2 * R ≤ R^2 := by nlinarith only [hR]
  have hcube : 2 * R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  dsimp [unarySized]
  nlinarith only [h, hR, hsq, hcube]

theorem budget_le (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    budget scopes n t + 1 ≤ 10000 * (capacity scopes n t)^3 := by
  let R := capacity scopes n t
  have hR : 2 ≤ R := by dsimp [R, capacity]; omega
  have hs : mass scopes ≤ R := by dsimp [R, capacity]; omega
  have he : scopes.length ≤ R := by dsimp [R, capacity]; omega
  have hnR : BinaryArithmetic.toNat n ≤ R := by dsimp [R, capacity]; omega
  have htR : BinaryArithmetic.toNat t ≤ R := by dsimp [R, capacity]; omega
  have hsum : (scopeBits scopes).length + scopes.length + BinaryArithmetic.toNat n + 1 ≤ R := by dsimp [R, capacity]; omega
  have hsize : mass scopes + t.length + n.length + 2 ≤ R := by dsimp [R, capacity]; omega
  have hinput : (scopeBits scopes).length + 1 ≤ R := by dsimp [R, capacity]; omega
  have hq : cut scopes n t ≤ R^2 := (cut_le_product scopes n t hn).trans (by
    simpa [pow_two] using Nat.mul_le_mul hs htR)
  have hsq : R ≤ R^2 := by nlinarith only [hR]
  have hcube : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  have hcount : SubexpScopeCountSetup.countBudget (records scopes) + 1 ≤ 14 * R := by
    have hc := SubexpSunflowerProgram.CountRecords.steps_le_encoded (records scopes)
    rw [records_bits] at hc
    dsimp [SubexpScopeCountSetup.countBudget, SubexpSunflowerProgram.CountRecords.steps]
    rw [records_bits]
    dsimp [SubexpSunflowerProgram.CountRecords.steps] at hc
    omega
  have hmass : MassPreserve.bound (scopeBits scopes) ≤ 40 * R := by
    dsimp [MassPreserve.bound]; omega
  have hbin : SubexpFactorCountSetup.countBudget (mass scopes) + 1 ≤ 30 * R^2 := by
    have hs2 := Nat.mul_self_le_mul_self hs
    dsimp [SubexpFactorCountSetup.countBudget]
    nlinarith only [hs2, hs, hsq, hR]
  have hcut : Cutoff.bound (List.replicate (mass scopes) false) t n ≤ 601 * R^2 := by
    have ha : mass scopes + t.length + 1 ≤ R := by omega
    have hb := Nat.pow_le_pow_left hsize 2
    have hc := Nat.pow_le_pow_left ha 2
    dsimp [Cutoff.bound]
    simp only [List.length_replicate]
    nlinarith only [hb, hc, hR]
  have hu : unarySized (cut scopes n t) (mass scopes + t.length + 2) ≤ 100 * R^3 :=
    unarySized_le _ _ _ hR hq (by omega)
  have hf : unarySized (BinaryArithmetic.toNat n) n.length ≤ 100 * R^3 :=
    unarySized_le _ _ _ hR (hnR.trans hsq) (by omega)
  have hquery : uniformQueryBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 2 ≤ 1100 * R^2 := by
    have hb := Nat.pow_le_pow_left hsum 2
    dsimp [uniformQueryBudget]
    nlinarith only [hb, hq, he, hsq, hR]
  have hscan : scanBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 1 ≤ 1100 * R^3 + 3 := by
    apply (scanBudget_le scopes (BinaryArithmetic.toNat n) (cut scopes n t)).trans
    have h := Nat.mul_le_mul hnR hquery
    nlinarith only [h]
  dsimp [budget]
  nlinarith only [hcount, hmass, hbin, hcut, hu, hf, hscan, hsq, hcube, hR]

theorem input_budget (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    budget scopes n t + 1 ≤ 270000 * (inputCapacity scopes n t)^3 := by
  apply (budget_le scopes n t hn).trans
  have h := Nat.pow_le_pow_left (capacity_le_input scopes n t) 3
  nlinarith

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem scopeCopies_cost (q : Query) (a : Data) (ha : q.Ready a) :
    copiesCost scopeCopies a=q.scopeCopyBudget := by
  rcases ha with ⟨h700,h701,h705,h706,h707,h708,h709,hz,h338,h718,h719⟩
  simp [copiesCost,scopeCopies,copied_stack,Query.scopeCopyBudget,h700,h701,h705,h706,h707,h708]

theorem coreBudget_le_input_oai (q : Query) (k : ℕ) (a : Data) (ha : q.Ready a)
    (hn : 0 < BinaryArithmetic.toNat q.ambient) (tau : List Bool)
    (ht : BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient))
    (hl : tau.length ≤ Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1) :
    coreBudget q k a tau (q.inputLengths k) ≤ q.coreInputBudget k := by
  have hc : HighIncidenceProgram.Prepare.inputCapacity q.scopeRows q.ambient tau ≤ q.highCapacity := by
    dsimp [HighIncidenceProgram.Prepare.inputCapacity,Query.highCapacity]
    rw [ht]
    exact Nat.add_le_add_right (Nat.add_le_add_left hl _) _
  have hh := (HighIncidenceProgram.Prepare.input_budget q.scopeRows q.ambient tau hn).trans
    (Nat.mul_le_mul_left 270000 (Nat.pow_le_pow_left hc 3))
  rw [coreBudget,Query.coreInputBudget,scopeCopies_cost q a ha]
  dsimp only [Query.numericCost,numericCost]
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget_le_input_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreBudget_le_input_oai
