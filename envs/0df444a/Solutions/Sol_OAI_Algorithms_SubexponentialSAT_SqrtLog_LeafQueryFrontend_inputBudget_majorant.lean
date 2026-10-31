-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:58:44.018007+00:00
-- url     : https://prove2.me/submissions/c5d628dc-1544-483d-b85e-1b100515df28

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_query_bounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_scope_cost_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SparsificationBudgetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A directly computed dyadic sparsification budget

For each fixed width k, a fixed control constant T suffices.  The selected
parameter is a power of two whose binary length is an affine function of the
binary length of the inverse budget.  This is the explicit witness from
SparsificationBudget.dyadic_witness, rather than the least passing candidate.

The control constant is chosen before the input word.  Program definitions
below manipulate bits only; their specifications use the corresponding
natural-number values.
-/

namespace SubexponentialSAT.SparsificationBudgetProgram

open SubexponentialSAT.CounterPrograms

/-! ## The actual fixed finite program -/

theorem bits_length_le (s : ℕ) : s.bits.length ≤ s := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_pow_self (by decide))

/-! ## The input-size to inverse-budget to M pipeline -/

end SubexponentialSAT.SparsificationBudgetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

/-- The scope representation used by the clause producer is exactly the
generic framed-record representation consumed by this program. -/
theorem encode_scope (scope : List ℕ) :
    Encoding.encodeList id (scope.map Encoding.encodeNat) =
      Encoding.encodeList Encoding.encodeNat scope := by
  induction scope with
  | nil => rfl
  | cons j scope ih => simp [Encoding.encodeList, ih]

end SubexponentialSAT.SubexpScopeCountSetup

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
@[simp] theorem decoded_encode (scope : List ℕ) :
    decoded (Encoding.encodeList Encoding.encodeNat scope) = scope := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeList_injective Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨scope,rfl⟩).elim

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArityBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost in the actual serialized scope input and mask length. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem scopeBudget_le (mask : List Bool) (scope : List ℕ) :
    scopeBudget mask scope ≤ (16*(mask.length+1)+17)*
      ((Encoding.encodeList Encoding.encodeNat scope).length+1) := by
  have h := RecordPrograms.program_budget_le_input
    (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) 0 (16*(mask.length+1))
    (by intro bits hb; simp)
  simpa [scopeBudget,ProgramEncoding.encodeRecords,SubexpScopeCountSetup.encode_scope] using h

theorem cost_le (mask : List Bool) (scope : List ℕ) :
    cost mask (Encoding.encodeList Encoding.encodeNat scope) ≤
      (16*(mask.length+1)+42)*((Encoding.encodeList Encoding.encodeNat scope).length+1) := by
  have hb := scopeBudget_le mask scope
  have hl := Encoding.length_encodeList_lower Encoding.encodeNat scope
  simp only [cost,decoded_encode]
  nlinarith

theorem totalBudget_le (mask : List Bool) (scopes : List (List ℕ)) :
    4+RecordPrograms.budget (cost mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)) ≤
      (32*(mask.length+1)+101)*
        ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes).length+1) := by
  have h := RecordPrograms.program_budget_le_input (cost mask)
    (scopes.map (Encoding.encodeList Encoding.encodeNat))
    (16*(mask.length+1)+42) (16*(mask.length+1)+42)
    (by
      intro bits hb
      obtain ⟨scope,hs,rfl⟩ := List.mem_map.mp hb
      have hc := cost_le mask scope
      nlinarith)
  have hencode : ∀ xs : List (List ℕ), ProgramEncoding.encodeRecords
      (xs.map (Encoding.encodeList Encoding.encodeNat)) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xs := by
    intro xs
    change Encoding.encodeList id (xs.map (Encoding.encodeList Encoding.encodeNat)) = _
    induction xs with
    | nil => rfl
    | cons scope scopes ih => simp [Encoding.encodeList,ih]
  rw [hencode] at h
  convert h using 1 <;> first | rfl | ring

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial physical cost and basic exact output identities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem stepBudget_le (scopes : List (List ℕ)) (n v : ℕ) (hv : v ≤ n) :
    stepBudget scopes v ≤ uniformStepBudget scopes n := by
  have hc := SubexpIncidenceSlotProgram.budget_le scopes scopes.length v
    ((scopeBits scopes).length+scopes.length+n)
    (by change (scopeBits scopes).length ≤ (scopeBits scopes).length+scopes.length+n; omega)
    (by omega) (by omega)
  have hd : degree scopes v ≤ scopes.length :=
    SubexpIncidencePlanScan.incidenceFrom_length_le v 0 scopes
  dsimp [stepBudget,uniformStepBudget]
  omega

theorem variableBudget_le (scopes : List (List ℕ)) (n v : ℕ) (mask : List Bool)
    (hn : v+mask.length ≤ n) :
    variableBudget scopes v mask ≤ mask.length*(uniformStepBudget scopes n+1)+1 := by
  induction mask generalizing v with
  | nil => simp [variableBudget]
  | cons b bs ih =>
    have hs := stepBudget_le scopes n v (by simp at hn; omega)
    have ht := ih (v+1) (by simp at hn; omega)
    simp only [variableBudget,List.length_cons]
    nlinarith

theorem bootBudget_le (scopes : List (List ℕ)) (mask : List Bool) :
    bootBudget scopes mask ≤ 10*(scopeBits scopes).length+7*mask.length+12 := by
  have h := SubexpSunflowerProgram.CountRecords.steps_le_encoded
    (scopes.map SubexpIncidenceSlotProgram.scopeBytes)
  rw [SubexpIncidenceSlotProgram.encode_map] at h
  change SubexpSunflowerProgram.CountRecords.steps (scopes.map SubexpIncidenceSlotProgram.scopeBytes) ≤
    3*(scopeBits scopes).length+4 at h
  dsimp [SubexpSunflowerProgram.CountRecords.steps] at h
  dsimp [bootBudget]
  omega

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafScopeInputBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem conversionCost_mono {a b : ℕ} (h : a ≤ b) : conversionCost a ≤ conversionCost b := by
  unfold conversionCost
  gcongr

theorem numericCost_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.numericCost k ≤ numericMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hk := (SparsificationBudgetProgram.bits_length_le k).trans h.widthParameter
  have hf := conversionCost_mono h.free
  have ho := conversionCost_mono h.occurrence
  have ha := conversionCost_mono h.arity
  have hq := conversionCost_mono h.factors
  have hm := conversionCost_mono h.incidences
  have hn := h.ambientBits
  have hc := h.modulus
  unfold Query.numericCost numericCost numericMajorant
  omega

theorem scopeCopyBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.scopeCopyBudget ≤ 42*capacity q k+30 := by
  have h := query_bounds q k hv
  have h0 := h.master
  have h1 := h.rowBits
  have h2 := h.index
  have h3 := h.modulus
  have h4 := h.width
  have h5 := h.eight
  unfold Query.scopeCopyBudget
  omega

theorem log_bound (q : Query) (k : ℕ) :
    Asymptotic.L (BinaryArithmetic.toNat q.ambient) ≤ capacity q k+17 := by
  have h := Nat.log2_le_self (BinaryArithmetic.toNat q.ambient+16)
  unfold Asymptotic.L capacity
  omega

theorem highCapacity_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.highCapacity ≤ 16*(capacity q k)^3+4*capacity q k+40 := by
  have h := query_bounds q k hv
  have hs := h.scopeBits
  have hn := h.ambient
  have hb := h.ambientBits
  have hl := log_bound q k
  have ht := Nat.sqrt_le_self (Asymptotic.L (BinaryArithmetic.toNat q.ambient))
  unfold Query.highCapacity EarlyThreshold.threshold
  omega

theorem high_stage_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    7*q.ambient.length+5+EarlyThreshold.runtimeBound q.ambient+
      (7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.ambient.length+5+
        7*(Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+5)+
      270000*q.highCapacity^3+17*q.forward.length+14 ≤ highMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hl := log_bound q k
  have hc := highCapacity_bound q k hv
  have he : EarlyThreshold.runtimeBound q.ambient ≤ 300001*(2*capacity q k+37)^3 := by
    unfold EarlyThreshold.runtimeBound
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have := h.ambientBits
    omega
  have hh := Nat.mul_le_mul_left 270000 (Nat.pow_le_pow_left hc 3)
  have hb := h.ambientBits
  have hs := h.scopeBits
  have hf := h.forward
  unfold highMajorant
  omega

theorem measure_stage_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+7*q.forward.length+5+
      LeafStatisticsProgram.bootBudget q.scopeRows q.forward+
      LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward+2+
      7*q.forward.length+5+7*(LeafStatisticsProgram.scopeBits q.scopeRows).length+5+3+4+
      RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
        (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat))+
      3*(totals q.scopeRows q.forward).uncovered+10 ≤ measureMajorant (capacity q k) := by
  have h := query_bounds q k hv
  have hb := LeafStatisticsProgram.bootBudget_le q.scopeRows q.forward
  have hvb := LeafStatisticsProgram.variableBudget_le q.scopeRows q.forward.length 0 q.forward (by omega)
  have hva : LeafStatisticsProgram.variableBudget q.scopeRows 0 q.forward ≤
      capacity q k*(1000*(16*(capacity q k)^3+capacity q k+capacity q k+1)^2+
        50*(capacity q k+1)+50+1)+1 := by
    apply hvb.trans
    unfold LeafStatisticsProgram.uniformStepBudget
    gcongr
    · exact h.forward
    · exact h.scopeBits
    · exact h.scopeCount
    · exact h.forward
    · exact h.scopeCount
  have hab := LeafStatisticsProgram.Arity.totalBudget_le q.forward q.scopeRows
  have hab' : 4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost q.forward)
      (q.scopeRows.map (Encoding.encodeList Encoding.encodeNat)) ≤
      (32*(capacity q k+1)+101)*(16*(capacity q k)^3+1) := by
    apply hab.trans
    change (32*(q.forward.length+1)+101)*((LeafStatisticsProgram.scopeBits q.scopeRows).length+1) ≤ _
    gcongr
    · exact h.forward
    · exact h.scopeBits
  have hs := h.scopeBits
  have hf := h.forward
  have hu := h.uncovered
  unfold measureMajorant
  omega

theorem coreInputBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.coreInputBudget k ≤ scanMajorant (capacity q k)+
      LeafParametersProgram.Execute.runtimeBound (q.input k) (q.inputLengths k)+1 := by
  have hr := scopeCopyBudget_bound q k hv
  have hs := scope_cost_le q k hv
  have hb := (query_bounds q k hv).scopeBits
  have hh := high_stage_bound q k hv
  have hm := measure_stage_bound q k hv
  have hn := numericCost_bound q k hv
  unfold Query.coreInputBudget scanMajorant
  dsimp only
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafScopeInputBounds
open LeafParametersProgram.FrontendBounds
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem parameter_counts_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    CountsBound (q.input k) (parameterSize (capacity q k)) := by
  have h := query_bounds q k hv
  have h0 := h.ambient
  have h1 := h.free
  have h2 := h.clauseCount
  have h3 := h.occurrence
  have h4 := h.arity
  have h5 := h.factors
  have h6 := h.widthParameter
  have h7 := h.incidences
  have hm := hv.2.2.2.2.2.1
  intro i
  fin_cases i
  · change BinaryArithmetic.toNat q.ambient ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).free ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change BinaryArithmetic.toNat q.modulus ≤ parameterSize (capacity q k)
    rw [hm]
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).occurrence ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change completedArity q.scopeRows q.forward ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change q.scopeRows.length+(totals q.scopeRows q.forward).uncovered ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change k ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega
  · change (totals q.scopeRows q.forward).incidences ≤ parameterSize (capacity q k)
    unfold parameterSize
    omega

theorem parameter_lengths_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    ∀ i, q.inputLengths k i ≤ parameterSize (capacity q k) := by
  intro i
  have h := numericCost_bound q k hv
  change q.numericCost k ≤ _
  unfold parameterSize
  omega

theorem hashCountBudget_bound (q : Query) (k : ℕ) (hv : q.Valid) :
    q.hashCountBudget ≤ 10*capacity q k+9 := by
  have hs := SubexpSunflowerProgram.CountRecords.steps_le_encoded
    (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
  have hr := (query_bounds q k hv).rowBits
  change (Encoding.encodeList id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))).length ≤
    capacity q k at hr
  unfold Query.hashCountBudget SubexpScopeCountSetup.countBudget
  dsimp only [SubexpSunflowerProgram.CountRecords.steps] at hs
  omega

theorem inputBudget_majorant_oai (C d : ℕ)
    (hp : ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ), CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l)+
        5000*(2*(Execute.guardedModel x l).val 29+1)^2*
          ((Execute.guardedModel x l).len 3+(Execute.guardedModel x l).len 21+
            (Execute.guardedModel x l).len 29+11)^2 ≤ C*(S+1)^d)
    (q : Query) (k : ℕ) (hv : q.Valid) :
    q.inputBudget k ≤ finalMajorant C d (capacity q k) := by
  have hc := coreInputBudget_bound q k hv
  have hh := hashCountBudget_bound q k hv
  have hn := (query_bounds q k hv).ambient
  have hb := hp (q.input k) (q.inputLengths k) (parameterSize (capacity q k))
    (parameter_counts_bound q k hv) (parameter_lengths_bound q k hv)
  change Execute.runtimeBound (q.input k) (q.inputLengths k)+
    Exports.prepareBudget (Execute.guardedModel (q.input k) (q.inputLengths k))+
    offsetModelBudget (Execute.guardedModel (q.input k) (q.inputLengths k)) ≤
      C*(parameterSize (capacity q k)+1)^d at hb
  unfold Query.inputBudget postUniformBudget postPrefixBudget finalMajorant
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.inputBudget_majorant_oai
