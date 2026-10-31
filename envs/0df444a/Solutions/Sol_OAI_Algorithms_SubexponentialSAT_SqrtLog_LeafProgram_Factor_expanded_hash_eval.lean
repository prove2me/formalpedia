-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:09:52.042295+00:00
-- url     : https://prove2.me/submissions/6c282433-a4c4-4920-b12d-e86654841cde

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Expansion_forward_original_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_hash_value_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

theorem stackMap_injective : Function.Injective stackMap := by decide

theorem finished_frame (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (i : Fin 768) (hi : ¬∃ j, stackMap j=i) :
    (finished a rf word).stacks i=a.stacks i :=
  embedState_stack_frame register stackMap a _ i hi

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansionForward
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The preserved source lookup returns forward frame contents. Reverse this
actual tape before invoking the raw-tuple assembler. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem reversedInput_frame (a : Data) (i : Fin 768) (hi : i ≠ 154) :
    (reversedInput a).stacks i = a.stacks i := by
  simp [reversedInput,afterReverse,StackRoutines.reverseStacks,hi]

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansionFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact frame of the paid forward-row expansion. The returned inline row
is the only retained output; source154 is consumed and all private cells
are restored to their empty entry values. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf word).stacks =
      Function.update (Function.update a.stacks 154 []) 64 word := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf word).stacks (stackMap j) =
        (HashInputProgram.Loop.data rf [] (a.stacks 708) (a.stacks 707)
          (a.stacks 700) (a.stacks 280) word [] [] [] []).stacks j from
      embedState_stack register stackMap a _ stackMap_injective j]
    fin_cases j <;>
      simp_all [HashInputProgram.Loop.data,HashInputProgram.Loop.tapes,stackMap,scratch]
  · have h154 : i ≠ 154 := by intro hi; subst i; exact hin ⟨0,rfl⟩
    have h64 : i ≠ 64 := by intro hi; subst i; exact hin ⟨16,rfl⟩
    rw [finished_frame a rf word i hin]
    simp [h154,h64]

theorem forward_finished_stacks (a : Data) (rf : Fin 8 → Bool) (word : List Bool)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished (reversedInput a) rf word).stacks =
      Function.update (Function.update a.stacks 154 []) 64 word := by
  have hw : ∀ i ∈ scratch, (reversedInput a).stacks i = [] := by
    intro i hi
    have hn : i ≠ 154 := by
      simp only [scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [reversedInput_frame a i hn]
    exact hwork i hi
  rw [finished_stacks _ _ _ hw]
  funext i
  by_cases h64 : i = 64
  · subst i; simp
  by_cases h154 : i = 154
  · subst i; simp
  simp only [Function.update_of_ne h64,Function.update_of_ne h154]
  exact reversedInput_frame a i h154

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Execution of the computed factor value and its multiplication into the
current head product. Input incidence dictionaries are the physically
produced tables supplied by the preceding service. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem low_ne (i : Fin 56) (j : Fin 768) (hj : 56 ≤ j.val) :
    nativeStacks (Memory.lowPort i)  ≠  j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=j.val at hv
  omega

theorem indicatorStacks_low (i : Fin 56) :
    indicatorStacks (Memory.lowPort i)=nativeStacks (Memory.lowPort i) := by
  have h78 := low_ne i 78 (by decide)
  have h143 := low_ne i 143 (by decide)
  simp [indicatorStacks,Equiv.swap_apply_def,h78,h143]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorExpanded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The ordinary hash branch reads the actual forward raw row, expands its
original clauses, computes the indicator, and accumulates its result. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram

theorem expanded_hash_eval_oai {t n d : ℕ} (ctx : Context 3 t n d) (ht : 0 < t) (hd : 0 < d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t)))
    (b : ℕ) (hb : 0 < b) (hbound : 3*(HashInputProgram.Expansion.encodedClauses source).length ≤ 2^b)
    (a : Data)
    (hraw : a.stacks 154=(HashInputProgram.Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=(HashInputProgram.Expansion.encodedClauses source).length)
    (hringshape : (a.stacks 280).length=d*baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hexpand : ∀ i ∈ Expansion.scratch,a.stacks i=[])
    (h358 : a.stacks 358=[]) (h359 : a.stacks 359=[])
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i)
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let ws := HashInputProgram.Expansion.weightedRow t d source terms
    let factor := Indicator.result ctx minus one incidence ws digits
    let result := Product.run 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k z,k ≤ 9*(a.stacks 154).length+10+
        HashInputProgram.Loop.uniformBudget t (d-1) b (a.stacks 707)
          (HashInputProgram.Expansion.encodedClauses source) terms.length+
        FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
        (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
          2*(a.stacks 62).length+6+productBudget 3 t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq Expansion.forwardCommand (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate)))) k a z ∧
      z.stacks=Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  let ws := HashInputProgram.Expansion.weightedRow t d source terms
  obtain ⟨ke,re,hke,he⟩ := HashInputProgram.Expansion.forward_original_eval t d ht hd b hb source terms
    hbound a hraw hsource hwidth hmodulus hringshape houtput hexpand h358 h359
  let mid := Expansion.finished (Expansion.reversedInput a) re (Encoding.encodeList id (ws.map Row.payload))
  have hm : mid.stacks=Function.update (Function.update a.stacks 154 []) 64
      (Encoding.encodeList id (ws.map Row.payload)) := Expansion.forward_finished_stacks a re _ hexpand
  have hmlow : ∀ i,mid.stacks (indicatorStacks (Memory.lowPort i))=low ctx i := by
    intro i
    rw [hm,indicatorStacks_low,Function.update_of_ne (low_ne i 64 (by decide)),
      Function.update_of_ne (low_ne i 154 (by decide))]
    simpa only [indicatorStacks_low] using hlow i
  have hmwork : ∀ i ∈ FactorServices.indicatorScratch,mid.stacks (indicatorStacks i)=[] := by
    intro i hi
    have hn : indicatorStacks i ≠ 64 ∧ indicatorStacks i ≠ 154 := by
      have hh : ∀ i ∈ FactorServices.indicatorScratch,indicatorStacks i ≠ 64 ∧ indicatorStacks i ≠ 154 := by decide
      exact hh i hi
    rw [hm,Function.update_of_ne hn.1,Function.update_of_ne hn.2]
    exact hwork i hi
  have hB : 0 < baseWidth 3 t := by
    unfold baseWidth
    exact Nat.mul_pos ht (by omega)
  obtain ⟨kv,z,hkv,hv,hz⟩ := hash_value_eval ctx hd hB minus one seed incidence entries hl ws digits mid hmlow
    (by rw [hm]; simp)
    (by simpa [hm] using htable)
    (by simpa [hm] using hone)
    (by simpa [hm] using hminus)
    (by simpa [hm] using htape)
    (by simpa [hm] using hshape)
    hmwork (by simpa [hm] using hseed) (by simpa [hm] using htmp)
  have hm62 : mid.stacks 62=a.stacks 62 := by simp [hm]
  rw [hm62] at hkv
  refine ⟨ke+kv,z,?_,he.seq hv,?_⟩
  · dsimp only [ws] at *
    omega
  · rw [hz,hm]
    funext i
    by_cases h154 : i=154 <;> by_cases h64 : i=64 <;> by_cases h67 : i=67 <;>
      by_cases h68 : i=68 <;> by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
      simp [h154,h64,h67,h68,h62,h151,ws]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval_oai
