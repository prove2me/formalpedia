-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:57:11.949631+00:00
-- url     : https://prove2.me/submissions/e71bad46-a6a6-477e-9137-b0122d3c0fe9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader_localResult_outputs

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

theorem write_length (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    (write mask j bit).length = mask.length := by
  simp [write, List.length_take, List.length_drop, Nat.min_eq_left hj.le]
  omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem scatter_length (js : List ℕ) (bits mask : List Bool)
    (hb : ∀ j ∈ js, j < mask.length) :
    (scatter js bits mask).length = mask.length := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have ht : ∀ k ∈ js, k < (write mask j b).length := by
            intro k hk; rw [hw]; exact hb k (by simp [hk])
          exact (ih bits _ ht).trans hw

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

private theorem write_eq_set (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    write mask j bit = mask.set j bit := by
  simp [List.set_eq_take_append_cons_drop, hj, write]

theorem scatter_outside (js : List ℕ) (bits mask : List Bool) (k : ℕ)
    (hb : ∀ j ∈ js, j < mask.length) (hk : k ∉ js) :
    (scatter js bits mask)[k]? = mask[k]? := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hne : j ≠ k := by intro h; subst k; simp at hk
          have htail : k ∉ js := by intro h; exact hk (List.mem_cons_of_mem j h)
          have hw := write_length mask j b hj
          change (scatter js bits (write mask j b))[k]? = _
          rw [ih bits (write mask j b) (by intro l hl; rw [hw]; exact hb l (by simp [hl])) htail]
          rw [write_eq_set mask j b hj, List.getElem?_set_ne hne]

theorem scatter_at (js : List ℕ) (bits mask : List Bool) (k : ℕ) (bit : Bool)
    (hb : ∀ j ∈ js, j < mask.length) (hd : js.Nodup) (hm : (k, bit) ∈ js.zip bits) :
    (scatter js bits mask)[k]? = some bit := by
  induction js generalizing bits mask with
  | nil => simp at hm
  | cons j js ih =>
      cases bits with
      | nil => simp at hm
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have htail : ∀ l ∈ js, l < (write mask j b).length := by
            intro l hl; rw [hw]; exact hb l (by simp [hl])
          simp only [List.zip_cons_cons, List.mem_cons] at hm
          rcases hm with heq | hm
          · have he : k = j ∧ bit = b := by simpa using heq
            rcases he with ⟨he1, he2⟩
            subst k; subst bit
            change (scatter js bits (write mask j b))[j]? = some b
            rw [scatter_outside js bits _ j htail (List.nodup_cons.mp hd).1]
            rw [write_eq_set mask j b hj, List.getElem?_set_self hj]
          · exact ih bits (write mask j b) htail (List.nodup_cons.mp hd).2 hm

theorem mask_length (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hb : ∀ j ∈ js, j < n) : (mask n js bits).length = n := by
  simpa [mask] using scatter_length js bits (List.replicate n false) (by simpa using hb)

theorem mask_outside (n : ℕ) (js : List ℕ) (bits : List Bool) (k : ℕ)
    (hb : ∀ j ∈ js, j < n) (hk : k < n) (hne : k ∉ js) :
    (mask n js bits)[k]? = some false := by
  rw [mask, scatter_outside js bits _ k (by simpa using hb) hne]
  simp [hk]

theorem mask_at (n : ℕ) (js : List ℕ) (bits : List Bool) (k : ℕ) (bit : Bool)
    (hb : ∀ j ∈ js, j < n) (hd : js.Nodup) (hm : (k, bit) ∈ js.zip bits) :
    (mask n js bits)[k]? = some bit :=
  scatter_at js bits _ k bit (by simpa using hb) hd hm

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

variable {n h : ℕ}

theorem headIds_bound (head : Fin h → Fin n) : ∀ j ∈ headIds head,j < n := by
  intro j hj
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
  exact (head i).isLt

theorem headIds_nodup (head : Fin h → Fin n) (hinj : Function.Injective head) :
    (headIds head).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  exact hinj (Fin.ext hij)

theorem typed_mask_head (head : Fin h → Fin n) (hinj : Function.Injective head)
    (x : Fin h → Bool) (i : Fin h) :
    (mask n (headIds head) (headBits x))[(head i).val]? = some (x i) := by
  apply mask_at n _ _ _ _ (headIds_bound head) (headIds_nodup head hinj)
  have hz : ((headIds head).zip (headBits x))[i.val]? = some ((head i).val,x i) := by
    apply List.getElem?_zip_eq_some.mpr
    constructor <;> simp [headIds,headBits,i.isLt]
  exact List.mem_of_getElem? hz

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_injective (p : ℕ → Bool) (n : ℕ) : Function.Injective (headOrder p n) := by
  intro i j hij
  apply List.nodup_iff_injective_getElem.mp (chosenIds_nodup p n)
  exact congrArg Fin.val hij

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem leafFrom_head_outputs (src : Fin 896) (frame : State 40 896) (a : State 16 896) (b : Data)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    let result := localResult b rp rm rs n N W z rows low raw shifted
    let e := embedState leafRegs id frame (exportedState (lowResultFrom src a result))
    let js := selectedHeads n rows low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        Encoding.encodeNat) := by
  dsimp only
  have hh := localResult_outputs b rp rm rs n N W z rows low raw shifted
  have hstack (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
      (embedState leafRegs id frame (exportedState (lowResultFrom src a
        (localResult b rp rm rs n N W z rows low raw shifted)))).stacks (lowStacks i)=
          (localResult b rp rm rs n N W z rows low raw shifted).stacks i :=
    (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
      (lowResultFrom_low src a _ i h659 h668 h669)
  exact ⟨(hstack 650 (by decide) (by decide) (by decide)).trans hh.1,
    (hstack 651 (by decide) (by decide) (by decide)).trans hh.2.1,
    (hstack 670 (by decide) (by decide) (by decide)).trans hh.2.2.1,
    (hstack 671 (by decide) (by decide) (by decide)).trans hh.2.2.2⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Scattering an actual all-true assignment over the emitted IDs yields
exactly the selection predicate in the original ambient coordinates. -/
theorem support_mask_at (p : ℕ → Bool) (n j : ℕ) (hj : j < n) :
    (HeadScatterProgram.mask n (chosenIds p n) (List.replicate (count p n) true))[j]? =
      some (p j) := by
  cases hp : p j with
  | false =>
      exact HeadScatterProgram.mask_outside n _ _ j (chosenIds_bound p n) hj
        (by simp [chosenIds,hp])
  | true =>
      have hm : j ∈ HeadScatterProgram.headIds (headOrder p n) := by
        rw [headOrder_ids]
        simp [chosenIds,hj,hp]
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      have he := HeadScatterProgram.typed_mask_head (headOrder p n)
        (headOrder_injective p n) (fun _ => true) i
      simpa only [headOrder_ids,HeadScatterProgram.headBits,List.ofFn_const,hi] using he

theorem support_mask_eq (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.mask n (chosenIds p n) (List.replicate (count p n) true) =
      List.ofFn (fun v : Fin n => p v.val) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [support_mask_at p n j hj]
    simp [hj]
  · rw [List.getElem?_eq_none (by
      rw [HeadScatterProgram.mask_length n _ _ (chosenIds_bound p n)]
      omega)]
    simp [hj]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Outputs
variable (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))

theorem result_head_outputs :
    let e := result s z frame rp rm rs raw shifted
    let js := selectedHeads s.n s.rows s.low z
    e.stacks 650=HeadScatterProgram.indices js ∧
    e.stacks 651=List.replicate js.length false ∧
    e.stacks 670=HeadScatterProgram.mask s.n js (List.replicate js.length true) ∧
    e.stacks 671=ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate s.rows s.n z) s.N).map
        Encoding.encodeNat) :=
  SignatureHeadLoader.leafFrom_head_outputs 843 frame _ _ rp rm rs
    s.n s.N (s.Q*s.r) z s.rows s.low raw shifted

theorem result_mask_word_oai :
    (result s z frame rp rm rs raw shifted).stacks 670 =
      List.ofFn (fun v : Fin s.n => HeadIdentifierProgram.predicate s.rows s.low z v.val) := by
  rw [(result_head_outputs s z frame rp rm rs raw shifted).2.2.1]
  exact HeadIdentifierProgram.support_mask_eq _ _

end Outputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_word_oai
