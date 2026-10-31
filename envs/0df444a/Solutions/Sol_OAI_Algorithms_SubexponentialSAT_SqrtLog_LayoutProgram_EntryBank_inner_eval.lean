-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:21:32.074819+00:00
-- url     : https://prove2.me/submissions/3478fc3d-ed13-4506-84a8-f97677cb0f6c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_prepared_integer_export_cleanup
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_IntegerEntry_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

theorem action_frame (v pr : Fin r) (op : Action s) (a : State r s)
    (j : Fin s) (hj : j≠op.destination) :
    (actionResult v pr op a).stacks j=a.stacks j := by
  cases op <;> simp_all [Action.destination,actionResult,StackRoutines.copyStacks,
    StackRoutines.clearStacks,TupleProgram.pushedState]

theorem result_frame (v pr : Fin r) (ops : List (Action s)) (a : State r s)
    (j : Fin s) (hj : ∀ op∈ops,j≠op.destination) :
    (result v pr ops a).stacks j=a.stacks j := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    exact (ih (actionResult v pr op a) (fun x hx=>hj x (by simp [hx]))).trans
      (action_frame v pr op a j (hj op (by simp)))

theorem clear_action_result (v pr : Fin r) (a : State r s) (i j : Fin s) :
    (actionResult v pr (.clear i) a).stacks j=if j=i then [] else a.stacks j := by
  simp [actionResult,StackRoutines.clearStacks,Function.update_apply]

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem integerRegs_inj : Function.Injective integerRegs := Fin.castAdd_injective _ _
theorem integerPorts_inj : Function.Injective integerPorts := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and measured-call lemmas used by the concrete entry-bank program.
The state maps below only specify the outcomes of actual fixed commands. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

/-- Every clear is charged, even when a repeated port is already empty. -/
theorem clear_cost_le {r s : ℕ} (v pr : Fin r) (ports : List (Fin s))
    (a : State r s) :
    Staging.cost v pr (ports.map Staging.Action.clear) a ≤
      2*(ports.map (fun j => (a.stacks j).length)).sum+3*ports.length := by
  induction ports generalizing a with
  | nil => simp [Staging.cost]
  | cons j js ih =>
    let b := Staging.actionResult v pr (.clear j) a
    have hb : ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
      intro i
      simp only [b,Staging.clear_action_result]
      split_ifs <;> simp
    have hsum' : (js.map (fun i => (b.stacks i).length)).sum ≤
        (js.map (fun i => (a.stacks i).length)).sum := by
      clear ih
      induction js with
      | nil => simp
      | cons i is hi => simpa using Nat.add_le_add (hb i) hi
    have h := ih b
    dsimp only [b] at h hsum'
    simp only [List.map_cons,Staging.cost,Staging.actionCost,List.sum_cons,List.length_cons]
    omega

theorem sum_map_le_length {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (h : ∀ x∈xs,f x ≤ B) : (xs.map f).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    calc
      f x+(xs.map f).sum ≤ B+xs.length*B := Nat.add_le_add hx hs
      _ = (xs.length+1)*B := by ring

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem prepare_frame (a : Data) (j : Fin 256) (hj : 64 ≤ j.val) :
    (Staging.result 0 1 prepareOps a).stacks j=a.stacks j := by
  apply Staging.result_frame
  intro op hop
  simp only [prepareOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [Staging.Action.destination] <;>
    (intro h; have hv := congrArg Fin.val h; simp at hv; omega)

theorem prepare_cost (a : Data) : Staging.cost 0 1 prepareOps a=7*prepareSize a+62 := by
  simp [prepareOps,Staging.cost,Staging.actionCost,Staging.actionResult,
    StackRoutines.copyStacks,prepareSize]
  ring

theorem exportPair_stacks (a : Data) (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[]) :
    (Staging.result 0 1 exportOps a).stacks=
      Function.update (Function.update a.stacks 254 (a.stacks 53)) 255 (a.stacks 54) := by
  simp [exportOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h254,h255]

theorem exportPair_cost (a : Data) :
    Staging.cost 0 1 exportOps a=7*((a.stacks 53).length+(a.stacks 54).length)+10 := by
  simp [exportOps,Staging.cost,Staging.actionCost,Staging.actionResult,StackRoutines.copyStacks]
  ring

theorem workPorts_mem (j : Fin 256) : j∈workPorts ↔ j.val < 200 := by
  simp only [workPorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    change i.val=j.val at hv
    omega
  · intro hj
    exact ⟨⟨j.val,hj⟩,Fin.ext rfl⟩

theorem workPorts_length : workPorts.length=200 :=
  List.length_ofFn

theorem cleanup_cost (a : Data) :
    Staging.cost 0 1 cleanupOps a ≤
      2*(workPorts.map (fun j => (a.stacks j).length)).sum+600 := by
  convert EntryBankFrame.clear_cost_le 0 1 workPorts a using 1 <;>
    norm_num [cleanupOps,workPorts_length]

theorem cleanup_cost_le (a : Data) (B : ℕ)
    (h : ∀ j : Fin 256, j.val < 200 → (a.stacks j).length ≤ B) :
    Staging.cost 0 1 cleanupOps a ≤ 400*B+600 := by
  have hs := EntryBankFrame.sum_map_le_length workPorts (fun j => (a.stacks j).length) B
    (fun j hj => h j ((workPorts_mem j).mp hj))
  have hc := cleanup_cost a
  rw [workPorts_length] at hs
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankFramePrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem prepare_stacks (a : Data) (h : ∀ j : Fin 256, j.val < 64 → a.stacks j=[]) :
    (Staging.result 0 1 prepareOps a).stacks=preparedStacks a := by
  simp [prepareOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,
    TupleProgram.pushedState,preparedStacks,h]

/-- The omitted negative power port really must be empty. This holds for the
unsigned power cache; no such assumption is hidden in the staging program. -/
theorem prepare_project {r Q : ℕ} (a : Data) (c : Numerator.Saved)
    (t : Fin Q) (u y : UniversalType r Q 1)
    (h : ∀ j : Fin 256, j.val < 64 → a.stacks j=[])
    (hp : a.stacks 202=c.hp) (hn : a.stacks 203=c.hn)
    (hw : a.stacks 204=c.width) (hpos : a.stacks 205=c.power.1)
    (hneg : c.power.2=[]) (hr : a.stacks 206=c.r) (ha : a.stacks 207=c.a)
    (hcolors : a.stacks 208=List.replicate r true)
    (hnodes : a.stacks 209=List.replicate Q true)
    (hnode : a.stacks 210=List.replicate t.val true)
    (hwidth : a.stacks 211=List.replicate (Q*r) true)
    (hu : a.stacks 65=CollisionProgram.encodeType u)
    (hy : a.stacks 68=CollisionProgram.encodeType y) :
    projectState integerRegs integerPorts (Staging.result 0 1 prepareOps a)=
      Numerator.state c ((Staging.result 0 1 prepareOps a).regs ∘ integerRegs)
        t u y [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  change (Staging.result 0 1 prepareOps a).stacks (integerPorts j)=_
  rw [prepare_stacks a h]
  fin_cases j <;>
    simp [integerPorts,preparedStacks,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,
      hp,hn,hw,hpos,hneg,hr,ha,hcolors,hnodes,hnode,hwidth,hu,hy,h]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankInner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual cached universal-entry call, including all physical staging,
export and cleanup. The caller's private fiber-loop bank is unrestricted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram

variable {r Q : ℕ}

private theorem prepareSize_le (a : Data) (S : ℕ)
    (h : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
    prepareSize a ≤ 12*S := by
  have h1 := h 202 (by decide)
  have h2 := h 203 (by decide)
  have h3 := h 204 (by decide)
  have h4 := h 205 (by decide)
  have h5 := h 206 (by decide)
  have h6 := h 207 (by decide)
  have h7 := h 208 (by decide)
  have h8 := h 209 (by decide)
  have h9 := h 210 (by decide)
  have h10 := h 211 (by decide)
  have h11 := h 65 (by decide)
  have h12 := h 68 (by decide)
  unfold prepareSize
  omega

private theorem update_length_le (f : Fin 256 → List Bool) (i j : Fin 256)
    (v : List Bool) (B : ℕ) (hf : (f j).length ≤ B) (hv : v.length ≤ B) :
    (Function.update f i v j).length ≤ B := by
  by_cases h : j=i
  · subst j; simpa using hv
  · simpa [Function.update_of_ne h] using hf

private theorem prepared_length (a : Data) (S : ℕ)
    (hl : ∀ j : Fin 256, j.val < 64 → a.stacks j=[])
    (h : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S)
    (j : Fin 256) (hj : j.val < 200) :
    ((Staging.result 0 1 prepareOps a).stacks j).length ≤ S+1 := by
  rw [prepare_stacks a hl]
  unfold preparedStacks
  repeat' apply update_length_le
  all_goals first
    | (exact (h _ (by omega)).trans (Nat.le_succ S))
    | (simp only [List.length_singleton]; omega)

/-- This theorem has no value-producing callback: it calls the fixed
`IntegerEntry.command`, and charges staging, export and complete cleanup. -/
theorem inner_eval_oai (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1)
    (a : Data) (S : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : Cached a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t u y)
    (hsize : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
    let L := IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1
    ∃ n ≤ IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y+
        484*S+407*L+1073,
      ∃ rf result, Eval inner n a (finish a rf result) ∧
        pairValue result=IntegerEntry.value aWord.length R t u y ∧
        LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  intro L
  let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord
  let p := Staging.result 0 1 prepareOps a
  have hproj := prepare_project a c t u y hc.low hc.hp hc.hn hc.hw hc.hpos hc.hneg hc.hr hc.ha
    hc.colors hc.nodes hc.node hc.typeWidth hc.rowType hc.colType
  obtain ⟨ni,hni,ri,result,hi,hvalue,hmass,hlength⟩ := IntegerEntry.command_eval Hwords width power
    (p.regs ∘ integerRegs) aWord R t u y hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
  let b := IntegerEntry.output c ri t u y result
  have hi' : Eval IntegerEntry.command ni (projectState integerRegs integerPorts p) b := by
    rw [hproj]
    exact hi
  let q := embedState integerRegs integerPorts p b
  let e := Staging.result 0 1 exportOps q
  let z := Staging.result 0 1 cleanupOps e
  obtain ⟨hrun,hout⟩ := prepared_integer_export_cleanup a hc.temp hc.posEmpty hc.negEmpty hi'
  have hbstacks : b.stacks=Function.update (Function.update
      (projectState integerRegs integerPorts p).stacks 53 result.1) 54 result.2 := by
    rw [hproj]
    rfl
  have hqstacks : q.stacks=Function.update (Function.update p.stacks 53 result.1) 54 result.2 := by
    change Function.extend integerPorts b.stacks p.stacks=_
    rw [hbstacks,ProgramLinking.extend_update integerPorts_inj,
      ProgramLinking.extend_update integerPorts_inj]
    have hext := congrArg StructuredProgram.State.stacks
      (embedState_project integerRegs integerPorts p integerRegs_inj integerPorts_inj)
    change Function.update (Function.update
      (embedState integerRegs integerPorts p (projectState integerRegs integerPorts p)).stacks
        (53 : Fin 256) result.1) (54 : Fin 256) result.2 = _
    rw [hext]
  have hz : z=finish a z.regs result := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      calc
        z.stacks j = if j.val < 200 then [] else if j=255 then b.stacks 54
            else if j=254 then b.stacks 53 else a.stacks j := hout j
        _ = (finish a z.regs result).stacks j := by simp [b,IntegerEntry.output,finish]
  have hpl : ∀ j : Fin 256, j.val < 200 → (p.stacks j).length ≤ S+1 :=
    prepared_length a S hc.low hsize
  have hql : ∀ j : Fin 256, j.val < 200 → (q.stacks j).length ≤ S+L+1 := by
    intro j hj
    rw [hqstacks]
    by_cases h54 : j=54
    · subst j
      simp only [Function.update_self]
      change result.1.length+result.2.length ≤ L at hlength
      omega
    · by_cases h53 : j=53
      · subst j
        simp only [Function.update_of_ne (by decide : (53:Fin 256)≠54),Function.update_self]
        change result.1.length+result.2.length ≤ L at hlength
        omega
      · rw [Function.update_of_ne h54,Function.update_of_ne h53]
        have hh := hpl j hj
        omega
  have hq254 : q.stacks 254=[] := by
    rw [hqstacks]
    simpa using (prepare_frame a 254 (by decide)).trans hc.posEmpty
  have hq255 : q.stacks 255=[] := by
    rw [hqstacks]
    simpa using (prepare_frame a 255 (by decide)).trans hc.negEmpty
  have hel : ∀ j : Fin 256, j.val < 200 → (e.stacks j).length ≤ S+L+1 := by
    intro j hj
    change ((Staging.result 0 1 exportOps q).stacks j).length ≤ _
    rw [exportPair_stacks q hq254 hq255]
    have hn254 : j≠254 := by intro h; subst j; omega
    have hn255 : j≠255 := by intro h; subst j; omega
    simpa [hn254,hn255] using hql j hj
  have hcleanup := cleanup_cost_le e (S+L+1) hel
  have hprepare := prepareSize_le a S hsize
  have hexport : Staging.cost 0 1 exportOps q ≤ 7*L+10 := by
    rw [exportPair_cost,hqstacks]
    simp only [Function.update_self,Function.update_of_ne (by decide : (53:Fin 256)≠54)]
    change result.1.length+result.2.length ≤ L at hlength
    omega
  refine ⟨Staging.cost 0 1 prepareOps a+((ni+1)+
      (Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e)),?_,z.regs,result,?_,hvalue,hmass,hlength⟩
  · rw [prepare_cost]
    omega
  · change Eval inner _ a z at hrun
    rw [hz] at hrun
    exact hrun

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval_oai
