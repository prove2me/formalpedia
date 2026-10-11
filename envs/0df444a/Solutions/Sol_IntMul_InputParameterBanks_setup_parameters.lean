-- Prove2me | solution 1 for IntMul.InputParameterBanks.setup_parameters
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T18:14:25.043291+00:00
-- url     : https://prove2.me/submissions/1f7d874f-44f6-4093-a92d-7019454666ec

import Definitions.Def_IntMul_InputParameterBanks
import Theorems.Thm_IntMul_InputCarrySetup_input_carry_setup
import Theorems.Thm_IntMul_DescriptorCopy_copy_descriptor
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Tactic
import Theorems.Thm_IntMul_InputArithmeticDescriptors_input_arithmetic_descriptors

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.InputParameterBanks
open TapeCopy (Sym)
private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private theorem parameter_step (c : InputCarrySetup.machine.Cfg) :
    subroutine.step (parameterView c)=parameterView (InputCarrySetup.machine.step c) := by
  classical
  let a : Fin 18 → Sym := fun i => c.cells i (c.head i)
  have ht : transition (parameterState c.state) a=(parameterState (InputCarrySetup.machine.δ c.state a).1,
      (InputCarrySetup.machine.δ c.state a).2) := by
    by_cases h : c.state=InputCarrySetup.machine.qHalt
    · rw [h,InputCarrySetup.machine.halt_fixed a]
      rfl
    · cases hc : c.state with
      | none => exact False.elim (h hc)
      | some q => rfl
  change transition (parameterView c).state (fun i => (parameterView c).cells i ((parameterView c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];rfl

private theorem parameter_run (c : InputCarrySetup.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (parameterView c)=parameterView (InputCarrySetup.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,parameter_step,Function.iterate_succ_apply']

private theorem copy_read (x y : List Bool) (c : DescriptorCopy.machine.Cfg) (j : Fin 3) :
    (copyView x y c).cells (copyTape j) ((copyView x y c).head (copyTape j))=c.cells j (c.head j) := by
  fin_cases j <;> rfl

private theorem copy_step (x y : List Bool) (c : DescriptorCopy.machine.Cfg) :
    subroutine.step (copyView x y c)=copyView x y (DescriptorCopy.machine.step c) := by
  classical
  let a : Fin 18 → Sym := fun i => (copyView x y c).cells i ((copyView x y c).head i)
  have hread : (fun j => a (copyTape j))=(fun j => c.cells j (c.head j)) := by
    funext j;exact copy_read x y c j
  have ht : transition (copyState c.state) a=
      (copyState (DescriptorCopy.machine.δ c.state (fun j => c.cells j (c.head j))).1,
        copyAction a (DescriptorCopy.machine.δ c.state (fun j => c.cells j (c.head j))).2) := by
    by_cases h : c.state=DescriptorCopy.machine.qHalt
    · rw [h,DescriptorCopy.machine.halt_fixed]
      change ((none:State),fun i => (a i,Move.stay))=
        (none,copyAction a (fun j => (c.cells j (c.head j),Move.stay)))
      congr 1;funext i;fin_cases i <;> rfl
    · conv_lhs => rw [copyState,if_neg h]
      change (copyState (DescriptorCopy.machine.δ c.state (fun j => a (copyTape j))).1,
        copyAction a (DescriptorCopy.machine.δ c.state (fun j => a (copyTape j))).2)=_
      rw [hread]
  change transition (copyView x y c).state
    (fun i => (copyView x y c).cells i ((copyView x y c).head i))=_ at ht
  apply cfg_ext subroutine
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i p
    fin_cases i
    all_goals first | rfl | (exact congrFun (Function.update_eq_self _ _) p)
  · simp only [MultitapeTM.step,ht];funext i
    fin_cases i <;> rfl

private theorem copy_run (x y : List Bool) (c : DescriptorCopy.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (copyView x y c)=copyView x y (DescriptorCopy.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,copy_step,Function.iterate_succ_apply']
end IntMul.InputParameterBanks

namespace IntMul.InputParameterBanks
open TapeCopy (Sym)
private theorem initial_handoff (x y : List Bool) :
    machine.initCfg x y=FiniteCaller.embed subroutine Bool false false dispatch
      (parameterView (InputCarrySetup.machine.initCfg x y)) := by rfl

private theorem after_parameters (x y : List Bool) :
    FiniteCaller.returned subroutine Bool false false dispatch
      (parameterView (InputCarrySetup.finalFrame x y))=
    FiniteCaller.embed subroutine Bool false true dispatch
      (copyView x y (DescriptorCopy.initialFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y))) := by
  apply cfg_ext machine
  · rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,parameterView,copyView,
      DescriptorCopy.initialFrame,copyBase,copyTape,InputCarrySetup.finalFrame,InputCarrySetup.carryView,
      InputCarrySetup.innerTape,CarryInitialization.finalFrame,CarryInitialization.widthBase,WidthPreparation.finalFrame,
      InputCarrySetup.carryBase,InputCarrySetup.nativeTape,InputArithmeticDescriptors.finalFrame] <;> rfl
  · funext i;fin_cases i <;> simp [FiniteCaller.returned,FiniteCaller.embed,parameterView,copyView,
      DescriptorCopy.initialFrame,copyBase,copyTape,InputCarrySetup.finalFrame,InputCarrySetup.carryView,
      InputCarrySetup.innerTape,CarryInitialization.finalFrame,CarryInitialization.widthBase,WidthPreparation.finalFrame,
      InputCarrySetup.carryBase,InputCarrySetup.nativeTape,InputArithmeticDescriptors.finalFrame] <;> rfl

private theorem final_handoff (x y : List Bool) :
    FiniteCaller.returned subroutine Bool false true dispatch
      (copyView x y (DescriptorCopy.finalFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y)))=
      finalFrame x y := by rfl
end IntMul.InputParameterBanks

namespace IntMul.InputParameterBanks
open TapeCopy (Sym)
private theorem owned_intmulinputparameterbanksprimary_block_word_bound (x y : List Bool) (hp : 0< x.length+y.length) :
    (InputArithmeticDescriptors.blockWord x y).length≤ x.length+y.length := by
  obtain ⟨t,ht,htlin,he,hh,hi,ho,hd,hb,hl,hwd,hzb,hpl,hz,hplsize⟩ :=
    InputArithmeticDescriptors.input_arithmetic_descriptors x y hp
  have hclog : Nat.clog 2 (x.length+y.length)≤ x.length+y.length :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (x.length+y.length).lt_two_pow_self)
  have hB : lg (x.length+y.length)≤ x.length+y.length := max_le hclog (by omega)
  exact hz.trans hB

private theorem setup_parameters (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 87*(x.length+y.length)+114 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.inTape=(machine.initCfg x y).cells machine.inTape ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.outTape=machine.tapeOf [] ∧
      (machine.step^[t] (machine.initCfg x y)).cells 6=
        machine.tapeOf ((InputArithmeticDescriptors.blockWord x y).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 6=0 ∧
      (machine.step^[t] (machine.initCfg x y)).cells 12=
        machine.tapeOf ((bin (3*lg (x.length+y.length)) 0).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 12=0 ∧
      (machine.step^[t] (machine.initCfg x y)).head machine.inTape=x.length+y.length+2 ∧
      (∀ i : Fin 18, i.val=15 ∨ i.val=16 ∨ i.val=17 →
        (machine.step^[t] (machine.initCfg x y)).head i=0) ∧
      val (InputArithmeticDescriptors.widthWord x y)+1=x.length+y.length ∧
      val (InputArithmeticDescriptors.blockWord x y)+1=lg (x.length+y.length) ∧
      val (InputArithmeticDescriptors.precisionWord x y)+1=3*lg (x.length+y.length) ∧
      CarryProduct.coefficientWidth (lg (x.length+y.length)) x y≤ 3*lg (x.length+y.length) := by
  obtain ⟨a,ha,hea,hhalt,hinput,houtput,hzero,hzerohead,hinhead,hparamheads,hd,hb,hl,hN⟩ :=
    InputCarrySetup.input_carry_setup x y hp
  have hparameters : subroutine.step^[a] (parameterView (InputCarrySetup.machine.initCfg x y))=
      parameterView (InputCarrySetup.finalFrame x y) := by rw [parameter_run,hea]
  obtain ⟨b,hbtime,heb⟩ := (FiniteCaller.simulate_run subroutine Bool false false dispatch
    (parameterView (InputCarrySetup.machine.initCfg x y)) a).2 (by rw [hparameters];rfl)
  rw [hparameters,after_parameters] at heb
  have hcopy := (DescriptorCopy.copy_descriptor (copyBase x y) (InputArithmeticDescriptors.blockWord x y)).1
  have hcopyrun : subroutine.step^[2*(InputArithmeticDescriptors.blockWord x y).length+3]
      (copyView x y (DescriptorCopy.initialFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y)))=
      copyView x y (DescriptorCopy.finalFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y)) := by
    rw [copy_run,hcopy]
  obtain ⟨c,hc,hec⟩ := (FiniteCaller.simulate_run subroutine Bool false true dispatch
    (copyView x y (DescriptorCopy.initialFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y)))
      (2*(InputArithmeticDescriptors.blockWord x y).length+3)).2 (by rw [hcopyrun];rfl)
  rw [hcopyrun,final_handoff] at hec
  have he : machine.step^[c+b] (machine.initCfg x y)=finalFrame x y := by
    rw [initial_handoff,Function.iterate_add_apply,heb,hec]
  have hlen := owned_intmulinputparameterbanksprimary_block_word_bound x y hp
  refine ⟨c+b,by omega,he,?_,?_,?_,?_,?_,?_,?_,?_,?_,hd,hb,hl,hN⟩
  all_goals rw [he]
  · rfl
  · change (copyView x y (DescriptorCopy.finalFrame (copyBase x y) (InputArithmeticDescriptors.blockWord x y))).cells 0=_
    change (InputCarrySetup.finalFrame x y).cells 0=(machine.initCfg x y).cells 0
    rw [hea] at hinput;exact hinput
  · change (InputCarrySetup.finalFrame x y).cells 1=machine.tapeOf []
    rw [hea] at houtput;exact houtput
  · simp [finalFrame,copyView,DescriptorCopy.finalFrame,DescriptorCopy.rewindFrame] <;> rfl
  · simp [finalFrame,copyView,DescriptorCopy.finalFrame,DescriptorCopy.rewindFrame]
  · change (InputCarrySetup.finalFrame x y).cells 12=_
    rw [hea] at hzero;exact hzero
  · change (InputCarrySetup.finalFrame x y).head 12=0
    rw [hea] at hzerohead;exact hzerohead
  · change (InputCarrySetup.finalFrame x y).head 0=x.length+y.length+2
    rw [hea] at hinhead;exact hinhead
  · intro i hi
    rcases hi with hi|hi|hi
    · have h : i=(15:Fin 18) := Fin.ext hi
      subst i;change (InputCarrySetup.finalFrame x y).head 15=0
      rw [hea] at hparamheads;exact hparamheads 15 (by decide)
    · have h : i=(16:Fin 18) := Fin.ext hi
      subst i;rfl
    · have h : i=(17:Fin 18) := Fin.ext hi
      subst i;change (InputCarrySetup.finalFrame x y).head 17=0
      rw [hea] at hparamheads;exact hparamheads 17 (by decide)
end IntMul.InputParameterBanks


open IntMul IntMul.InputParameterBanks

theorem solution (x y : List Bool) (hp : 0< x.length+y.length) :
    ∃ t : ℕ, t≤ 87*(x.length+y.length)+114 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.inTape=(machine.initCfg x y).cells machine.inTape ∧
      (machine.step^[t] (machine.initCfg x y)).cells machine.outTape=machine.tapeOf [] ∧
      (machine.step^[t] (machine.initCfg x y)).cells 6=
        machine.tapeOf ((InputArithmeticDescriptors.blockWord x y).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 6=0 ∧
      (machine.step^[t] (machine.initCfg x y)).cells 12=
        machine.tapeOf ((bin (3*lg (x.length+y.length)) 0).map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x y)).head 12=0 ∧
      (machine.step^[t] (machine.initCfg x y)).head machine.inTape=x.length+y.length+2 ∧
      (∀ i : Fin 18, i.val=15 ∨ i.val=16 ∨ i.val=17 →
        (machine.step^[t] (machine.initCfg x y)).head i=0) ∧
      val (InputArithmeticDescriptors.widthWord x y)+1=x.length+y.length ∧
      val (InputArithmeticDescriptors.blockWord x y)+1=lg (x.length+y.length) ∧
      val (InputArithmeticDescriptors.precisionWord x y)+1=3*lg (x.length+y.length) ∧
      CarryProduct.coefficientWidth (lg (x.length+y.length)) x y≤ 3*lg (x.length+y.length) :=
  IntMul.InputParameterBanks.setup_parameters x y hp

#print axioms solution
