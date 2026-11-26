-- Prove2me | solution 1 for Leakage.not_ct_subroutine_ok_branch_on_secret_byte
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T23:57:34.118879+00:00
-- url     : https://prove2.me/submissions/b8959973-14fb-495e-9188-d419a33805c5

import Definitions.Def_Arm64_Leakage
open Arm64 Leakage

/-! Counterexample: two entry states differing only in the secret byte at `x0` (0 vs 1);
the branch on it makes the third observation's pc differ (0x1000c vs 0x10008). -/

namespace CtBranchByte

def P : Program := Program.ofWords 0x10000#64 [0x39400001#32, 0x34000041#32, 0xd503201f#32, 0xd65f03c0#32]

def mem (v : BitVec 8) : Memory :=
  Memory.ofFn
    (fun a => if a = 0x20000#64 then v else if (a - 0x10000#64).toNat < 16 then P.code.getD (a - 0x10000#64).toNat 0 else 0)
    (fun a => if a = 0x20000#64 then some Perm.rw else if (a - 0x10000#64).toNat < 16 then some Perm.rx else none)

def st (v : BitVec 8) : State :=
  { regs := ⟨fun i => if i = 0#5 then 0x20000#64 else if i = 30#5 then 0x50000#64 else 0#64⟩,
    sp := 0x40000#64, pc := 0x10000#64, mem := mem v }

theorem codeLoaded0 : P.CodeLoaded (st 0).mem := by
  unfold Program.CodeLoaded
  decide
theorem codeLoaded1 : P.CodeLoaded (st 1).mem := by
  unfold Program.CodeLoaded
  decide

theorem disj_empty (h : Heap) : h.Disjoint Heap.empty :=
  ⟨fun _ => Or.inr (Or.inl rfl), fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl,
   fun _ _ _ _ hh => hh.elim (fun ⟨_, h2⟩ => nomatch h2) (fun ⟨h1, _⟩ => nomatch h1),
   fun _ => Or.inr rfl⟩

theorem sat (v : BitVec 8) :
    (st v).mem ⊨ ((st v).readReg64 Reg.x0 ↦ₛ [v]) ∗ emp := by
  unfold SepProp.Satisfies pointsToBytes
  refine ⟨(((Heap.singleton 0x20000#64 v).union Heap.empty).union Heap.empty), ?_, ?_⟩
  · have hx : (st v).readReg64 Reg.x0 = 0x20000#64 := rfl
    rw [hx]
    exact ⟨_, Heap.empty, disj_empty _, rfl,
      ⟨_, Heap.empty, disj_empty _, rfl, rfl, rfl⟩, rfl⟩
  · refine ⟨?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ h => nomatch h⟩
    intro a c h
    simp only [Heap.union, Heap.singleton, Heap.empty] at h
    by_cases ha : a = 0x20000#64
    · subst ha
      simp at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · simp [ha] at h

theorem step_det {s s' : State} {i : Instr} (h : P.fetchMem s.mem s.pc = some i)
    (hs : Step P s s') : s' = P.evalInst i s := by
  cases hs with
  | exec _ hf => rw [hf] at h; cases h; rfl
  | halt_unmapped _ hf _ => rw [hf] at h; cases h
  | externHook _ he _ _ => simp [Program.fetchMem, he] at h
  | extern_fault _ he _ => simp [Program.fetchMem, he] at h

theorem obs_cons {ar : String → Nat} {stop : State → Prop} {s f : State} {o : Obs} {t : List Obs}
    (h : ObsUntil P ar stop s (o :: t) f) :
    ∃ s', Step P s s' ∧ o = stepObs P ar s ∧ ObsUntil P ar stop s' t f := by
  cases h with
  | step _ hs hr => exact ⟨_, hs, rfl, hr⟩

def iLdr : Instr := .ldr .W32 .B8 false (.gpr 1#5) (.Offset (.gpr 0#5) 0#64)
def iCbz : Instr := .cbz .W32 false (.gpr 1#5) 8#64
def iNop : Instr := .nop
def iRet : Instr := .ret (.gpr 30#5)

def a1 : State := P.evalInst iLdr (st 0)
def a2 : State := P.evalInst iCbz a1
def a3 : State := P.evalInst iRet a2
def b1 : State := P.evalInst iLdr (st 1)
def b2 : State := P.evalInst iCbz b1

theorem f_a0 : P.fetchMem (st 0).mem (st 0).pc = some iLdr := by decide
theorem f_a1 : P.fetchMem a1.mem a1.pc = some iCbz := by decide
theorem f_a2 : P.fetchMem a2.mem a2.pc = some iRet := by decide
theorem f_b0 : P.fetchMem (st 1).mem (st 1).pc = some iLdr := by decide
theorem f_b1 : P.fetchMem b1.mem b1.pc = some iCbz := by decide

theorem not_stop {s : State} (hpc : s.pc ≠ 0x50000#64) (hst : s.status = .Running) :
    ¬ SubroutineStop (st 0) s := by
  intro h
  rcases h with h | h | ⟨_, h⟩ | h
  · exact hpc h.1
  all_goals (rw [hst] at h; cases h)

end CtBranchByte

open CtBranchByte

theorem Leakage.not_ct_subroutine_ok_branch_on_secret_byte :
    ¬ ct_subroutine_ok
      (Program.ofWords 0x10000#64 [0x39400001#32, 0x34000041#32, 0xd503201f#32, 0xd65f03c0#32])
      (fun _ => 0) 0x10000#64
      ({ pre := fun b s => s.readReg64 Reg.x0 ↦ₛ [b], post := fun _ _ _ => ⌜True⌝ } : Spec (BitVec 8))
      (fun _ _ => True) := by
  intro H
  have hE := H 0 1 emp emp (st 0) (st 1) ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ codeLoaded0 codeLoaded1
    (sat 0) (sat 1) rfl trivial
  have hrun : ObsUntil P (fun _ => 0) (SubroutineStop (st 0)) (st 0)
      [stepObs P (fun _ => 0) (st 0), stepObs P (fun _ => 0) a1, stepObs P (fun _ => 0) a2] a3 :=
    .step (not_stop (by decide) (by decide)) (.exec rfl f_a0)
      (.step (not_stop (by decide) (by decide)) (.exec (by decide) f_a1)
        (.step (not_stop (by decide) (by decide)) (.exec (by decide) f_a2) (.refl _)))
  obtain ⟨f₂, h₂, -⟩ := hE.1 _ _ hrun
  obtain ⟨s₁, hs₁, -, h₂⟩ := obs_cons h₂
  cases step_det f_b0 hs₁
  obtain ⟨s₂, hs₂, -, h₂⟩ := obs_cons h₂
  cases step_det f_b1 hs₂
  obtain ⟨_, _, ho, _⟩ := obs_cons h₂
  exact absurd (congrArg Prod.fst ho) (by decide)

theorem solution : type_of% @Leakage.not_ct_subroutine_ok_branch_on_secret_byte := @Leakage.not_ct_subroutine_ok_branch_on_secret_byte
