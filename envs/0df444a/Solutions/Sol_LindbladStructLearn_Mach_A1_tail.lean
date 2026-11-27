-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:37.135264+00:00
-- url     : https://prove2.me/submissions/7d869d44-87fc-468b-a4d8-b94161445677

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_decode
import Definitions.Def_LindbladStructLearn_alg1Input
import Definitions.Def_LindbladStructLearn_IsChannel
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_pairSupport
import Definitions.Def_LindbladStructLearn_alg1Sample
import Definitions.Def_LindbladStructLearn_Alg1Learner
import Theorems.Thm_LindbladStructLearn_Mach_A1_S2_exec
import Theorems.Thm_LindbladStructLearn_Mach_A1_S3_exec
import Theorems.Thm_LindbladStructLearn_Mach_A1_xEnd_facts

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma mass_succ (N : ℕ) (s : MState) (E : MState → Prop) :
    mass P n evo (N + 1) s E = ((branches P n evo s).map fun b => b.1 * mass P n evo N b.2 E).sum :=
  rfl

lemma reach_succ (N : ℕ) (s s' : MState) :
    Reach P n evo (N + 1) s s' ↔ ∃ b ∈ branches P n evo s, b.1 ≠ 0 ∧ Reach P n evo N b.2 s' :=
  Iff.rfl

/-- a deterministic step: a single branch of weight one -/
lemma mass_det {s s' : MState} (h : branches P n evo s = [(1, s')]) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) s E = mass P n evo N s' E := by
  rw [mass_succ, h]; simp

lemma reach_det {s s' : MState} (h : branches P n evo s = [(1, s')]) (N : ℕ) (x : MState) :
    Reach P n evo (N + 1) s x ↔ Reach P n evo N s' x := by
  rw [reach_succ, h]; simp

/-- iterate deterministic steps -/
lemma mass_det_run (f : MState → MState) (m : ℕ) (s : MState)
    (h : ∀ i < m, branches P n evo (f^[i] s) = [(1, f^[i+1] s)]) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + m) s E = mass P n evo N (f^[m] s) E := by
  induction m generalizing N with
  | zero => rfl
  | succ m ih =>
    rw [show N + (m + 1) = (N + 1) + m by ring, ih (fun i hi => h i (by omega)) (N + 1)]
    exact mass_det (h m (by omega)) N E

lemma reach_det_run (f : MState → MState) (m : ℕ) (s : MState)
    (h : ∀ i < m, branches P n evo (f^[i] s) = [(1, f^[i+1] s)]) (N : ℕ) (x : MState) :
    Reach P n evo (N + m) s x ↔ Reach P n evo N (f^[m] s) x := by
  induction m generalizing N with
  | zero => rfl
  | succ m ih =>
    rw [show N + (m + 1) = (N + 1) + m by ring, ih (fun i hi => h i (by omega)) (N + 1)]
    exact reach_det (h m (by omega)) N x

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma branches_det (P : Program) (s : MState) (ins : Instr) (hpc : P[s.core.pc]? = some ins)
    (hdet : IsDet ins) (hout : s.output = none) :
    branches P n evo s = [(1, dstep P s)] := by
  unfold branches dstep
  simp only [hout, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [hpc]
  cases ins <;> simp_all [IsDet]

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma DetRun.single {s : MState} {ins : Instr} (hpc : P[s.core.pc]? = some ins) (hdet : IsDet ins)
    (hout : s.output = none) : DetRun P 1 s (dstep P s) :=
  ⟨fun i hi => by
    have : i = 0 := by omega
    subst this; exact ⟨hout, ins, hpc, hdet⟩, rfl⟩

lemma DetRun.trans {m1 m2 : ℕ} {s1 s2 s3 : MState} (h1 : DetRun P m1 s1 s2)
    (h2 : DetRun P m2 s2 s3) : DetRun P (m1 + m2) s1 s3 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases hi1 : i < m1
    · exact h1a i hi1
    · have := h2a (i - m1) (by omega)
      rw [← h1b, ← Function.iterate_add_apply, show i - m1 + m1 = i by omega] at this
      exact this
  · rw [add_comm, Function.iterate_add_apply, h1b, h2b]

lemma DetRun.mass {m : ℕ} {s s' : MState} (h : DetRun P m s s') (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + m) s E = mass P n evo N s' E := by
  rw [← h.2]
  apply mass_det_run (dstep P) m s
  intro i hi
  obtain ⟨hout, ins, hpc, hdet⟩ := h.1 i hi
  rw [Function.iterate_succ_apply']
  exact branches_det P _ ins hpc hdet hout

lemma DetRun.reach {m : ℕ} {s s' : MState} (h : DetRun P m s s') (N : ℕ) (x : MState) :
    Reach P n evo (N + m) s x ↔ Reach P n evo N s' x := by
  rw [← h.2]
  apply reach_det_run (dstep P) m s
  intro i hi
  obtain ⟨hout, ins, hpc, hdet⟩ := h.1 i hi
  rw [Function.iterate_succ_apply']
  exact branches_det P _ ins hpc hdet hout

lemma dstep_work {s : MState} {ins : Instr} (hpc : P[s.core.pc]? = some ins) (hdet : IsDet ins) :
    (dstep P s).work = s.work + 1 := by
  unfold dstep; rw [hpc]
  cases ins <;> simp_all [IsDet]

lemma dstep_output {s : MState} {ins : Instr} (hpc : P[s.core.pc]? = some ins) (hdet : IsDet ins) :
    (dstep P s).output = s.output := by
  unfold dstep; rw [hpc]
  cases ins <;> simp_all [IsDet]

lemma dstep_durations {s : MState} {ins : Instr} (hpc : P[s.core.pc]? = some ins) (hdet : IsDet ins) :
    (dstep P s).durations = s.durations := by
  unfold dstep; rw [hpc]
  cases ins <;> simp_all [IsDet]

lemma iter_props (s : MState) (m : ℕ)
    (h1 : ∀ i < m, ((dstep P)^[i] s).output = none ∧
      ∃ ins, P[((dstep P)^[i] s).core.pc]? = some ins ∧ IsDet ins) :
    ((dstep P)^[m] s).work = s.work + m ∧ ((dstep P)^[m] s).durations = s.durations ∧
      ((dstep P)^[m] s).output = s.output := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ha, hb, hc⟩ := ih (fun i hi => h1 i (by omega))
    obtain ⟨_, ins, hpc, hdet⟩ := h1 m (by omega)
    rw [Function.iterate_succ_apply', dstep_work hpc hdet, dstep_durations hpc hdet,
      dstep_output hpc hdet, ha, hb, hc]
    exact ⟨by ring, rfl, rfl⟩

lemma DetRun.work {m : ℕ} {s s' : MState} (h : DetRun P m s s') : s'.work = s.work + m := by
  rw [← h.2]; exact (iter_props s m h.1).1

lemma DetRun.durations {m : ℕ} {s s' : MState} (h : DetRun P m s s') :
    s'.durations = s.durations := by
  rw [← h.2]; exact (iter_props s m h.1).2.1

lemma DetRun.output {m : ℕ} {s s' : MState} (h : DetRun P m s s') :
    s'.output = s.output := by
  rw [← h.2]; exact (iter_props s m h.1).2.2

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program}

lemma core_fetch {s : MState} {ins : RAMInstr} (h : P[s.core.pc]? = some (.core ins)) :
    (coreProgram P)[s.core.pc]? = some ins := by
  unfold coreProgram; rw [List.getElem?_map, h]; rfl

lemma dstep_core {s : MState} {ins : RAMInstr} (h : P[s.core.pc]? = some (.core ins)) :
    dstep P s = ⟨RAMStep (coreProgram P) s.core, s.intMem, s.output, s.durations, s.work + 1⟩ := by
  unfold dstep; rw [h]

lemma ds_pjle_t {s : MState} {q q' t : ℕ} (h : P[s.core.pc]? = some (.core (.pjle q q' t)))
    (hc : s.core.ptrs q ≤ s.core.ptrs q') :
    dstep P s = ⟨⟨t, s.core.regs, s.core.ptrs, s.core.mem⟩, s.intMem, s.output, s.durations, s.work + 1⟩ := by
  rw [dstep_core h]; unfold RAMStep; simp [core_fetch h, hc]

lemma ds_pjle_f {s : MState} {q q' t : ℕ} (h : P[s.core.pc]? = some (.core (.pjle q q' t)))
    (hc : ¬ s.core.ptrs q ≤ s.core.ptrs q') :
    dstep P s = ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, s.intMem, s.output, s.durations, s.work + 1⟩ := by
  rw [dstep_core h]; unfold RAMStep; simp [core_fetch h, hc]

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma branches_halt {s : MState} {a : ℕ} (h : P[s.core.pc]? = some (.halt a)) (hout : s.output = none) :
    branches P n evo s = [(1, haltSt s a)] := by
  unfold branches; simp only [hout, Option.isSome_none, Bool.false_eq_true, if_false]; rw [h]
  simp only [haltSt]

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma Plain.isDet {i : Instr} (h : Plain i) : IsDet i := by
  rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Plain, IsDet]

lemma dstep_plain {P : Program} {s : MState} {i : Instr} (hf : P[s.core.pc]? = some i)
    (hp : Plain i) : dstep P s = setpc (ains i s) (s.core.pc + 1) := by
  unfold dstep; rw [hf]
  rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
  · rcases ins <;> simp_all [Plain, ains, setpc, RAMStep, core_fetch hf]
  all_goals simp_all [Plain, ains, setpc]

lemma ains_setpc (i : Instr) (s : MState) (a : ℕ) : ains i (setpc s a) = setpc (ains i s) a := by
  rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
  · rcases ins <;> rfl
  all_goals rfl

lemma setpc_setpc (s : MState) (a b : ℕ) : setpc (setpc s a) b = setpc s b := rfl

@[simp] lemma setpc_pc (s : MState) (a : ℕ) : (setpc s a).core.pc = a := rfl
@[simp] lemma setpc_ptrs (s : MState) (a : ℕ) : (setpc s a).core.ptrs = s.core.ptrs := rfl
@[simp] lemma setpc_output (s : MState) (a : ℕ) : (setpc s a).output = s.output := rfl

lemma ains_output (i : Instr) (s : MState) : (ains i s).output = s.output := by
  rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
  · rcases ins <;> rfl
  all_goals rfl

lemma Stmt.comp_length (st : Stmt) (base : ℕ) : (st.comp base).length = st.len := by
  induction st generalizing base with
  | ins i => rfl
  | seq a b iha ihb => simp [Stmt.comp, Stmt.len, iha, ihb]
  | loop x y b ih => simp [Stmt.comp, Stmt.len, ih]
  | ite x y a b iha ihb => simp [Stmt.comp, Stmt.len, iha, ihb]; try ring

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program}

lemma Placed.left {base : ℕ} {l1 l2 : List Instr} (h : Placed P base (l1 ++ l2)) : Placed P base l1 := by
  intro i hi
  rw [h i (by simp; omega), List.getElem?_append_left hi]

lemma Placed.right {base : ℕ} {l1 l2 : List Instr} (h : Placed P base (l1 ++ l2)) :
    Placed P (base + l1.length) l2 := by
  intro i hi
  rw [add_assoc, h (l1.length + i) (by simp; omega), List.getElem?_append_right (by omega)]
  simp

lemma Placed.head {base : ℕ} {i : Instr} {l : List Instr} (h : Placed P base (i :: l)) :
    P[base]? = some i := by
  have := h 0 (by simp); simpa using this

lemma Exec.output {st : Stmt} {s s' : MState} {m : ℕ} (h : Exec st s s' m) : s'.output = s.output := by
  induction h with
  | ins i s _ => exact ains_output i s
  | seq _ _ ih1 ih2 => rw [ih2, ih1]
  | loopDone _ => rfl
  | loopStep _ _ _ ih1 ih2 => rw [ih2]; exact ih1
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih

lemma Exec.work {st : Stmt} {s s' : MState} {m : ℕ} (h : Exec st s s' m) : s'.work = s.work + m := by
  induction h with
  | ins i s hp =>
    rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
    · rcases ins <;> first | rfl | exact absurd hp id
    all_goals first | rfl | exact absurd hp id
  | seq _ _ ih1 ih2 => rw [ih2, ih1]; ring
  | loopDone _ => rfl
  | loopStep _ _ _ ih1 ih2 => rw [ih2]; simp only [tick] at ih1 ⊢; rw [ih1]; ring
  | iteT _ _ ih => rw [ih]; simp only [tick]; ring
  | iteF _ _ ih => simp only [tick]; rw [ih]; simp only [tick]; ring

lemma Exec.durations {st : Stmt} {s s' : MState} {m : ℕ} (h : Exec st s s' m) :
    s'.durations = s.durations := by
  induction h with
  | ins i s hp =>
    rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
    · rcases ins <;> first | rfl | exact absurd hp id
    all_goals first | rfl | exact absurd hp id
  | seq _ _ ih1 ih2 => rw [ih2, ih1]
  | loopDone _ => rfl
  | loopStep _ _ _ ih1 ih2 => rw [ih2]; exact ih1
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih

lemma getElem?_cons_append_last {α : Type*} (a j : α) (l : List α) :
    (a :: (l ++ [j]))[1 + l.length]? = some j := by
  rw [add_comm, List.getElem?_cons_succ, List.getElem?_append_right le_rfl]; simp

lemma getElem?_cons_append_mid {α : Type*} (a j : α) (l r : List α) :
    (a :: (l ++ j :: r))[1 + l.length]? = some j := by
  rw [add_comm, List.getElem?_cons_succ, List.getElem?_append_right le_rfl]; simp

lemma pjle_t' {s : MState} {a x y t : ℕ} (hf : P[(setpc s a).core.pc]? = some (.core (.pjle x y t)))
    (hc : s.core.ptrs x ≤ s.core.ptrs y) : dstep P (setpc s a) = setpc (tick s) t := by
  rw [ds_pjle_t hf hc]; rfl

lemma pjle_f' {s : MState} {a x y t : ℕ} (hf : P[(setpc s a).core.pc]? = some (.core (.pjle x y t)))
    (hc : ¬ s.core.ptrs x ≤ s.core.ptrs y) : dstep P (setpc s a) = setpc (tick s) (a + 1) := by
  rw [ds_pjle_f hf hc]; rfl

theorem Exec.detRun {st : Stmt} {s s' : MState} {m : ℕ} (h : Exec st s s' m) :
    ∀ base, Placed P base (st.comp base) → st.WF → s.output = none →
      DetRun P m (setpc s base) (setpc s' (base + st.len)) := by
  induction h with
  | ins i s hp =>
    intro base hP hwf hout
    have hf : P[(setpc s base).core.pc]? = some i := hP.head
    have := DetRun.single hf (Plain.isDet hwf) hout
    rw [dstep_plain hf hwf, ains_setpc, setpc_setpc] at this
    simpa [Stmt.len] using this
  | @seq a b s s1 s2 m1 m2 h1 h2 ih1 ih2 =>
    intro base hP hwf hout
    have hP1 := hP.left
    have hP2 := hP.right
    rw [Stmt.comp_length] at hP2
    have r1 := ih1 base hP1 hwf.1 hout
    have r2 := ih2 (base + a.len) hP2 hwf.2 (by rw [h1.output]; exact hout)
    have := r1.trans r2
    simpa [Stmt.len, add_assoc] using this
  | @loopDone x y b s hc =>
    intro base hP hwf hout
    have hf : P[(setpc s base).core.pc]? = some (.core (.pjle x y (base + b.len + 2))) := by
      simp only [setpc_pc]; exact hP.head
    have := DetRun.single hf trivial hout
    rw [pjle_t' hf hc] at this
    simpa [Stmt.len, add_assoc] using this
  | @loopStep x y b s s1 s2 m1 m2 hc h1 h2 ih1 ih2 =>
    intro base hP hwf hout
    have hf : P[(setpc s base).core.pc]? = some (.core (.pjle x y (base + b.len + 2))) := by
      simp only [setpc_pc]; exact hP.head
    have r0 := DetRun.single hf trivial hout
    rw [pjle_f' hf hc] at r0
    have hPb : Placed P (base + 1) (b.comp (base + 1)) := by
      have := (hP.left (l2 := [.core (.pjle 0 0 base)])).right (l1 := [_])
      simpa using this
    have r1 := ih1 (base + 1) hPb hwf (by simpa [tick] using hout)
    have hfj : P[(setpc s1 (base + 1 + b.len)).core.pc]? = some (.core (.pjle 0 0 base)) := by
      have := hP (1 + b.len) (by rw [Stmt.comp_length]; simp [Stmt.len]; omega)
      simp only [setpc_pc]; rw [← add_assoc] at this; rw [this]
      simp only [Stmt.comp, List.singleton_append, List.cons_append]
      rw [← Stmt.comp_length b (base + 1)]
      exact getElem?_cons_append_last _ _ _
    have hout1 : s1.output = none := by rw [h1.output]; simpa [tick] using hout
    have r2 := DetRun.single hfj trivial hout1
    rw [pjle_t' hfj le_rfl] at r2
    have r3 := ih2 base hP hwf (by simpa [tick] using hout1)
    have := ((r0.trans r1).trans (by simpa [setpc, tick] using r2)).trans r3
    simpa [add_comm, add_assoc, add_left_comm] using this
  | @iteT x y a b s s1 m hc h1 ih =>
    intro base hP hwf hout
    have hf : P[(setpc s base).core.pc]? = some (.core (.pjle x y (base + b.len + 2))) := by
      simp only [setpc_pc]; exact hP.head
    have r0 := DetRun.single hf trivial hout
    rw [pjle_t' hf hc] at r0
    have hPa : Placed P (base + b.len + 2) (a.comp (base + b.len + 2)) := by
      have := hP.right (l1 := [.core (.pjle x y (base + b.len + 2))] ++ b.comp (base + 1) ++
        [.core (.pjle 0 0 (base + a.len + b.len + 2))])
      have e : base + ([Instr.core (RAMInstr.pjle x y (base + b.len + 2))] ++ b.comp (base + 1) ++
          [Instr.core (RAMInstr.pjle 0 0 (base + a.len + b.len + 2))]).length = base + b.len + 2 := by
        simp [Stmt.comp_length]; ring
      rw [e] at this
      exact this
    have r1 := ih (base + b.len + 2) hPa hwf.1 (by simpa [tick] using hout)
    have := r0.trans r1
    simpa [Stmt.len, add_comm, add_assoc, add_left_comm] using this
  | @iteF x y a b s s1 m hc h1 ih =>
    intro base hP hwf hout
    have hf : P[(setpc s base).core.pc]? = some (.core (.pjle x y (base + b.len + 2))) := by
      simp only [setpc_pc]; exact hP.head
    have r0 := DetRun.single hf trivial hout
    rw [pjle_f' hf hc] at r0
    have hPb : Placed P (base + 1) (b.comp (base + 1)) := by
      have := ((hP.left (l2 := a.comp (base + b.len + 2))).left
        (l2 := [.core (.pjle 0 0 (base + a.len + b.len + 2))])).right (l1 := [_])
      simpa using this
    have r1 := ih (base + 1) hPb hwf.2 (by simpa [tick] using hout)
    have hfj : P[(setpc s1 (base + 1 + b.len)).core.pc]? =
        some (.core (.pjle 0 0 (base + a.len + b.len + 2))) := by
      have := hP (1 + b.len) (by rw [Stmt.comp_length]; simp [Stmt.len]; omega)
      simp only [setpc_pc]; rw [← add_assoc] at this; rw [this]
      simp only [Stmt.comp, List.singleton_append, List.cons_append, List.append_assoc,
        List.nil_append]
      rw [← Stmt.comp_length b (base + 1)]
      exact getElem?_cons_append_mid _ _ _ _
    have hout1 : s1.output = none := by rw [h1.output]; simpa [tick] using hout
    have r2 := DetRun.single hfj trivial hout1
    rw [pjle_t' hfj le_rfl] at r2
    have := (r0.trans r1).trans r2
    simpa [Stmt.len, setpc, tick, add_comm, add_assoc, add_left_comm] using this

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

namespace A1
-- short names
lemma S0_len (k : ℕ) : (S0 k).len = 71 := by
  simp [S0, seqs, tableEntries, Stmt.len, iload, pset, padd, istore, rconst, preal, rdiv]
lemma S2_len (k : ℕ) : (S2 k).len = 95 := by
  simp [S2, body2, copyBody, validBody, within, beyond, inval, odoBody, seqs, Stmt.len, iload, pset,
    padd, istore, pinc, pdec, pcopy, skip]
lemma S3_len (k : ℕ) : (S3 k).len = 106 := by
  simp [S3, body3, core3, sampBody, siteBody, caseE, seqs, Stmt.len, iload, pset, padd, psub, istore, pinc,
    rconst, rmul, radd, rsub, rstore, skip]

end A1
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma prog_eq (k : ℕ) : prog k = (S0 k).comp 0 ++ (S1 71 ++ ((S2 k).comp 96 ++ ((S3 k).comp 191 ++
    [.halt 12]))) := by
  simp [prog, a1, a2, a3, S0_len, S2_len, List.append_assoc]

lemma placed_S2 (k : ℕ) : Placed (prog k) 96 ((S2 k).comp 96) := by
  intro i hi
  have h1 : (S1 71).length = 25 := rfl
  rw [prog_eq, List.getElem?_append_right (by rw [Stmt.comp_length, S0_len]; omega),
    Stmt.comp_length, S0_len, List.getElem?_append_right (by rw [h1]; omega), h1,
    show 96 + i - 71 - 25 = i by omega, List.getElem?_append_left hi]

lemma placed_S3 (k : ℕ) : Placed (prog k) 191 ((S3 k).comp 191) := by
  intro i hi
  have h1 : (S1 71).length = 25 := rfl
  rw [prog_eq, List.getElem?_append_right (by rw [Stmt.comp_length, S0_len]; omega),
    Stmt.comp_length, S0_len, List.getElem?_append_right (by rw [h1]; omega), h1,
    List.getElem?_append_right (by rw [Stmt.comp_length, S2_len]; omega), Stmt.comp_length, S2_len,
    show 191 + i - 71 - 25 - 95 = i by omega, List.getElem?_append_left hi]

lemma fetch_halt (k : ℕ) : (prog k)[297]? = some (.halt 12) := by
  have h1 : (S1 71).length = 25 := rfl
  rw [prog_eq, List.getElem?_append_right (by rw [Stmt.comp_length, S0_len]; omega),
    Stmt.comp_length, S0_len, List.getElem?_append_right (by rw [h1]; omega), h1,
    List.getElem?_append_right (by rw [Stmt.comp_length, S2_len]; omega), Stmt.comp_length, S2_len,
    List.getElem?_append_right (by rw [Stmt.comp_length, S3_len]), Stmt.comp_length, S3_len]
  rfl

lemma wf_S2 (k : ℕ) : (S2 k).WF := by
  simp [S2, body2, copyBody, validBody, within, beyond, inval, odoBody, seqs, Stmt.WF, iload, pset,
    padd, istore, pinc, pdec, pcopy, skip, Plain]

lemma wf_S3 (k : ℕ) : (S3 k).WF := by
  simp [S3, body3, core3, sampBody, siteBody, caseE, seqs, Stmt.WF, iload, pset, padd, psub, istore, pinc,
    rconst, rmul, radd, rsub, rstore, skip, Plain]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

@[simp] lemma cset_output (s : MState) (d : ℕ) (c : ℤ) : (cset s d c).output = s.output := rfl
@[simp] lemma tick_output (s : MState) : (tick s).output = s.output := rfl
@[simp] lemma ains_output' (i : Instr) (s : MState) : (ains i s).output = s.output := ains_output i s

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma Same.trans {s t u : MState} (h1 : Same s t) (h2 : Same t u) : Same s u :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩
lemma Same.tick {s t : MState} (h : Same s t) : Same s (tick t) := h

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

@[simp] lemma tick_core (s : MState) : (tick s).core = s.core := rfl
@[simp] lemma tick_intMem (s : MState) : (tick s).intMem = s.intMem := rfl
@[simp] lemma tick_work (s : MState) : (tick s).work = s.work + 1 := rfl
@[simp] lemma tick_durations (s : MState) : (tick s).durations = s.durations := rfl

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn

end LindbladStructLearn.Rec

namespace LindbladStructLearn.Rec

end LindbladStructLearn.Rec

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Rec
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Mach.A1

variable {k n : ℕ} {D : ℕ → ℕ}

end LindbladStructLearn.Rec

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma RegFix.trans {s t u : MState} {S : Finset ℕ} (h1 : RegFix s t S) (h2 : RegFix t u S) : RegFix s u S :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    fun q hq => (h2.2.2.2 q hq).trans (h1.2.2.2 q hq)⟩

lemma RegFix.tick {s t : MState} {S : Finset ℕ} (h : RegFix s t S) : RegFix s (tick t) S := h

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma tail (k M : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (G : Fin M → Rd n) :
    ∃ H : MState, ∃ m : ℕ, m ≤ Kc k n * (130 * k + 62) + 5 + (Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3) + 1 ∧
      (∀ N E, mass (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) E = mass (prog k) n evo N H E) ∧
      (∀ N x, Reach (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) x ↔ Reach (prog k) n evo N H x) ∧
      Halted H ∧ H.output = some (pEnd k n M) ∧ H.durations = List.replicate M 0 ∧
      H.work = (xEnd k n M ε δ G).work + m ∧
      H.intMem (pEnd k n M) = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, H.intMem (recAddr k (pEnd k n M) j + i) = recCell k n j i) ∧
      (∀ j < Kc k n, validD k (Dseq k n j) →
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1)) = (tsum k n M G j).re * (1 / M) ∧
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1) + 1) = (tsum k n M G j).im * (1 / M)) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20⟩ :=
    xEnd_facts k n M ε δ G
  set x := xEnd k n M ε δ G
  set p := pEnd k n M
  have hp : cDIG k + 3 * k < p := by
    simp only [p, pEnd, cSAMP, cDIG]; have : (0 : ℤ) ≤ 4 * n * M := by positivity
    omega
  obtain ⟨s2, m2, e2, hm2, ssame, sptr, s14, sp, srec, smem⟩ := S2_exec k n hn x p x4 x8 x9 x14 x11 x10 x18 hp
  have f2 : ∀ q, q ∉ scr2 → s2.core.ptrs q = x.core.ptrs q := sptr
  have hsm : SampMem k n M G s2.intMem := by
    intro i y
    have hi := i.isLt; have hy := y.isLt
    have lo : ∀ c : ℤ, 0 ≤ c → c < 4 * n → cDIG k + 3 * k < cSAMP k + 4 * n * i + c := by
      intro c _ _; unfold cSAMP cDIG; have : (0 : ℤ) ≤ 4 * n * i := by positivity
      omega
    have hi' : ∀ c : ℤ, c < 4 * n → cSAMP k + 4 * n * i + c < p := by
      intro c hc; simp only [p, pEnd]
      have h1 : (i : ℤ) + 1 ≤ M := by exact_mod_cast hi
      have h2 : (4 * n : ℤ) * (i + 1) ≤ 4 * n * M := mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    obtain ⟨e1, e2', e3, e4⟩ := x20 i y
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [smem _ (Or.inr (lo _ (by positivity) (by push_cast; omega))) (hi' _ (by push_cast; omega))]; exact e1
    · rw [smem _ (Or.inr (lo _ (by positivity) (by push_cast; omega))) (hi' _ (by push_cast; omega))]; exact e2'
    · rw [smem _ (Or.inr (lo _ (by positivity) (by push_cast; omega))) (hi' _ (by push_cast; omega))]; exact e3
    · rw [smem _ (Or.inr (lo _ (by positivity) (by push_cast; omega))) (hi' _ (by push_cast; omega))]; exact e4
  have hpS : cSAMP k ≤ p := by
    simp only [p, pEnd]; have : (0 : ℤ) ≤ 4 * n * M := by positivity
    omega
  have htab : Tab s2.intMem := by
    intro a b
    have := x19 a b
    have ha := a.isLt; have hb := b.isLt
    have c1 : (4 : ℤ) + 4 * (a : ℕ) + (b : ℕ) < p := by
      have : (4 : ℤ) + 4 * (a : ℕ) + (b : ℕ) < cSAMP k := by unfold cSAMP; push_cast; omega
      omega
    have c2 : (20 : ℤ) + 4 * (a : ℕ) + (b : ℕ) < p := by
      have : (20 : ℤ) + 4 * (a : ℕ) + (b : ℕ) < cSAMP k := by unfold cSAMP; push_cast; omega
      omega
    rw [smem _ (Or.inl (by unfold cDIG; push_cast; omega)) c1,
      smem _ (Or.inl (by unfold cDIG; push_cast; omega)) c2]
    exact this
  obtain ⟨s3, m3, e3, hm3, o1, o2, o3, o12, ov⟩ := S3_exec s2 k n M hn G p
    (by rw [f2 10 (by simp [scr2]), x8]) (by rw [f2 11 (by simp [scr2]), x9])
    (by rw [f2 45 (by simp [scr2]), x13]) (by rw [f2 43 (by simp [scr2]), x12])
    (by rw [f2 47 (by simp [scr2]), x15]) (by rw [f2 46 (by simp [scr2]), x14])
    (by rw [f2 0 (by simp [scr2]), x4]) (by rw [f2 2 (by simp [scr2]), x6])
    (by rw [f2 1 (by simp [scr2]), x5]) (by rw [f2 18 (by simp [scr2]), x11])
    (by rw [f2 12 (by simp [scr2]), x10]) s14 (by rw [ssame.2.2.1, x16]) htab srec hsm
  have d2 := e2.detRun (P := prog k) 96 (placed_S2 k) (wf_S2 k) x1
  have hout2 : s2.output = none := by rw [ssame.1, x1]
  have d3 := e3.detRun (P := prog k) 191 (by simpa using placed_S3 k) (wf_S3 k) hout2
  rw [S2_len] at d2
  rw [S3_len] at d3
  have d := d2.trans d3
  have hout3 : s3.output = none := by rw [o1, hout2]
  have hb := branches_halt (P := prog k) (n := n) (evo := evo) (s := setpc s3 297) (a := 12) (fetch_halt k) hout3
  refine ⟨haltSt (setpc s3 297) 12, m2 + m3 + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N E
    rw [show N + (m2 + m3 + 1) = (N + 1) + (m2 + m3) by ring, d.mass, mass_det hb]
  · intro N y
    rw [show N + (m2 + m3 + 1) = (N + 1) + (m2 + m3) by ring, d.reach, reach_det hb]
  · simp [Halted, haltSt]
  · simp only [haltSt, setpc]; rw [o12]
  · simp only [haltSt, setpc]; rw [o2, ssame.2.1, x2]
  · simp only [haltSt, setpc]
    have := d.work; simp only [setpc] at this; omega
  · simp only [haltSt, setpc]; rw [o3, sp]
  · intro j hj i hi; simp only [haltSt, setpc]; rw [o3]; exact srec j hj i hi
  · intro j hj hv; simp only [haltSt, setpc]
    obtain ⟨v1, v2⟩ := ov j hj hv
    rw [v1, v2, ssame.2.2.1, x17]; exact ⟨rfl, rfl⟩

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.FourierAux
open LindbladTolerant.Testing LindbladStructLearn

end LindbladStructLearn.FourierAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

end LindbladStructLearn.AAux

namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

end LindbladStructLearn.AAux

namespace LindbladStructLearn

open LindbladTolerant.Testing LindbladStructLearn.FourierAux LindbladStructLearn.AAux

variable {n : ℕ}

end LindbladStructLearn

namespace LindbladStructLearn.Hoeff

open Classical


variable {X : Type*} [Fintype X]

end LindbladStructLearn.Hoeff

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1


open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.Mach LindbladStructLearn.Mach.A1 SmaleNinth LindbladStructLearn.Rec in
theorem solution : ∀ {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k M : ℕ) (hn : 1 ≤ n) (ε δ : ℝ) (G : Fin M → Rd n),
    ∃ H : MState, ∃ m : ℕ, m ≤ Kc k n * (130 * k + 62) + 5 + (Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3) + 1 ∧
      (∀ N E, mass (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) E = mass (prog k) n evo N H E) ∧
      (∀ N x, Reach (prog k) n evo (N + m) (setpc (xEnd k n M ε δ G) 96) x ↔ Reach (prog k) n evo N H x) ∧
      Halted H ∧ H.output = some (pEnd k n M) ∧ H.durations = List.replicate M 0 ∧
      H.work = (xEnd k n M ε δ G).work + m ∧
      H.intMem (pEnd k n M) = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, H.intMem (recAddr k (pEnd k n M) j + i) = recCell k n j i) ∧
      (∀ j < Kc k n, validD k (Dseq k n j) →
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1)) = (tsum k n M G j).re * (1 / M) ∧
        H.core.mem (recAddr k (pEnd k n M) j + (3 * k + 1) + 1) = (tsum k n M G j).im * (1 / M)) :=
  @LindbladStructLearn.Mach.A1.tail
