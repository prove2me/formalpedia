-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.S0_run
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:33.922902+00:00
-- url     : https://prove2.me/submissions/fcf53a31-72fa-43a6-bede-16f8ecb111cb

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

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

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
end A1
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma prog_eq (k : ℕ) : prog k = (S0 k).comp 0 ++ (S1 71 ++ ((S2 k).comp 96 ++ ((S3 k).comp 191 ++
    [.halt 12]))) := by
  simp [prog, a1, a2, a3, S0_len, S2_len, List.append_assoc]

lemma placed_S0 (k : ℕ) : Placed (prog k) 0 ((S0 k).comp 0) := by
  intro i hi; rw [prog_eq, zero_add, List.getElem?_append_left hi]

lemma wf_S0 (k : ℕ) : (S0 k).WF := by
  simp [S0, seqs, tableEntries, Stmt.WF, iload, pset, padd, istore, rconst, preal, rdiv, Plain]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma Stmt.exec_fin (st : Stmt) (h : st.NoLoop) (s : MState) : Exec st s (st.fin s) (st.steps s) := by
  induction st generalizing s with
  | ins i => exact Exec.ins i s h
  | seq a b iha ihb => exact Exec.seq (iha h.1 s) (ihb h.2 _)
  | loop x y b ih => exact absurd h id
  | ite x y a b iha ihb =>
    unfold Stmt.fin Stmt.steps
    split_ifs with hc
    · exact Exec.iteT hc (iha h.1 _)
    · exact Exec.iteF hc (ihb h.2 _)

end LindbladStructLearn.Mach

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma S0_noLoop (k : ℕ) : (S0 k).NoLoop := by
  simp [S0, seqs, tableEntries, Stmt.NoLoop, iload, pset, padd, istore, rconst, preal, rdiv, Plain]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma S0_steps (k : ℕ) (s : MState) : (S0 k).steps s = 71 := by
  simp [S0, seqs, tableEntries, Stmt.steps, iload, pset, padd, istore, rconst, preal, rdiv]

lemma S0_run (k n M : ℕ) (ε δ : ℝ) :
    DetRun (prog k) 71 (alg1Input n M ε δ) (setpc (st0 k n M ε δ) 71) := by
  have h := ((S0 k).exec_fin (S0_noLoop k) (alg1Input n M ε δ)).detRun 0 (placed_S0 k) (wf_S0 k) rfl
  rw [S0_steps, S0_len] at h
  exact h

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
theorem solution : ∀ (k n M : ℕ) (ε δ : ℝ),
    DetRun (prog k) 71 (alg1Input n M ε δ) (setpc (st0 k n M ε δ) 71) :=
  @LindbladStructLearn.Mach.A1.S0_run
