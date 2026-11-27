-- Prove2me | solution 1 for LindbladStructLearn.lemma_2_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:40.428114+00:00
-- url     : https://prove2.me/submissions/3ddc0207-0fed-41b3-be1b-debef2555eb1

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_tail
import Theorems.Thm_LindbladStructLearn_Mach_A1_outerLoop_mass
import Theorems.Thm_LindbladStructLearn_Mach_A1_outerLoop_reach
import Theorems.Thm_LindbladStructLearn_Mach_A1_exit_mass
import Theorems.Thm_LindbladStructLearn_Mach_A1_exit_reach
import Theorems.Thm_LindbladStructLearn_Mach_A1_iterOuter_frame
import Theorems.Thm_LindbladStructLearn_Mach_A1_st0_facts
import Theorems.Thm_LindbladStructLearn_Mach_A1_S0_run
import Theorems.Thm_LindbladStructLearn_Mach_A1_prob_good

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma mass_zero (s : MState) (E : MState → Prop) [DecidablePred E] :
    mass P n evo 0 s E = if E s then 1 else 0 := by
  simp only [mass]; congr

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

lemma branches_halted {s : MState} (h : Halted s) : branches P n evo s = [(1, s)] := by
  unfold branches Halted at *
  simp [h]

lemma mass_halted {s : MState} (h : Halted s) (N : ℕ) (E : MState → Prop) [DecidablePred E] :
    mass P n evo N s E = if E s then 1 else 0 := by
  induction N with
  | zero => exact mass_zero s E
  | succ N ih => rw [mass_det (branches_halted h), ih]

lemma reach_halted {s : MState} (h : Halted s) (N : ℕ) (x : MState) :
    Reach P n evo N s x ↔ x = s := by
  induction N with
  | zero => exact Iff.rfl
  | succ N ih => rw [reach_det (branches_halted h), ih]

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

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

@[simp] lemma setpc_pc (s : MState) (a : ℕ) : (setpc s a).core.pc = a := rfl
@[simp] lemma setpc_ptrs (s : MState) (a : ℕ) : (setpc s a).core.ptrs = s.core.ptrs := rfl
@[simp] lemma setpc_output (s : MState) (a : ℕ) : (setpc s a).output = s.output := rfl

lemma ains_output (i : Instr) (s : MState) : (ains i s).output = s.output := by
  rcases i with ins | _ | _ | _ | _ | _ | _ | _ | _
  · rcases ins <;> rfl
  all_goals rfl

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

lemma mem0_high (n M : ℕ) (z : ℤ) (hz : 36 ≤ z) : mem0 n M z = 0 := by
  unfold mem0; repeat rw [if_neg (by omega)]

lemma mem0_mul (n M : ℕ) (a b : Fin 4) : mem0 n M (4 + 4 * (a : ℕ) + (b : ℕ)) = (letterMul a b : ℕ) := by
  fin_cases a <;> fin_cases b <;> simp [mem0, letterMul]

lemma mem0_ph (n M : ℕ) (a b : Fin 4) : mem0 n M (20 + 4 * (a : ℕ) + (b : ℕ)) = phexp a b := by
  fin_cases a <;> fin_cases b <;> simp [mem0, phexp]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma S0_steps (k : ℕ) (s : MState) : (S0 k).steps s = 71 := by
  simp [S0, seqs, tableEntries, Stmt.steps, iload, pset, padd, istore, rconst, preal, rdiv]

lemma st0_work (k n M : ℕ) (ε δ : ℝ) : (st0 k n M ε δ).work = 71 := by
  have := ((S0 k).exec_fin (S0_noLoop k) (alg1Input n M ε δ)).work
  rw [S0_steps] at this; exact this

-- fetch facts for the sampling block
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

lemma innerPost_ptrs (s : MState) (c1 c2 c3 c4 c5 : Fin 2) (q : ℕ) (h5 : q ≠ 5) (h6 : q ≠ 6)
    (h7 : q ≠ 7) (h8 : q ≠ 8) (h9 : q ≠ 9) :
    (innerPost s c1 c2 c3 c4 c5).core.ptrs q = s.core.ptrs q := by
  simp only [innerPost, ains, cset, tick, Function.update_of_ne h5, Function.update_of_ne h6,
    Function.update_of_ne h7, Function.update_of_ne h8, Function.update_of_ne h9]

lemma innerPost_p5 (s : MState) (c1 c2 c3 c4 c5 : Fin 2) :
    (innerPost s c1 c2 c3 c4 c5).core.ptrs 5 = s.core.ptrs 5 + 1 := by
  simp only [innerPost, ains, cset, tick, Function.update_self]
  simp [Function.update_apply]

lemma innerPost_misc (s : MState) (c1 c2 c3 c4 c5 : Fin 2) :
    let t := innerPost s c1 c2 c3 c4 c5
    t.output = s.output ∧ t.durations = s.durations ∧ t.work = s.work + 18 ∧
    t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem := by
  simp only [innerPost, ains, cset, tick]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

lemma innerPost_mem (s : MState) (c1 c2 c3 c4 c5 : Fin 2) :
    (innerPost s c1 c2 c3 c4 c5).intMem = Function.update (Function.update (Function.update s.intMem
      (s.core.ptrs 4 + s.core.ptrs 5) ((c1 : ℤ) + c1 + c2))
      (s.core.ptrs 4 + s.core.ptrs 5 + s.core.ptrs 0) c3)
      (s.core.ptrs 4 + s.core.ptrs 5 + s.core.ptrs 0 + s.core.ptrs 0) ((c4 : ℤ) + c4 + c5) := by
  simp only [innerPost, ains, cset, tick]
  simp only [Function.update_self, Function.update_apply]
  simp

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma iterInner_frame (r : ℕ) (g : Fin r → C5) (s : MState) :
    let t := iterInner r g s
    t.output = s.output ∧ t.durations = s.durations ∧ t.work = s.work + 18 * r ∧
    t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 5 = s.core.ptrs 5 + r := by
  induction r generalizing s with
  | zero => simp [iterInner]
  | succ r ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (fun j => g j.succ) (innerC s (g 0))
    obtain ⟨m1, m2, m3, m4, m5⟩ := innerPost_misc s (g 0).1 (g 0).2.1 (g 0).2.2.1 (g 0).2.2.2.1
      (g 0).2.2.2.2
    simp only [iterInner]
    refine ⟨h1.trans m1, h2.trans m2, by rw [h3]; simp only [innerC] at m3 ⊢; rw [m3]; ring,
      h4.trans m4, h5.trans m5, fun q a b c d e => (h6 q a b c d e).trans
        (innerPost_ptrs s _ _ _ _ _ q a b c d e), ?_⟩
    rw [h7]; simp only [innerC]; rw [innerPost_p5]; push_cast; ring

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma innerC_mem (s : MState) (c : C5) : (innerC s c).intMem =
    Function.update (Function.update (Function.update s.intMem
      (s.core.ptrs 4 + s.core.ptrs 5) (cA c))
      (s.core.ptrs 4 + s.core.ptrs 5 + s.core.ptrs 0) (cV c))
      (s.core.ptrs 4 + s.core.ptrs 5 + s.core.ptrs 0 + s.core.ptrs 0) (cB c) := by
  simp only [innerC]; rw [innerPost_mem]; rfl

lemma iterInner_mem (r : ℕ) (g : Fin r → C5) (s : MState) (hr : s.core.ptrs 0 = s.core.ptrs 5 + r)
    (h5 : 0 ≤ s.core.ptrs 5) :
    let base := s.core.ptrs 4; let q := s.core.ptrs 5; let nn := s.core.ptrs 0
    let t := iterInner r g s
    (∀ j : Fin r, t.intMem (base + q + j) = cA (g j) ∧ t.intMem (base + q + j + nn) = cV (g j) ∧
      t.intMem (base + q + j + nn + nn) = cB (g j)) ∧
    (∀ z, (∀ j : Fin r, z ≠ base + q + j ∧ z ≠ base + q + j + nn ∧ z ≠ base + q + j + nn + nn) →
      t.intMem z = s.intMem z) := by
  induction r generalizing s with
  | zero => simp [iterInner]
  | succ r ih =>
    intro base q nn t
    have hp0 : (innerC s (g 0)).core.ptrs 0 = nn := innerPost_ptrs _ _ _ _ _ _ 0 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hp4 : (innerC s (g 0)).core.ptrs 4 = base := innerPost_ptrs _ _ _ _ _ _ 4 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hp5 : (innerC s (g 0)).core.ptrs 5 = q + 1 := innerPost_p5 _ _ _ _ _ _
    obtain ⟨A1, A2⟩ := ih (fun j => g j.succ) (innerC s (g 0)) (by rw [hp0, hp5]; simp only [nn, q, hr]; push_cast; ring)
      (by rw [hp5]; omega)
    simp only [hp0, hp4, hp5] at A1 A2
    have hm := innerC_mem s (g 0)
    have hnn : nn = q + (r + 1 : ℕ) := hr
    constructor
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [t, iterInner, Fin.val_zero, Nat.cast_zero, add_zero]
        rw [A2, A2, A2]
        · rw [hm]; simp [Function.update_apply, base, q, nn]; push_cast at hnn ⊢; omega
        all_goals intro j'; push_cast at hnn ⊢; refine ⟨?_, ?_, ?_⟩ <;> omega
      · obtain ⟨e1, e2, e3⟩ := A1 j
        simp only [t, iterInner, Fin.val_succ]
        push_cast
        refine ⟨?_, ?_, ?_⟩
        · rw [show base + q + ((j : ℤ) + 1) = base + (q + 1) + j by ring]; exact e1
        · rw [show base + q + ((j : ℤ) + 1) + nn = base + (q + 1) + j + nn by ring]; exact e2
        · rw [show base + q + ((j : ℤ) + 1) + nn + nn = base + (q + 1) + j + nn + nn by ring]; exact e3
    · intro z hz
      simp only [t, iterInner]
      rw [A2 z (fun j => by
        have := hz j.succ; simp only [Fin.val_succ] at this; push_cast at this
        refine ⟨?_, ?_, ?_⟩
        · intro h; apply this.1; rw [h]; ring
        · intro h; apply this.2.1; rw [h]; ring
        · intro h; apply this.2.2; rw [h]; ring), hm]
      have h0 := hz 0
      simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h0
      simp [Function.update_apply, h0.1, h0.2.1, h0.2.2, base, q, nn]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma pre1_ptrs (s : MState) (q : ℕ) (hq : q ≠ 5) : (pre1 s).core.ptrs q = s.core.ptrs q := by
  simp [pre1, ains, tick, Function.update_of_ne hq]
lemma pre1_p5 (s : MState) : (pre1 s).core.ptrs 5 = 0 := by simp [pre1, ains, tick]

lemma pre2_facts (s : MState) (g : Fin n → C5) (h0 : s.core.ptrs 0 = n) :
    let t := pre2 n s g
    t.output = s.output ∧ t.durations = s.durations ∧ t.work = s.work + 18 * n + 3 ∧
    t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    (∀ j : Fin n, t.intMem (s.core.ptrs 4 + j) = cA (g j) ∧
      t.intMem (s.core.ptrs 4 + (n + j)) = cV (g j) ∧
      t.intMem (s.core.ptrs 4 + (2 * n + j)) = cB (g j)) ∧
    (∀ z, (z < s.core.ptrs 4 ∨ s.core.ptrs 4 + 3 * n ≤ z) → t.intMem z = s.intMem z) := by
  intro t
  have hr : (pre1 s).core.ptrs 0 = (pre1 s).core.ptrs 5 + n := by
    rw [pre1_ptrs s 0 (by norm_num), pre1_p5, h0]; ring
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := iterInner_frame n g (pre1 s)
  obtain ⟨m1, m2⟩ := iterInner_mem n g (pre1 s) hr (by rw [pre1_p5])
  simp only [pre1_ptrs s 0 (by norm_num), pre1_ptrs s 4 (by norm_num), pre1_p5, h0, add_zero] at m1 m2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [t, pre2, tick_output]; rw [f1]; simp [pre1]
  · simp only [t, pre2, tick]; rw [f2]; simp [pre1, ains, tick]
  · simp only [t, pre2, tick]; rw [f3]; simp [pre1, ains, tick]; ring
  · simp only [t, pre2, tick]; rw [f4]; simp [pre1, ains, tick]
  · simp only [t, pre2, tick]; rw [f5]; simp [pre1, ains, tick]
  · intro q a b c d e; simp only [t, pre2, tick]; rw [f6 q a b c d e, pre1_ptrs s q a]
  · intro j; obtain ⟨e1, e2, e3⟩ := m1 j
    simp only [t, pre2, tick]
    refine ⟨e1, ?_, ?_⟩
    · rw [show s.core.ptrs 4 + ((n : ℤ) + j) = s.core.ptrs 4 + j + n by ring]; exact e2
    · rw [show s.core.ptrs 4 + (2 * (n : ℤ) + j) = s.core.ptrs 4 + j + n + n by ring]; exact e3
  · intro z hz
    simp only [t, pre2, tick]
    rw [m2 z (fun j => by have := j.isLt; refine ⟨?_, ?_, ?_⟩ <;> omega)]
    simp [pre1, ains, tick]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma outerPost_eq (s : MState) (g : Fin n → C5) (w : Qubits n) :
    outerPost n s g w = tick (ains (.core (.pinc 3)) (ains (.pointerAdd 4 4 2) (expSt0 n (pre2 n s g) w))) :=
  rfl

lemma outerPost_facts (s : MState) (g : Fin n → C5) (w : Qubits n) (h0 : s.core.ptrs 0 = n) :
    let t := outerPost n s g w
    t.output = s.output ∧ t.durations = s.durations ++ [s.core.regs 0] ∧
    t.work = s.work + (19 * n + 7) ∧ t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 3 = s.core.ptrs 3 + 1 ∧ t.core.ptrs 4 = s.core.ptrs 4 + s.core.ptrs 2 ∧
    (∀ j : Fin n, t.intMem (s.core.ptrs 4 + j) = cA (g j) ∧
      t.intMem (s.core.ptrs 4 + (n + j)) = cV (g j) ∧
      t.intMem (s.core.ptrs 4 + (2 * n + j)) = cB (g j) ∧
      t.intMem (s.core.ptrs 4 + (3 * n + j)) = if w j then 1 else 0) ∧
    (∀ z, (z < s.core.ptrs 4 ∨ s.core.ptrs 4 + 4 * n ≤ z) → t.intMem z = s.intMem z) := by
  intro t
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := pre2_facts s g h0
  have h4 := f6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := f6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := f6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm : t.intMem = (expSt0 n (pre2 n s g) w).intMem := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [t, outerPost_eq, tick_output, ains_output']; simp [expSt0, f1]
  · simp [t, outerPost_eq, tick, ains, expSt0, f2, f4]
  · simp only [t, outerPost_eq, tick, ains, expSt0, f3]; ring
  · simp [t, outerPost_eq, tick, ains, expSt0, f4]
  · simp [t, outerPost_eq, tick, ains, expSt0, f5]
  · intro q a b c d e f g'
    simp [t, outerPost_eq, tick, ains, expSt0, Function.update_of_ne a, Function.update_of_ne b,
      f6 q c d e f g']
  · simp [t, outerPost_eq, tick, ains, expSt0, h3]
  · simp [t, outerPost_eq, tick, ains, expSt0, h4, h2]
  · intro j
    obtain ⟨e1, e2, e3⟩ := f7 j
    have hj := j.isLt
    rw [hm]; simp only [expSt0, h4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [dif_neg (by omega), e1]
    · rw [dif_neg (by omega), e2]
    · rw [dif_neg (by omega), e3]
    · rw [dif_pos (by omega)]
      have e : (⟨(s.core.ptrs 4 + (3 * n + j) - (s.core.ptrs 4 + 3 * n)).toNat, by omega⟩ : Fin n) = j :=
        Fin.ext (by simp)
      rw [e]
  · intro z hz
    rw [hm]; simp only [expSt0, h4]
    rw [dif_neg (by omega), f8 z (by omega)]

lemma iterOuter_mem (r : ℕ) (G : Fin r → Rd n) (s : MState) (h0 : s.core.ptrs 0 = n)
    (h2 : s.core.ptrs 2 = 4 * n) :
    let t := iterOuter r G s
    let b := s.core.ptrs 4
    (∀ i : Fin r, ∀ j : Fin n, t.intMem (b + 4 * n * i + j) = cA ((G i).1 j) ∧
      t.intMem (b + 4 * n * i + (n + j)) = cV ((G i).1 j) ∧
      t.intMem (b + 4 * n * i + (2 * n + j)) = cB ((G i).1 j) ∧
      t.intMem (b + 4 * n * i + (3 * n + j)) = if (G i).2 j then 1 else 0) ∧
    (∀ z, (z < b ∨ b + 4 * n * r ≤ z) → t.intMem z = s.intMem z) := by
  induction r generalizing s with
  | zero => simp [iterOuter]
  | succ r ih =>
    intro t b
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := outerPost_facts s (G 0).1 (G 0).2 h0
    have h0' : (outerPost n s (G 0).1 (G 0).2).core.ptrs 0 = n := by
      rw [o6 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h0]
    have h2' : (outerPost n s (G 0).1 (G 0).2).core.ptrs 2 = 4 * n := by
      rw [o6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h2]
    obtain ⟨A1, A2⟩ := ih (fun j => G j.succ) _ h0' h2'
    rw [o8, h2] at A1 A2
    constructor
    · intro i j
      have hj := j.isLt
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [t, iterOuter, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero]
        obtain ⟨e1, e2, e3, e4⟩ := o9 j
        rw [A2 _ (by omega), A2 _ (by omega), A2 _ (by omega), A2 _ (by omega)]
        exact ⟨e1, e2, e3, e4⟩
      · obtain ⟨e1, e2, e3, e4⟩ := A1 i j
        simp only [t, iterOuter, Fin.val_succ]
        push_cast
        have r1 : ∀ x : ℤ, b + 4 * n * ((i : ℤ) + 1) + x = s.core.ptrs 4 + 4 * n + 4 * n * i + x := by
          intro x; simp only [b]; ring
        rw [r1, r1, r1, r1]
        exact ⟨e1, e2, e3, e4⟩
    · intro z hz
      simp only [t, iterOuter]
      push_cast at hz
      simp only [b] at hz
      have hn : (0 : ℤ) ≤ 4 * n := by positivity
      have hA : z < s.core.ptrs 4 + s.core.ptrs 2 ∨ s.core.ptrs 4 + s.core.ptrs 2 + 4 * n * r ≤ z := by
        rw [h2]; rcases hz with hz | hz
        · left; omega
        · right; nlinarith
      have hB : z < s.core.ptrs 4 ∨ s.core.ptrs 4 + 4 * n ≤ z := by
        rcases hz with hz | hz
        · left; exact hz
        · right; have : (0 : ℤ) ≤ 4 * n * r := by positivity
          nlinarith
      rw [h2] at hA
      rw [A2 z hA, o10 z hB]

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

lemma oW_succ (k n q : ℕ) : oW k n (q + 1) = oW k n q * rad k n (q + 1) := by
  unfold oW; rw [Finset.prod_range_succ]

lemma rad_pos (k n : ℕ) (hn : 1 ≤ n) (i : ℕ) : 0 < rad k n i := by
  unfold rad; split_ifs <;> omega

lemma oval_congr (k n : ℕ) : ∀ (q : ℕ) (D E : ℕ → ℕ), (∀ i ≤ q, D i = E i) →
    oval k n q D = oval k n q E
  | 0, D, E, h => by simp [oval, h 0 le_rfl]
  | q + 1, D, E, h => by
      simp only [oval]
      rw [oval_congr k n q D E (fun i hi => h i (by omega)), h (q + 1) le_rfl]

lemma oval_zero (k n : ℕ) : ∀ q : ℕ, oval k n q (fun _ => 0) = 0
  | 0 => rfl
  | q + 1 => by simp [oval, oval_zero k n q]

lemma oval_lt (k n : ℕ) : ∀ (q : ℕ) (D : ℕ → ℕ), (∀ i ≤ q, D i < rad k n i) →
    oval k n q D < oW k n q
  | 0, D, h => by simpa [oval, oW] using h 0 le_rfl
  | q + 1, D, h => by
      have ih := oval_lt k n q D (fun i hi => h i (by omega))
      have hd := h (q + 1) le_rfl
      rw [oW_succ]; simp only [oval]
      calc oval k n q D * rad k n (q + 1) + D (q + 1)
          < oval k n q D * rad k n (q + 1) + rad k n (q + 1) := by omega
        _ = (oval k n q D + 1) * rad k n (q + 1) := by ring
        _ ≤ oW k n q * rad k n (q + 1) := Nat.mul_le_mul_right _ ih

lemma oval_inj (k n : ℕ) : ∀ (q : ℕ) (D E : ℕ → ℕ), (∀ i ≤ q, D i < rad k n i) →
    (∀ i ≤ q, E i < rad k n i) → oval k n q D = oval k n q E → ∀ i ≤ q, D i = E i
  | 0, D, E, _, _, h, i, hi => by
      obtain rfl : i = 0 := by omega
      simpa [oval] using h
  | q + 1, D, E, hD, hE, h, i, hi => by
      simp only [oval] at h
      have hd := hD (q + 1) le_rfl
      have he := hE (q + 1) le_rfl
      set r := rad k n (q + 1)
      have heq : oval k n q D = oval k n q E := by
        rcases lt_trichotomy (oval k n q D) (oval k n q E) with hlt | heq | hgt
        · have : (oval k n q D + 1) * r ≤ oval k n q E * r := Nat.mul_le_mul_right _ hlt
          nlinarith
        · exact heq
        · have : (oval k n q E + 1) * r ≤ oval k n q D * r := Nat.mul_le_mul_right _ hgt
          nlinarith
      rw [heq] at h
      rcases Nat.lt_or_ge i (q + 1) with hi' | hi'
      · exact oval_inj k n q D E (fun j hj => hD j (by omega)) (fun j hj => hE j (by omega))
          heq i (by omega)
      · obtain rfl : i = q + 1 := by omega
        omega

lemma incAt_high (k n : ℕ) : ∀ (q : ℕ) (D : ℕ → ℕ) (i : ℕ), q < i → (incAt k n q D).1 i = D i
  | 0, D, i, hi => by
      simp only [incAt]
      split_ifs <;> simp [Function.update_of_ne (show i ≠ 0 by omega)]
  | q + 1, D, i, hi => by
      simp only [incAt]
      split_ifs
      · simp [Function.update_of_ne (show i ≠ q + 1 by omega)]
      · rw [incAt_high k n q _ i (by omega)]
        simp [Function.update_of_ne (show i ≠ q + 1 by omega)]

lemma incAt_inRange (k n : ℕ) (hn : 1 ≤ n) : ∀ (q : ℕ) (D : ℕ → ℕ),
    (∀ i ≤ q, D i < rad k n i) → ∀ i ≤ q, (incAt k n q D).1 i < rad k n i
  | 0, D, hD, i, hi => by
      obtain rfl : i = 0 := by omega
      simp only [incAt]
      split_ifs with h1
      · simpa using h1
      · simpa using rad_pos k n hn 0
  | q + 1, D, hD, i, hi => by
      simp only [incAt]
      split_ifs with h1
      · by_cases hiq : i = q + 1
        · subst hiq; simpa using h1
        · show Function.update D (q + 1) (D (q + 1) + 1) i < rad k n i
          rw [Function.update_of_ne hiq]; exact hD i hi
      · have hD' : ∀ j ≤ q, Function.update D (q + 1) 0 j < rad k n j := by
          intro j hj
          rw [Function.update_of_ne (show j ≠ q + 1 by omega)]; exact hD j (by omega)
        rcases Nat.lt_or_ge i (q + 1) with hi' | hi'
        · exact incAt_inRange k n hn q _ hD' i (by omega)
        · obtain rfl : i = q + 1 := by omega
          rw [incAt_high k n q _ (q + 1) (by omega)]
          simpa using rad_pos k n hn (q + 1)

lemma incAt_spec (k n : ℕ) : ∀ (q : ℕ) (D : ℕ → ℕ), (∀ i ≤ q, D i < rad k n i) →
    ((incAt k n q D).2 = false → oval k n q (incAt k n q D).1 = oval k n q D + 1) ∧
    ((incAt k n q D).2 = true → oval k n q D + 1 = oW k n q)
  | 0, D, hD => by
      have hd := hD 0 le_rfl
      simp only [incAt]
      split_ifs with h1
      · refine ⟨fun _ => ?_, fun h => by simp at h⟩
        simp [oval]
      · refine ⟨fun h => by simp at h, fun _ => ?_⟩
        simp only [oval, oW, zero_add, Finset.prod_range_one]
        omega
  | q + 1, D, hD => by
      have hd := hD (q + 1) le_rfl
      simp only [incAt]
      split_ifs with h1
      · refine ⟨fun _ => ?_, fun h => by simp at h⟩
        simp only [oval]
        rw [oval_congr k n q (Function.update D (q + 1) (D (q + 1) + 1)) D
          (fun i hi => Function.update_of_ne (show i ≠ q + 1 by omega) _ _)]
        simp; ring
      · have hD' : ∀ j ≤ q, Function.update D (q + 1) 0 j < rad k n j := by
          intro j hj
          rw [Function.update_of_ne (show j ≠ q + 1 by omega)]; exact hD j (by omega)
        have hc : oval k n q (Function.update D (q + 1) 0) = oval k n q D :=
          oval_congr k n q _ D (fun i hi => Function.update_of_ne (show i ≠ q + 1 by omega) _ _)
        obtain ⟨ih1, ih2⟩ := incAt_spec k n q _ hD'
        have hr : rad k n (q + 1) = D (q + 1) + 1 := by omega
        refine ⟨fun hf => ?_, fun ht => ?_⟩
        · simp only [oval]
          rw [ih1 hf, hc, incAt_high k n q _ (q + 1) (by omega), hr]
          simp; ring
        · have := ih2 ht
          rw [hc] at this
          simp only [oval]
          rw [oW_succ, ← this, hr]; ring

lemma incAt_flag_iff (k n : ℕ) (hn : 1 ≤ n) (q : ℕ) (D : ℕ → ℕ)
    (hD : ∀ i ≤ q, D i < rad k n i) :
    (incAt k n q D).2 = true ↔ oval k n q D + 1 = oW k n q := by
  obtain ⟨h1, h2⟩ := incAt_spec k n q D hD
  refine ⟨h2, fun h => ?_⟩
  by_contra hf
  have hf' : (incAt k n q D).2 = false := by simpa using hf
  have := oval_lt k n q _ (incAt_inRange k n hn q D hD)
  rw [h1 hf'] at this
  omega

lemma Dseq_succ (k n j : ℕ) : Dseq k n (j + 1) = succD k n (Dseq k n j) :=
  Function.iterate_succ_apply' _ _ _

lemma Kc_eq_oW (k n : ℕ) : Kc k n = oW k n (3 * k) := rfl

theorem Dseq_inRange (k n : ℕ) (hn : 1 ≤ n) (j : ℕ) : InRange k n (Dseq k n j) := by
  unfold InRange
  induction j with
  | zero => intro i _; simpa [Dseq] using rad_pos k n hn i
  | succ j ih =>
      rw [Dseq_succ, succD]
      exact incAt_inRange k n hn _ _ ih

lemma Dseq_val (k n : ℕ) (hn : 1 ≤ n) : ∀ j < Kc k n, oval k n (3 * k) (Dseq k n j) = j := by
  intro j
  induction j with
  | zero => intro _; exact oval_zero k n _
  | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hR := Dseq_inRange k n hn j
      have hf : (incAt k n (3 * k) (Dseq k n j)).2 = false := by
        by_contra hf
        have ht : (incAt k n (3 * k) (Dseq k n j)).2 = true := by simpa using hf
        rw [incAt_flag_iff k n hn _ _ hR, ih', ← Kc_eq_oW] at ht
        omega
      rw [Dseq_succ, succD, (incAt_spec k n _ _ hR).1 hf, ih']

theorem Dseq_inj (k n : ℕ) (hn : 1 ≤ n) (j j' : ℕ) (hj : j < Kc k n) (hj' : j' < Kc k n)
    (h : ∀ i ≤ 3 * k, Dseq k n j i = Dseq k n j' i) : j = j' := by
  rw [← Dseq_val k n hn j hj, ← Dseq_val k n hn j' hj']
  exact oval_congr k n _ _ _ h

theorem Dseq_surj (k n : ℕ) (hn : 1 ≤ n) (D : ℕ → ℕ) (hD : InRange k n D) :
    ∃ j < Kc k n, ∀ i ≤ 3 * k, Dseq k n j i = D i := by
  have hlt : oval k n (3 * k) D < Kc k n := oval_lt k n _ D hD
  refine ⟨oval k n (3 * k) D, hlt, ?_⟩
  exact oval_inj k n _ _ _ (Dseq_inRange k n hn _) hD (Dseq_val k n hn _ hlt)

theorem Kc_eq (k n : ℕ) : Kc k n = (k + 1) * n ^ k * 16 ^ k := by
  unfold Kc
  rw [Finset.prod_range_succ', show 3 * k = k + 2 * k by ring, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range k, rad k n (x + 1) = n ^ k := by
    have : ∀ x ∈ Finset.range k, rad k n (x + 1) = n := by
      intro x hx
      simp only [Finset.mem_range] at hx
      unfold rad; rw [if_neg (by omega), if_pos (by omega)]
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range]
  have h2 : ∏ x ∈ Finset.range (2 * k), rad k n (k + x + 1) = 16 ^ k := by
    have : ∀ x ∈ Finset.range (2 * k), rad k n (k + x + 1) = 4 := by
      intro x _
      unfold rad; rw [if_neg (by omega), if_neg (by omega)]
    rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range, pow_mul]
    norm_num
  rw [h1, h2]
  simp [rad]; ring

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

lemma s_le (hD : InRange k n D) : D 0 ≤ k := by
  have := hD 0 (by omega); simp [rad] at this; omega

lemma site_lt (hD : InRange k n D) (r : ℕ) (hr : r < k) : D (1 + r) < n := by
  have := hD (1 + r) (by omega)
  rwa [rad, if_neg (by omega), if_pos (by omega)] at this

lemma l1_lt (hD : InRange k n D) (r : ℕ) (hr : r < k) : D (1 + k + r) < 4 := by
  have := hD (1 + k + r) (by omega)
  rwa [rad, if_neg (by omega), if_neg (by omega)] at this

lemma l2_lt (hD : InRange k n D) (r : ℕ) (hr : r < k) : D (1 + 2 * k + r) < 4 := by
  have := hD (1 + 2 * k + r) (by omega)
  rwa [rad, if_neg (by omega), if_neg (by omega)] at this

lemma L1_val (hD : InRange k n D) (r : ℕ) (hr : r < k) : ((L1 k D r : Fin 4) : ℕ) = D (1 + k + r) :=
  Nat.mod_eq_of_lt (l1_lt hD r hr)

lemma L2_val (hD : InRange k n D) (r : ℕ) (hr : r < k) : ((L2 k D r : Fin 4) : ℕ) = D (1 + 2 * k + r) :=
  Nat.mod_eq_of_lt (l2_lt hD r hr)

lemma site_strict (hv : validD k D) (hs : D 0 ≤ k) {r r' : ℕ} (h : r < r') (h' : r' < D 0) :
    D (1 + r) < D (1 + r') := by
  induction r' with
  | zero => omega
  | succ m ih =>
    have step : D (1 + m) < D (1 + (m + 1)) := ((hv m (by omega)).2 (by omega)).2 (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact lt_trans (ih h1 (by omega)) step
    · subst h1; exact step

lemma site_inj (hv : validD k D) (hs : D 0 ≤ k) {r r' : ℕ} (h : r < D 0) (h' : r' < D 0)
    (he : D (1 + r) = D (1 + r')) : r = r' := by
  rcases lt_trichotomy r r' with h1 | h1 | h1
  · have := site_strict hv hs h1 h'; omega
  · exact h1
  · have := site_strict hv hs h1 h; omega

lemma pairOf_site (hD : InRange k n D) (hv : validD k D) (r : ℕ) (hr : r < D 0) (i : Fin n)
    (hi : (i : ℕ) = D (1 + r)) :
    (pairOf n k D).1 i = L1 k D r ∧ (pairOf n k D).2 i = L2 k D r := by
  have hs := s_le hD
  have key : ∀ h : ∃ r', r' < D 0 ∧ D (1 + r') = (i : ℕ), Nat.find h = r := fun h =>
    site_inj hv hs (Nat.find_spec h).1 hr ((Nat.find_spec h).2.trans hi)
  unfold pairOf
  dsimp only
  constructor
  · split_ifs with h
    · apply Fin.ext; simp only [L1]; rw [key h]
    · exact absurd ⟨r, hr, hi.symm⟩ h
  · split_ifs with h
    · apply Fin.ext; simp only [L2]; rw [key h]
    · exact absurd ⟨r, hr, hi.symm⟩ h

lemma pairOf_off (i : Fin n) (hi : ∀ r < D 0, D (1 + r) ≠ i) :
    (pairOf n k D).1 i = 0 ∧ (pairOf n k D).2 i = 0 := by
  unfold pairOf
  dsimp only
  have : ¬ ∃ r, r < D 0 ∧ D (1 + r) = (i : ℕ) := fun ⟨r, hr, he⟩ => hi r hr he
  simp only [dif_neg this, and_self]

/-- the sites of a record -/
def sig (hD : InRange k n D) (r : Fin (D 0)) : Fin n :=
  ⟨D (1 + r), site_lt hD r (lt_of_lt_of_le r.2 (s_le hD))⟩

lemma sig_inj (hD : InRange k n D) (hv : validD k D) : Function.Injective (sig hD) := by
  intro r r' h
  have := congrArg Fin.val h
  exact Fin.ext (site_inj hv (s_le hD) r.2 r'.2 this)

lemma sig_strictMono (hD : InRange k n D) (hv : validD k D) : StrictMono (sig hD) := by
  intro r r' h
  exact site_strict hv (s_le hD) h r'.2

def sigE (hD : InRange k n D) (hv : validD k D) : Fin (D 0) ↪ Fin n := ⟨sig hD, sig_inj hD hv⟩

lemma mem_pairSupport {P : Pauli n × Pauli n} (i : Fin n) :
    i ∈ pairSupport P ↔ P.1 i ≠ 0 ∨ P.2 i ≠ 0 := by
  simp [pairSupport, support]

lemma supp_eq (hD : InRange k n D) (hv : validD k D) :
    pairSupport (pairOf n k D) = Finset.univ.map (sigE hD hv) := by
  have hs := s_le hD
  ext i
  rw [mem_pairSupport]
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  by_cases hex : ∃ r < D 0, D (1 + r) = i
  · obtain ⟨r, hr, he⟩ := hex
    have h := pairOf_site hD hv r hr i he.symm
    rw [h.1, h.2]
    refine ⟨fun _ => ⟨⟨r, hr⟩, Fin.ext he⟩, fun _ => ?_⟩
    have hnz := ((hv r (by omega)).2 hr).1
    by_contra hc
    push Not at hc
    apply hnz
    have a := congrArg Fin.val hc.1
    have b := congrArg Fin.val hc.2
    rw [L1_val hD r (by omega)] at a
    rw [L2_val hD r (by omega)] at b
    exact ⟨a, b⟩
  · push Not at hex
    have h := pairOf_off (k := k) i hex
    rw [h.1, h.2]
    simp only [ne_eq, not_true_eq_false, or_self, false_iff, not_exists]
    intro r hr
    exact hex r r.2 (congrArg Fin.val hr)

theorem card_pairOf (hD : InRange k n D) (hv : validD k D) :
    (pairSupport (pairOf n k D)).card = D 0 := by
  rw [supp_eq hD hv, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem recordPair_invalid (im : ℤ → ℤ) (b : ℤ) (h : im b = k + 1) : recordPair n k im b = none := by
  unfold recordPair
  dsimp only
  rw [if_neg]
  rw [h]; omega

theorem recordPair_valid (hD : InRange k n D) (hv : validD k D) (im : ℤ → ℤ) (b : ℤ)
    (him : ∀ i ≤ 3 * k, im (b + i) = D i) :
    recordPair n k im b = some (pairOf n k D) := by
  have hs := s_le hD
  have h0 : im b = D 0 := by simpa using him 0 (by omega)
  have hsN : (im b).toNat = D 0 := by rw [h0]; simp
  have hsite : ∀ r : ℕ, r < D 0 → im (b + 1 + r) = D (1 + r) := fun r hr => by
    have := him (1 + r) (by omega); push_cast at this; rw [← this]; ring_nf
  have hl1 : ∀ r : ℕ, r < D 0 → im (b + 1 + k + r) = D (1 + k + r) := fun r hr => by
    have := him (1 + k + r) (by omega); push_cast at this; rw [← this]; ring_nf
  have hl2 : ∀ r : ℕ, r < D 0 → im (b + 1 + 2 * k + r) = D (1 + 2 * k + r) := fun r hr => by
    have := him (1 + 2 * k + r) (by omega); push_cast at this; rw [← this]; ring_nf
  unfold recordPair
  dsimp only
  rw [if_pos]
  swap
  · refine ⟨by rw [h0]; omega, by rw [h0]; omega, ?_, ?_⟩
    · intro r hr
      rw [hsN] at hr
      rw [hsite r hr, hl1 r hr, hl2 r hr]
      have := site_lt hD r (by omega)
      have := l1_lt hD r (by omega)
      have := l2_lt hD r (by omega)
      omega
    · intro r hr
      rw [hsN] at hr
      have e1 := hsite r (by omega)
      have e2 := hsite (r + 1) hr
      have := site_strict hv hs (by omega : r < r + 1) hr
      push_cast at e2 ⊢
      rw [e1, e2]; exact_mod_cast this
  congr 1
  have equiv : ∀ (i : Fin n) (r : ℕ), (r < (im b).toNat ∧ im (b + 1 + r) = ((i : ℕ) : ℤ)) ↔
      (r < D 0 ∧ D (1 + r) = (i : ℕ)) := by
    intro i r
    rw [hsN]
    constructor
    · rintro ⟨hr, he⟩; rw [hsite r hr] at he; exact ⟨hr, by exact_mod_cast he⟩
    · rintro ⟨hr, he⟩; rw [hsite r hr]; exact ⟨hr, by exact_mod_cast he⟩
  refine Prod.ext ?_ ?_ <;> funext i <;> dsimp only
  · by_cases hex : ∃ r < D 0, D (1 + r) = i
    · obtain ⟨r, hr, he⟩ := hex
      rw [(pairOf_site hD hv r hr i he.symm).1]
      split_ifs with h
      · have hf := (equiv i _).1 (Nat.find_spec h)
        have : Nat.find h = r := site_inj hv hs hf.1 hr (hf.2.trans he.symm)
        apply Fin.ext; simp only [L1]; rw [this, hl1 r hr]; simp
      · exact absurd ⟨r, (equiv i r).2 ⟨hr, he⟩⟩ h
    · push Not at hex
      rw [(pairOf_off (k := k) i hex).1]
      split_ifs with h
      · obtain ⟨r, hr⟩ := h
        exact absurd ((equiv i r).1 hr).2 (hex r ((equiv i r).1 hr).1)
      · rfl
  · by_cases hex : ∃ r < D 0, D (1 + r) = i
    · obtain ⟨r, hr, he⟩ := hex
      rw [(pairOf_site hD hv r hr i he.symm).2]
      split_ifs with h
      · have hf := (equiv i _).1 (Nat.find_spec h)
        have : Nat.find h = r := site_inj hv hs hf.1 hr (hf.2.trans he.symm)
        apply Fin.ext; simp only [L2]; rw [this, hl2 r hr]; simp
      · exact absurd ⟨r, (equiv i r).2 ⟨hr, he⟩⟩ h
    · push Not at hex
      rw [(pairOf_off (k := k) i hex).2]
      split_ifs with h
      · obtain ⟨r, hr⟩ := h
        exact absurd ((equiv i r).1 hr).2 (hex r ((equiv i r).1 hr).1)
      · rfl

lemma pos_cases (i : ℕ) (hi : i ≤ 3 * k) : i = 0 ∨ (∃ r < k, i = 1 + r) ∨
    (∃ r < k, i = 1 + k + r) ∨ (∃ r < k, i = 1 + 2 * k + r) := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i ≤ k
  · exact Or.inr (Or.inl ⟨i - 1, by omega, by omega⟩)
  by_cases h2 : i ≤ 2 * k
  · exact Or.inr (Or.inr (Or.inl ⟨i - 1 - k, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i - 1 - 2 * k, by omega, by omega⟩))

theorem exists_code (hn : 0 < n) (Q : Pauli n × Pauli n) (hQ : (pairSupport Q).card ≤ k) :
    ∃ D, InRange k n D ∧ validD k D ∧ pairOf n k D = Q := by
  classical
  obtain ⟨S, hS⟩ : ∃ S, S = pairSupport Q := ⟨_, rfl⟩
  rw [← hS] at hQ
  have hmemS : ∀ i, i ∈ S ↔ Q.1 i ≠ 0 ∨ Q.2 i ≠ 0 := fun i => hS ▸ mem_pairSupport i
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  let f : ℕ → ℕ := fun r => if h : r < S.card then (e ⟨r, h⟩ : ℕ) else 0
  let g1 : ℕ → ℕ := fun r => if h : r < S.card then (Q.1 (e ⟨r, h⟩) : ℕ) else 0
  let g2 : ℕ → ℕ := fun r => if h : r < S.card then (Q.2 (e ⟨r, h⟩) : ℕ) else 0
  let D : ℕ → ℕ := fun i => if i = 0 then S.card else if i ≤ k then f (i - 1) else
    if i ≤ 2 * k then g1 (i - 1 - k) else g2 (i - 1 - 2 * k)
  have hD0 : D 0 = S.card := by simp [D]
  have hD1 : ∀ r < k, D (1 + r) = f r := by
    intro r hr; simp only [D]; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
  have hD2 : ∀ r < k, D (1 + k + r) = g1 r := by
    intro r hr; simp only [D]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 1; omega
  have hD3 : ∀ r, D (1 + 2 * k + r) = g2 r := by
    intro r; simp only [D]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; congr 1; omega
  have hemem : ∀ j, e j ∈ S := fun j => Finset.orderEmbOfFin_mem S rfl j
  have hIR : InRange k n D := by
    intro i hi
    rcases pos_cases i hi with h | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · subst h; rw [hD0]; simp [rad]; omega
    · rw [hD1 r hr, rad, if_neg (by omega), if_pos (by omega)]
      simp only [f]; split_ifs
      · exact Fin.isLt _
      · exact hn
    · rw [hD2 r hr, rad, if_neg (by omega), if_neg (by omega)]
      simp only [g1]; split_ifs
      · exact Fin.isLt _
      · norm_num
    · rw [hD3 r, rad, if_neg (by omega), if_neg (by omega)]
      simp only [g2]; split_ifs
      · exact Fin.isLt _
      · norm_num
  have hV : validD k D := by
    intro r hr
    rw [hD0, hD1 r hr, hD2 r hr, hD3 r]
    refine ⟨fun h => ?_, fun h => ⟨?_, fun h' => ?_⟩⟩
    · simp only [f, g1, g2, dif_neg (show ¬ r < S.card by omega), and_self]
    · simp only [g1, g2, dif_pos h]
      rintro ⟨h1, h2⟩
      rcases (hmemS _).1 (hemem ⟨r, h⟩) with h3 | h3
      · exact h3 (Fin.ext h1)
      · exact h3 (Fin.ext h2)
    · rw [hD1 (r + 1) (by omega)]
      simp only [f, dif_pos h, dif_pos h']
      exact e.strictMono (show (⟨r, h⟩ : Fin S.card) < ⟨r + 1, h'⟩ from Fin.mk_lt_mk.2 (by omega))
  refine ⟨D, hIR, hV, ?_⟩
  have key : ∀ i, (i ∈ S → ∃ j : Fin S.card, j.val < D 0 ∧ (i : ℕ) = D (1 + j) ∧
      (L1 k D j = Q.1 i ∧ L2 k D j = Q.2 i)) := by
    intro i hi
    have : i ∈ Set.range e := by
      simp only [e]; rw [Finset.range_orderEmbOfFin]; exact hi
    obtain ⟨j, hj⟩ := this
    have hjk : (j : ℕ) < k := lt_of_lt_of_le j.2 hQ
    refine ⟨j, by rw [hD0]; exact j.2, ?_, ?_, ?_⟩
    · rw [hD1 j hjk]; simp only [f, dif_pos j.2]; rw [← hj]
    · apply Fin.ext; rw [L1_val hIR j hjk, hD2 j hjk]; simp only [g1, dif_pos j.2]; rw [← hj]
    · apply Fin.ext; rw [L2_val hIR j hjk, hD3 j]; simp only [g2, dif_pos j.2]; rw [← hj]
  have off : ∀ i, i ∉ S → ∀ r < D 0, D (1 + r) ≠ i := by
    intro i hi r hr he
    rw [hD0] at hr
    rw [hD1 r (by omega)] at he
    simp only [f, dif_pos hr] at he
    exact hi (Fin.ext he ▸ hemem _)
  refine Prod.ext ?_ ?_ <;> funext i <;> by_cases hi : i ∈ S
  · obtain ⟨j, hj, hji, hl, -⟩ := key i hi
    rw [(pairOf_site hIR hV j hj i hji).1, hl]
  · rw [(pairOf_off (k := k) i (off i hi)).1]
    have := (hmemS i).not.1 hi; push Not at this; exact this.1.symm
  · obtain ⟨j, hj, hji, -, hl⟩ := key i hi
    rw [(pairOf_site hIR hV j hj i hji).2, hl]
  · rw [(pairOf_off (k := k) i (off i hi)).2]
    have := (hmemS i).not.1 hi; push Not at this; exact this.2.symm

theorem code_unique (D D' : ℕ → ℕ) (hD : InRange k n D) (hv : validD k D) (hD' : InRange k n D')
    (hv' : validD k D') (h : pairOf n k D = pairOf n k D') : ∀ i ≤ 3 * k, D i = D' i := by
  have h0 : D 0 = D' 0 := by rw [← card_pairOf hD hv, ← card_pairOf hD' hv', h]
  have hs := s_le hD
  have hs' := s_le hD'
  set S := pairSupport (pairOf n k D) with hS
  have hcard : S.card = D 0 := card_pairOf hD hv
  have mem1 : ∀ r, sig hD r ∈ S := by
    intro r; rw [hS, supp_eq hD hv]; exact Finset.mem_map_of_mem _ (Finset.mem_univ r)
  have mem2 : ∀ r, sig hD' (Fin.cast h0 r) ∈ S := by
    intro r; rw [hS, h, supp_eq hD' hv']; exact Finset.mem_map_of_mem _ (Finset.mem_univ _)
  have e1 := Finset.orderEmbOfFin_unique hcard mem1 (sig_strictMono hD hv)
  have e2 := Finset.orderEmbOfFin_unique hcard mem2
    ((sig_strictMono hD' hv').comp (Fin.cast_strictMono h0))
  have hsite : ∀ r (hr : r < D 0), sig hD ⟨r, hr⟩ = sig hD' ⟨r, h0 ▸ hr⟩ := by
    intro r hr
    have := congrFun (e1.trans e2.symm) ⟨r, hr⟩
    exact this
  have hsite' : ∀ r < D 0, D (1 + r) = D' (1 + r) := fun r hr => congrArg Fin.val (hsite r hr)
  have hlet : ∀ r < D 0, D (1 + k + r) = D' (1 + k + r) ∧ D (1 + 2 * k + r) = D' (1 + 2 * k + r) := by
    intro r hr
    have hr' : r < D' 0 := h0 ▸ hr
    have a := pairOf_site hD hv r hr (sig hD ⟨r, hr⟩) rfl
    have b := pairOf_site hD' hv' r hr' (sig hD ⟨r, hr⟩) (by rw [hsite r hr]; rfl)
    rw [h] at a
    rw [← L1_val hD r (by omega), ← L1_val hD' r (by omega), ← L2_val hD r (by omega),
      ← L2_val hD' r (by omega), ← a.1, ← a.2, b.1, b.2]
    exact ⟨rfl, rfl⟩
  intro i hi
  rcases pos_cases i hi with rfl | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact h0
  · by_cases hr0 : r < D 0
    · exact hsite' r hr0
    · rw [((hv r hr).1 (by omega)).1, ((hv' r hr).1 (by omega)).1]
  · by_cases hr0 : r < D 0
    · exact (hlet r hr0).1
    · rw [((hv r hr).1 (by omega)).2.1, ((hv' r hr).1 (by omega)).2.1]
  · by_cases hr0 : r < D 0
    · exact (hlet r hr0).2
    · rw [((hv r hr).1 (by omega)).2.2, ((hv' r hr).1 (by omega)).2.2]

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

lemma tab_mem0 (n M : ℕ) : Tab (mem0 n M) := fun x y => ⟨mem0_mul n M x y, by rw [mem0_ph]⟩

lemma xEnd_facts (k n M : ℕ) (ε δ : ℝ) (G : Fin M → Rd n) :
    let s := xEnd k n M ε δ G
    s.output = none ∧ s.durations = List.replicate M 0 ∧ s.work = 71 + M * (19 * n + 7) + 1 + 1 ∧
    s.core.ptrs 0 = n ∧ s.core.ptrs 1 = M ∧ s.core.ptrs 2 = 4 * n ∧ s.core.ptrs 3 = M ∧
    s.core.ptrs 10 = 0 ∧ s.core.ptrs 11 = 1 ∧ s.core.ptrs 12 = pEnd k n M ∧
    s.core.ptrs 18 = 3 * k + 3 ∧ s.core.ptrs 43 = 3 ∧ s.core.ptrs 45 = 2 ∧ s.core.ptrs 46 = k ∧
    s.core.ptrs 47 = 4 ∧ s.core.regs 4 = 4 ∧ s.core.regs 6 = 1 / M ∧
    (∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) ∧ Tab s.intMem ∧ SampMem k n M G s.intMem := by
  intro s
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ :=
    st0_facts k n M ε δ
  have w0 := st0_work k n M ε δ
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := iterOuter_frame M G (st0 k n M ε δ) a3
  obtain ⟨m1, m2⟩ := iterOuter_mem M G (st0 k n M ε δ) a3 a5
  have hs : s = ains (.core (.pcopy 12 4)) (tick (iterOuter M G (st0 k n M ε δ))) := rfl
  have fp : ∀ q, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 12 →
      s.core.ptrs q = (st0 k n M ε δ).core.ptrs q := by
    intro q b1 b2 b3 b4 b5 b6 b7 b8
    rw [hs]; simp only [ains, tick_core, Function.update_of_ne b8]; exact f6 q b1 b2 b3 b4 b5 b6 b7
  have mem_eq : s.intMem = (iterOuter M G (st0 k n M ε δ)).intMem := by rw [hs]; rfl
  have low : ∀ z, z < cSAMP k → s.intMem z = mem0 n M z := by
    intro z hz; rw [mem_eq, m2 z (Or.inl (by rw [a7]; exact hz)), a20]
  have regs_eq : s.core.regs = (st0 k n M ε δ).core.regs := by rw [hs]; simp only [ains, tick_core]; exact f4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; simp only [ains_output', tick_output]; rw [f1, a1]
  · rw [hs]; simp only [ains, tick_durations]; rw [f2, a2, a15]; simp
  · rw [hs]; simp only [ains, tick_work]; rw [f3, w0]
  · rw [fp 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a3]
  · rw [fp 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a4]
  · rw [fp 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a5]
  · rw [hs]; simp only [ains, tick_core, Function.update_of_ne (show (3 : ℕ) ≠ 12 by norm_num)]; rw [f7, a6]; simp
  · rw [fp 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a8]
  · rw [fp 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a9]
  · rw [hs]; simp only [ains, tick_core, Function.update_self]; rw [f8, a7, a5, pEnd]; ring
  · rw [fp 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a10]
  · rw [fp 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a11]
  · rw [fp 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a12]
  · rw [fp 46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a13]
  · rw [fp 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), a14]
  · rw [regs_eq, a16]
  · rw [regs_eq, a18]
  · intro i hi
    rw [low _ (by unfold cSAMP cDIG; push_cast; omega), mem0_high _ _ _ (by unfold cDIG; push_cast; omega)]
  · intro x y
    have h1 : (4 : ℤ) + 4 * (x : ℕ) + (y : ℕ) < cSAMP k := by
      unfold cSAMP; have := x.isLt; have := y.isLt; push_cast; omega
    have h2 : (20 : ℤ) + 4 * (x : ℕ) + (y : ℕ) < cSAMP k := by
      unfold cSAMP; have := x.isLt; have := y.isLt; push_cast; omega
    rw [low _ h1, low _ h2]; exact tab_mem0 n M x y
  · intro i x
    rw [mem_eq]
    have := m1 i x
    rw [a7] at this
    exact this

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma validD_congr (k n : ℕ) (D D' : ℕ → ℕ) (hD : InRange k n D) (h : ∀ i ≤ 3 * k, D i = D' i) :
    validD k D ↔ validD k D' := by
  have hs := s_le hD
  have h0 : D 0 = D' 0 := h 0 (by omega)
  unfold validD
  constructor
  · intro hv r hr
    obtain ⟨a, b⟩ := hv r hr
    rw [← h0, ← h (1 + r) (by omega), ← h (1 + k + r) (by omega), ← h (1 + 2 * k + r) (by omega)]
    refine ⟨a, fun hr' => ⟨(b hr').1, fun hr'' => ?_⟩⟩
    rw [← h (1 + (r + 1)) (by omega)]; exact (b hr').2 hr''
  · intro hv r hr
    obtain ⟨a, b⟩ := hv r hr
    rw [← h0, ← h (1 + r) (by omega), ← h (1 + k + r) (by omega), ← h (1 + 2 * k + r) (by omega)] at a b
    refine ⟨a, fun hr' => ⟨(b hr').1, fun hr'' => ?_⟩⟩
    have := (b hr').2 hr''
    rw [← h (1 + (r + 1)) (by omega)] at this; exact this

lemma pairOf_congr (k n : ℕ) (D D' : ℕ → ℕ) (hD : InRange k n D) (h : ∀ i ≤ 3 * k, D i = D' i) :
    pairOf n k D = pairOf n k D' := by
  classical
  have hs := s_le hD
  have h0 : D 0 = D' 0 := h 0 (by omega)
  have hp : ∀ (i : ℕ) (r : ℕ), (r < D 0 ∧ D (1 + r) = i) ↔ (r < D' 0 ∧ D' (1 + r) = i) := by
    intro i r
    constructor
    · rintro ⟨a, b⟩; exact ⟨h0 ▸ a, by rw [← h (1 + r) (by omega)]; exact b⟩
    · rintro ⟨a, b⟩; exact ⟨h0 ▸ a, by rw [h (1 + r) (by omega)]; exact b⟩
  have key : ∀ (i : ℕ) (hex : ∃ r, r < D 0 ∧ D (1 + r) = i) (hex' : ∃ r, r < D' 0 ∧ D' (1 + r) = i),
      Nat.find hex = Nat.find hex' := by
    intro i hex hex'
    apply le_antisymm
    · exact Nat.find_min' hex ((hp i _).mpr (Nat.find_spec hex'))
    · exact Nat.find_min' hex' ((hp i _).mp (Nat.find_spec hex))
  unfold pairOf
  ext i
  · simp only
    by_cases hex : ∃ r, r < D 0 ∧ D (1 + r) = (i : ℕ)
    · have hex' : ∃ r, r < D' 0 ∧ D' (1 + r) = (i : ℕ) := by
        obtain ⟨r, hr⟩ := hex; exact ⟨r, (hp i r).mp hr⟩
      rw [dif_pos hex, dif_pos hex']
      show D (1 + k + Nat.find hex) % 4 = D' (1 + k + Nat.find hex') % 4
      rw [← key i hex hex']
      have := (Nat.find_spec hex).1
      rw [h (1 + k + Nat.find hex) (by omega)]
    · have hex' : ¬ ∃ r, r < D' 0 ∧ D' (1 + r) = (i : ℕ) := by
        rintro ⟨r, hr⟩; exact hex ⟨r, (hp i r).mpr hr⟩
      rw [dif_neg hex, dif_neg hex']
  · simp only
    by_cases hex : ∃ r, r < D 0 ∧ D (1 + r) = (i : ℕ)
    · have hex' : ∃ r, r < D' 0 ∧ D' (1 + r) = (i : ℕ) := by
        obtain ⟨r, hr⟩ := hex; exact ⟨r, (hp i r).mp hr⟩
      rw [dif_pos hex, dif_pos hex']
      show D (1 + 2 * k + Nat.find hex) % 4 = D' (1 + 2 * k + Nat.find hex') % 4
      rw [← key i hex hex']
      have := (Nat.find_spec hex).1
      rw [h (1 + 2 * k + Nat.find hex) (by omega)]
    · have hex' : ¬ ∃ r, r < D' 0 ∧ D' (1 + r) = (i : ℕ) := by
        rintro ⟨r, hr⟩; exact hex ⟨r, (hp i r).mpr hr⟩
      rw [dif_neg hex, dif_neg hex']

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma recCell_valid (k n j : ℕ) (hv : validD k (Dseq k n j)) (i : ℕ) : recCell k n j i = Dseq k n j i := by
  unfold recCell; split_ifs with h
  · subst h; rfl
  · rfl

open Classical in
lemma decode_H (k n M : ℕ) (hn : 1 ≤ n) (H : MState) (p : ℤ) (T : ℕ → ℂ)
    (hout : H.output = some p) (hcnt : H.intMem p = Kc k n)
    (hrec : ∀ j < Kc k n, ∀ i ≤ 3 * k, H.intMem (recAddr k p j + i) = recCell k n j i)
    (hval : ∀ j < Kc k n, validD k (Dseq k n j) →
      H.core.mem (recAddr k p j + (3 * k + 1)) = (T j).re * (1 / M) ∧
      H.core.mem (recAddr k p j + (3 * k + 1) + 1) = (T j).im * (1 / M))
    (Q : Pauli n × Pauli n) (hQ : (pairSupport Q).card ≤ k) :
    ∃ j0 < Kc k n, pairOf n k (Dseq k n j0) = Q ∧ decode n k H Q = T j0 * (1 / (M : ℂ)) := by
  obtain ⟨D, hD, hvD, hDQ⟩ := exists_code hn Q hQ
  obtain ⟨j0, hj0, hagree⟩ := Dseq_surj k n hn D hD
  have hD0 := Dseq_inRange k n hn j0
  have hv0 : validD k (Dseq k n j0) := (validD_congr k n D _ hD (fun i hi => (hagree i hi).symm)).mp hvD
  have hQ0 : pairOf n k (Dseq k n j0) = Q := by
    rw [← hDQ]; exact pairOf_congr k n _ _ hD0 hagree
  refine ⟨j0, hj0, hQ0, ?_⟩
  have hb : ∀ j : ℕ, p + 1 + (j : ℤ) * (3 * k + 3) = recAddr k p j := fun j => rfl
  have hrp : ∀ j < Kc k n, recordPair n k H.intMem (recAddr k p j) =
      if validD k (Dseq k n j) then some (pairOf n k (Dseq k n j)) else none := by
    intro j hj
    split_ifs with hv
    · apply recordPair_valid (Dseq_inRange k n hn j) hv
      intro i hi; rw [hrec j hj i hi, recCell_valid k n j hv]
    · apply recordPair_invalid
      have := hrec j hj 0 (by omega)
      simp only [Nat.cast_zero, add_zero] at this
      rw [this]; unfold recCell; simp [hv]
  unfold decode
  rw [hout]
  simp only []
  rw [hcnt, Int.toNat_natCast]
  rw [Finset.sum_eq_single j0]
  · simp only [hb, hrp j0 hj0, if_pos hv0, hQ0]
    rw [if_pos trivial]
    obtain ⟨v1, v2⟩ := hval j0 hj0 hv0
    rw [show recAddr k p j0 + 3 * k + 1 = recAddr k p j0 + (3 * k + 1) by ring,
      show recAddr k p j0 + 3 * k + 2 = recAddr k p j0 + (3 * k + 1) + 1 by ring, v1, v2]
    apply Complex.ext <;> simp
  · intro j hj hne
    rw [Finset.mem_range] at hj
    simp only [hb, hrp j hj]
    by_cases hv : validD k (Dseq k n j)
    · rw [if_pos hv]
      by_cases h : some (pairOf n k (Dseq k n j)) = some Q
      · exfalso; apply hne
        have hpq : pairOf n k (Dseq k n j) = pairOf n k (Dseq k n j0) := by
          rw [hQ0]; exact Option.some_injective _ h
        exact Dseq_inj k n hn j j0 hj hj0
          (code_unique _ _ (Dseq_inRange k n hn j) hv hD0 hv0 hpq)
      · rw [if_neg h]
    · rw [if_neg hv, if_neg (by simp)]
  · intro h; exact absurd (Finset.mem_range.mpr hj0) h

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.FourierAux
open LindbladTolerant.Testing LindbladStructLearn

lemma tens_mul {n : ℕ} (a b : Fin n → Op Bool) :
    tens a * tens b = tens (fun i => a i * b i) := by
  ext x z
  simp only [tens, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

lemma tens_conjTranspose {n : ℕ} (a : Fin n → Op Bool) :
    (tens a)ᴴ = tens (fun i => (a i)ᴴ) := by
  ext x y
  simp [tens, Matrix.conjTranspose_apply]

lemma tens_trace {n : ℕ} (a : Fin n → Op Bool) :
    (tens a).trace = ∏ i, (a i).trace := by
  simp only [Matrix.trace, Matrix.diag, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end LindbladStructLearn.FourierAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

end LindbladStructLearn.AAux

namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma sum_tens (F : Fin n → Bool → Op Bool) :
    ∑ w : Qubits n, tens (fun i => F i (w i)) = tens (fun i => ∑ b, F i b) := by
  ext x y
  simp only [tens, Matrix.sum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma eigenProj_eq (A : Pauli n) (v : Qubits n) :
    eigenProj A v = tens (fun i => oneEigenProj (A i) (v i)) := rfl

lemma one_eigen_sum (a : Fin 4) :
    ∑ b : Bool, oneEigenProj a b = 1 := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;>
    simp [oneEigenProj, onePauli, Fintype.sum_bool] <;> norm_num

end LindbladStructLearn.AAux

namespace LindbladStructLearn

open LindbladTolerant.Testing LindbladStructLearn.FourierAux LindbladStructLearn.AAux

variable {n : ℕ}

lemma oneEigenProj_conjTranspose (a : Fin 4) (b : Bool) :
    (oneEigenProj a b)ᴴ = oneEigenProj a b := by
  ext x y
  fin_cases a <;> cases b <;> cases x <;> cases y <;>
    simp [oneEigenProj, onePauli, Matrix.conjTranspose_apply] <;> norm_num

lemma oneEigenProj_mul_self (a : Fin 4) (b : Bool) :
    oneEigenProj a b * oneEigenProj a b = oneEigenProj a b := by
  ext x y
  fin_cases a <;> cases b <;> cases x <;> cases y <;>
    simp [oneEigenProj, onePauli, Matrix.mul_apply] <;> ring_nf <;>
    simp [Complex.ext_iff] <;> norm_num

lemma oneEigenProj_trace (a : Fin 4) (b : Bool) : (oneEigenProj a b).trace = 1 := by
  fin_cases a <;> cases b <;>
    simp [oneEigenProj, onePauli, Matrix.trace] <;> norm_num

lemma eigenProj_eq_conjTranspose_mul_self (A : Pauli n) (v : Qubits n) :
    eigenProj A v = (eigenProj A v)ᴴ * eigenProj A v := by
  rw [eigenProj_eq, tens_conjTranspose, tens_mul]
  simp_rw [oneEigenProj_conjTranspose, oneEigenProj_mul_self]

lemma eigenProj_posSemidef (A : Pauli n) (v : Qubits n) : (eigenProj A v).PosSemidef := by
  rw [eigenProj_eq_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma eigenProj_trace (A : Pauli n) (v : Qubits n) : (eigenProj A v).trace = 1 := by
  rw [eigenProj_eq, tens_trace]
  simp [oneEigenProj_trace]

lemma eigenProj_sum (B : Pauli n) : ∑ w : Qubits n, eigenProj B w = 1 := by
  simp_rw [eigenProj_eq]
  rw [sum_tens (fun i b => oneEigenProj (B i) b)]
  simp_rw [one_eigen_sum]
  ext x y
  simp only [tens, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- A completely positive map sends PSD matrices to PSD matrices (ancilla of size 1). -/
lemma applySuper_posSemidef_of_isCP (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsCP Φ)
    (X : Op (Qubits n)) (hX : X.PosSemidef) : (applySuper Φ X).PosSemidef := by
  have hx : (X.submatrix (Prod.fst : Qubits n × Fin 1 → Qubits n) Prod.fst).PosSemidef :=
    hX.submatrix _
  have h := (hΦ 1 _ hx).submatrix (fun i : Qubits n => (i, (0 : Fin 1)))
  convert h using 1
  ext i j
  rfl

theorem bornAmp_nonneg (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) (w : Qubits n) : 0 ≤ bornAmp Φ A v B w := by
  have hY := applySuper_posSemidef_of_isCP Φ hΦ.1 _ (eigenProj_posSemidef A v)
  rw [bornAmp, eigenProj_eq_conjTranspose_mul_self B w, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc]
  have := (hY.mul_mul_conjTranspose_same (eigenProj B w)).trace_nonneg
  rwa [Matrix.mul_assoc] at this

theorem bornAmp_sum (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) : ∑ w : Qubits n, bornAmp Φ A v B w = 1 := by
  simp only [bornAmp]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, eigenProj_sum, Matrix.one_mul, hΦ.2,
    eigenProj_trace]

lemma bornAmp_re_nonneg (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) (w : Qubits n) : 0 ≤ (bornAmp Φ A v B w).re :=
  (Complex.nonneg_iff.1 (bornAmp_nonneg Φ hΦ A v B w)).1

lemma bornAmp_re_sum (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) : ∑ w : Qubits n, (bornAmp Φ A v B w).re = 1 := by
  rw [← Complex.re_sum, bornAmp_sum Φ hΦ, Complex.one_re]

end LindbladStructLearn

namespace LindbladStructLearn.Hoeff

open Classical


variable {X : Type*} [Fintype X]

omit [Fintype X] in
/-- The product weights are nonnegative. -/
theorem prod_weight_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) {M : ℕ} (ω : Fin M → X) :
    0 ≤ ∏ i, p (ω i) :=
  Finset.prod_nonneg fun i _ => hp (ω i)

end LindbladStructLearn.Hoeff

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

lemma pw_nonneg (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (x : Rd n) : 0 ≤ pw Φ x :=
  mul_nonneg (by positivity) (bornAmp_re_nonneg Φ hΦ _ _ _ _)

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma nat_bound (k n : ℕ) (hn : 1 ≤ n) : 4 * ((k + 1) * n ^ k * 16 ^ k) ≤ (2 * n) ^ (7 * k + 3) := by
  have h1 : k + 1 ≤ 2 ^ (3 * k + 1) := by
    have := Nat.lt_two_pow_self (n := 3 * k + 1); omega
  have h2 : n ^ k ≤ n ^ (7 * k + 3) := Nat.pow_le_pow_right hn (by omega)
  have h3 : (2 * n) ^ (7 * k + 3) = 2 ^ (7 * k + 3) * n ^ (7 * k + 3) := by rw [mul_pow]
  have h4 : 2 ^ (7 * k + 3) = 4 * 16 ^ k * 2 ^ (3 * k + 1) := by
    rw [show 16 = 2 ^ 4 by rfl, ← pow_mul, show 4 = 2 ^ 2 by rfl, ← pow_add, ← pow_add]; congr 1; ring
  rw [h3, h4]
  calc 4 * ((k + 1) * n ^ k * 16 ^ k) = 4 * 16 ^ k * ((k + 1) * n ^ k) := by ring
    _ ≤ 4 * 16 ^ k * (2 ^ (3 * k + 1) * n ^ (7 * k + 3)) := by gcongr
    _ = _ := by ring

lemma exp_bound (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (M : ℕ) (hM : (65536 : ℝ) ^ k * Real.log (2 * n / δ) / ε ^ 2 ≤ M) :
    4 * (Kc k n : ℝ) * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤ δ := by
  set L := Real.log (2 * n / δ) with hL
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 < 2 * n / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hL0 : 0 < L := Real.log_pos hx
  have hMe : (65536 : ℝ) ^ k * L ≤ M * ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hM; linarith
  set m := 7 * k + 3 with hm
  -- exponent comparison
  have ha : (m : ℝ) * L ≤ M * ε ^ 2 / (64 * 16 ^ k) := by
    rw [le_div_iff₀ (by positivity)]
    have h16 : (65536 : ℝ) ^ k = 4096 ^ k * 16 ^ k := by rw [← mul_pow]; norm_num
    have hb : (64 : ℝ) * m ≤ 4096 ^ k := by
      have : (4096 : ℝ) ^ k ≥ 1 + k * 4095 := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 4095 by norm_num) k
        norm_num at this; linarith
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      simp only [hm]; push_cast; nlinarith
    have h16p : (0 : ℝ) < 16 ^ k := by positivity
    calc (m : ℝ) * L * (64 * 16 ^ k) = (64 * m) * 16 ^ k * L := by ring
      _ ≤ 4096 ^ k * 16 ^ k * L := by gcongr
      _ = 65536 ^ k * L := by rw [h16]
      _ ≤ M * ε ^ 2 := hMe
  have hexp : Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤ (δ / (2 * n)) ^ m := by
    have e1 : Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤ Real.exp (-(m * L)) := by
      apply Real.exp_le_exp.mpr; rw [neg_div]; linarith
    have e2 : Real.exp (-(m * L)) = (δ / (2 * n)) ^ m := by
      rw [Real.exp_neg, Real.exp_nat_mul, hL, Real.exp_log (by linarith), ← inv_pow, inv_div]
    linarith
  have hKc : (4 * (Kc k n : ℝ)) ≤ (2 * n) ^ m := by
    rw [Kc_eq]; exact_mod_cast nat_bound k n hn
  have hpos2n : (0 : ℝ) < (2 * n) ^ m := by positivity
  have hdm : (δ / (2 * n)) ^ m ≤ δ / (2 * n) ^ m := by
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ hpos2n.le
    calc δ ^ m ≤ δ ^ 1 := pow_le_pow_of_le_one hδ.le hδ1.le (by omega)
      _ = δ := pow_one δ
  calc 4 * (Kc k n : ℝ) * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k))
      ≤ (2 * n) ^ m * (δ / (2 * n) ^ m) := by
        apply mul_le_mul hKc (hexp.trans hdm) (Real.exp_pos _).le hpos2n.le
    _ = δ := by field_simp

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma branches_dur (s : MState) : ∀ b ∈ branches P n evo s, s.durations.length ≤ b.2.durations.length := by
  intro b hb
  unfold branches at hb
  split_ifs at hb with h1
  · simp at hb; rw [hb]
  · revert hb
    rcases hP : P[s.core.pc]? with _ | ins
    · simp; intro hb; rw [hb]
    · rcases ins with c | _ | _ | _ | _ | _ | _ | _ | _ <;> simp only [hP]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rw [hb]
      · intro hb; simp at hb; rcases hb with hb | hb <;> rw [hb]
      · split_ifs
        · intro hb; simp at hb; rw [hb]
        · intro hb; simp only [List.mem_map] at hb
          obtain ⟨w, _, rfl⟩ := hb
          simp
      · intro hb; simp at hb; rw [hb]

lemma branches_pos (hevo : ∀ τ, IsChannel (evo τ)) (s : MState) : ∃ b ∈ branches P n evo s, b.1 ≠ 0 := by
  unfold branches
  split_ifs with h1
  · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
  · rcases hP : P[s.core.pc]? with _ | ins
    · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
    · rcases ins with c | _ | _ | _ | _ | _ | _ | _ | _ <;> simp only
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
      · exact ⟨_, List.mem_cons_self, by simp⟩
      · split_ifs
        · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩
        · rename_i addr tm _
          set τ := s.core.regs tm
          set A : Pauli n := fun i => ⟨(s.intMem (s.core.ptrs addr + i)).toNat % 4, Nat.mod_lt _ (by norm_num)⟩
          set v : Qubits n := fun i => decide (s.intMem (s.core.ptrs addr + (n + i)) = 1)
          set B : Pauli n := fun i => ⟨(s.intMem (s.core.ptrs addr + (2 * n + i))).toNat % 4,
            Nat.mod_lt _ (by norm_num)⟩
          have hsum := bornAmp_re_sum (evo τ) (hevo τ) A v B
          obtain ⟨w, -, hw⟩ : ∃ w ∈ (Finset.univ : Finset (Qubits n)), 0 < (bornAmp (evo τ) A v B w).re := by
            by_contra hc
            push Not at hc
            have : ∑ w : Qubits n, (bornAmp (evo τ) A v B w).re ≤ 0 :=
              Finset.sum_nonpos fun w hw => hc w hw
            linarith
          refine ⟨_, List.mem_map.mpr ⟨w, Finset.mem_toList.mpr (Finset.mem_univ w), rfl⟩, ?_⟩
          simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact hw
      · exact ⟨_, List.mem_singleton_self _, one_ne_zero⟩

lemma reach_dur : ∀ (m : ℕ) (s x : MState), Reach P n evo m s x → s.durations.length ≤ x.durations.length := by
  intro m
  induction m with
  | zero => intro s x h; simp only [Reach] at h; rw [h]
  | succ m ih =>
    intro s x h
    rw [reach_succ] at h
    obtain ⟨b, hb, -, hr⟩ := h
    exact (branches_dur s b hb).trans (ih _ _ hr)

lemma reach_ext (hevo : ∀ τ, IsChannel (evo τ)) : ∀ (d : ℕ) (s : MState), ∃ y, Reach P n evo d s y := by
  intro d
  induction d with
  | zero => intro s; exact ⟨s, rfl⟩
  | succ d ih =>
    intro s
    obtain ⟨b, hb, hb0⟩ := branches_pos (P := P) hevo s
    obtain ⟨y, hy⟩ := ih b.2
    exact ⟨y, by rw [reach_succ]; exact ⟨b, hb, hb0, hy⟩⟩

lemma reach_add (b : ℕ) : ∀ (a : ℕ) (s x : MState),
    Reach P n evo (a + b) s x ↔ ∃ y, Reach P n evo a s y ∧ Reach P n evo b y x := by
  intro a
  induction a with
  | zero => intro s x; simp only [zero_add, Reach]; exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨y, hy, h⟩ => hy ▸ h⟩
  | succ a ih =>
    intro s x
    rw [show a + 1 + b = (a + b) + 1 by ring, reach_succ]
    constructor
    · rintro ⟨br, hbr, h0, hr⟩
      obtain ⟨y, h1, h2⟩ := (ih br.2 x).mp hr
      exact ⟨y, by rw [reach_succ]; exact ⟨br, hbr, h0, h1⟩, h2⟩
    · rintro ⟨y, h1, h2⟩
      rw [reach_succ] at h1
      obtain ⟨br, hbr, h0, hr⟩ := h1
      exact ⟨br, hbr, h0, (ih br.2 x).mpr ⟨y, hr, h2⟩⟩

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma Stmt.adm_comp (st : Stmt) (h : st.Adm) : ∀ base, ∀ op ∈ st.comp base, AdmI op := by
  induction st with
  | ins i => intro base op hop; simp [Stmt.comp] at hop; subst hop; exact h
  | seq a b iha ihb =>
    intro base op hop; simp only [Stmt.comp, List.mem_append] at hop
    rcases hop with hop | hop
    · exact iha h.1 _ op hop
    · exact ihb h.2 _ op hop
  | loop x y b ih =>
    intro base op hop; simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hop
    rcases hop with (hop | hop) | hop
    · subst hop; trivial
    · exact ih h _ op hop
    · subst hop; trivial
  | ite x y a b iha ihb =>
    intro base op hop; simp only [Stmt.comp, List.mem_append, List.mem_singleton] at hop
    rcases hop with ((hop | hop) | hop) | hop
    · subst hop; trivial
    · exact ihb h.2 _ op hop
    · subst hop; trivial
    · exact iha h.1 _ op hop

end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma seqs_adm (l : List Stmt) (h : ∀ st ∈ l, st.Adm) : (seqs l).Adm := by
  induction l with
  | nil => simp [seqs, skip, Stmt.Adm, pcopy, AdmI]
  | cons a l ih =>
    cases l with
    | nil => simpa [seqs] using h
    | cons b l' =>
      simp only [seqs]
      exact ⟨h a (by simp), ih (fun st hs => h st (by simp [hs]))⟩

lemma admissible_prog (k : ℕ) : Admissible (prog k) := by
  have h0 : (S0 k).Adm := by
    unfold S0
    apply seqs_adm
    intro st hst
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_nil_iff, or_false] at hst
    rcases hst with (h | h) | h
    · rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
        simp [Stmt.Adm, iload, pset, padd, AdmI]
    · obtain ⟨e, -, rfl⟩ := h
      apply seqs_adm; intro st hst; simp at hst
      rcases hst with h | h | h <;> subst h <;> simp [Stmt.Adm, pset, istore, AdmI]
    · rcases h with h | h | h | h | h | h <;> subst h <;>
        simp [Stmt.Adm, rconst, preal, rdiv, pset, AdmI]
      · exact ⟨4, by norm_num⟩
      · exact ⟨1, by norm_num⟩
  have h2 : (S2 k).Adm := by
    simp [S2, body2, copyBody, validBody, within, beyond, inval, odoBody, seqs, Stmt.Adm, iload, pset,
      padd, istore, pinc, pdec, pcopy, skip, AdmI]
  have h3 : (S3 k).Adm := by
    simp [S3, body3, core3, sampBody, siteBody, caseE, seqs, Stmt.Adm, iload, pset, padd, psub, istore,
      pinc, rconst, rmul, radd, rsub, rstore, skip, pcopy, AdmI]
    exact ⟨⟨1, by norm_num⟩, ⟨0, by norm_num⟩⟩
  intro op hop
  rw [prog_eq] at hop
  simp only [List.mem_append, List.mem_singleton] at hop
  rcases hop with h | h | h | h | h
  · exact (S0 k).adm_comp h0 0 op h
  · simp [S1] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h <;> subst h <;> trivial
  · exact (S2 k).adm_comp h2 96 op h
  · exact (S3 k).adm_comp h3 191 op h
  · subst h; trivial

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

lemma wt_eq (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (x : Rd n) :
    wt (fun _ => Φ) x.1 x.2 = ENNReal.ofReal (pw Φ x) := by
  unfold wt pw
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

lemma work_bound (k n M : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hM : 1 ≤ M) :
    73 + M * (19 * n + 7) + mB k n M ≤ 400 * (k + 1) ^ 2 * 16 ^ k * M * n ^ k := by
  unfold mB
  rw [Kc_eq]
  have h1 : n ≤ n ^ k := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ k := Nat.pow_le_pow_right hn hk
  have h2 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
  have h3 : 1 ≤ 16 ^ k := Nat.one_le_pow _ _ (by norm_num)
  set A := n ^ k
  set B := 16 ^ k
  have hA : A ≤ M * A := Nat.le_mul_of_pos_left A (by omega)
  have hMA : 1 ≤ M * A := le_trans h2 hA
  have hkB : 1 ≤ (k + 1) * B := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e1 : 82 ≤ 82 * (M * A) := by omega
  have e2 : M * (19 * n + 7) ≤ 26 * (M * A) := by
    have : 19 * n + 7 ≤ 26 * A := by omega
    calc M * (19 * n + 7) ≤ M * (26 * A) := Nat.mul_le_mul_left _ this
      _ = 26 * (M * A) := by ring
  have e3 : (k + 1) * A * B * (130 * k + 62) ≤ (k + 1) * B * (130 * k + 62) * (M * A) := by
    calc (k + 1) * A * B * (130 * k + 62) = (k + 1) * B * (130 * k + 62) * A := by ring
      _ ≤ (k + 1) * B * (130 * k + 62) * (M * A) := Nat.mul_le_mul_left _ hA
  have e4 : (k + 1) * A * B * (4 * k + 32) ≤ (k + 1) * B * (4 * k + 32) * (M * A) := by
    calc (k + 1) * A * B * (4 * k + 32) = (k + 1) * B * (4 * k + 32) * A := by ring
      _ ≤ (k + 1) * B * (4 * k + 32) * (M * A) := Nat.mul_le_mul_left _ hA
  have e5 : 108 + (k + 1) * B * (204 * k + 126) ≤ (k + 1) * B * (400 * (k + 1)) := by
    have : 108 ≤ (k + 1) * B * 108 := by
      calc 108 = 1 * 108 := by ring
        _ ≤ (k + 1) * B * 108 := Nat.mul_le_mul_right _ hkB
    have : (k + 1) * B * (204 * k + 126) + (k + 1) * B * 108 ≤ (k + 1) * B * (400 * (k + 1)) := by
      rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
    omega
  calc 73 + M * (19 * n + 7) + ((k + 1) * A * B * (130 * k + 62) + 5 +
        ((k + 1) * A * B * (M * (70 * k + 32) + 4 * k + 32) + 3) + 1)
      = 82 + M * (19 * n + 7) + (k + 1) * A * B * (130 * k + 62) +
        (k + 1) * B * (70 * k + 32) * (M * A) + (k + 1) * A * B * (4 * k + 32) := by ring
    _ ≤ 82 * (M * A) + 26 * (M * A) + (k + 1) * B * (130 * k + 62) * (M * A) +
        (k + 1) * B * (70 * k + 32) * (M * A) + (k + 1) * B * (4 * k + 32) * (M * A) := by
        gcongr
    _ = (M * A) * (108 + (k + 1) * B * (204 * k + 126)) := by ring
    _ ≤ (M * A) * ((k + 1) * B * (400 * (k + 1))) := Nat.mul_le_mul_left _ e5
    _ = 400 * (k + 1) ^ 2 * B * M * A := by ring

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

theorem lemma_2_10_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ C' : ℝ, 0 < C' ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ M : ℕ,
      C ^ k * Real.log (2 * n / δ) / ε ^ 2 ≤ M →
      ∀ Φ : Super (Qubits n) (Qubits n), IsChannel Φ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun _ => Φ
        let N : ℕ := ⌈C' * M * (n : ℝ) ^ k⌉₊
        (∀ s, Reach P n evo N (alg1Input n M ε δ) s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N (alg1Input n M ε δ) (fun s => Halted s ∧
          ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k →
            ‖decode n k s Q - locFourier Φ Q‖ ≤ ε) ∧
        ∀ (M' : ℕ) (s : MState), Reach P n evo M' (alg1Input n M ε δ) s →
          s.durations.length ≤ M := by
  refine ⟨65536, by norm_num, fun k hk => ⟨400 * (k + 1) ^ 2 * 16 ^ k, by positivity, prog k,
    admissible_prog k, fun n hn ε hε δ hδ hδ1 M hM Φ hΦ => ?_⟩⟩
  intro evo N
  -- basic facts
  have hL : 0 < Real.log (2 * n / δ) := by
    apply Real.log_pos; rw [lt_div_iff₀ hδ]; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < 65536 ^ k * Real.log (2 * n / δ) / ε ^ 2 := by positivity
    have : (0 : ℝ) < M := lt_of_lt_of_le this hM
    exact_mod_cast this
  have hevo : ∀ τ, IsChannel (evo τ) := fun _ => hΦ
  -- the bound
  have hWN : 73 + M * (19 * n + 7) + mB k n M ≤ N := by
    have h := work_bound k n M hk hn hM1
    have : ((73 + M * (19 * n + 7) + mB k n M : ℕ) : ℝ) ≤ 400 * (k + 1) ^ 2 * 16 ^ k * M * (n : ℝ) ^ k := by
      exact_mod_cast h
    exact Nat.cast_le.mp (this.trans (Nat.le_ceil _))
  -- the tails
  choose Hf mf hmf hmass hreach hhalt hout hdur hwork hcnt hrec hval using
    fun G : Fin M → Rd n => tail (evo := evo) k M hn ε δ G
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ :=
    st0_facts k n M ε δ
  set s0 := st0 k n M ε δ
  have hpre : s0.core.ptrs 3 + M ≤ s0.core.ptrs 1 := by rw [a6, a4]; simp
  -- decomposition of N
  set N1 := N - 71 - M * (18 * n + 7) with hN1
  have hN : N = N1 + M * (18 * n + 7) + 71 := by
    have : 71 + M * (18 * n + 7) ≤ N := by
      have : M * (18 * n + 7) ≤ M * (19 * n + 7) := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  have hN1b : ∀ G, mf G + 2 ≤ N1 := by
    intro G; have := hmf G
    have : M * (18 * n + 7) ≤ M * (19 * n + 7) := Nat.mul_le_mul_left _ (by omega)
    unfold mB at hWN; omega
  have hsEnd : ∀ G : Fin M → Rd n, (iterOuter M G s0).output = none ∧
      (iterOuter M G s0).core.ptrs 1 ≤ (iterOuter M G s0).core.ptrs 3 := by
    intro G
    obtain ⟨f1, -, -, -, -, f6, f7, -⟩ := iterOuter_frame M G s0 a3
    refine ⟨by rw [f1, a1], ?_⟩
    rw [f6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      f7, a4, a6]; simp
  -- reach characterization
  have hreachN : ∀ x, Reach (prog k) n evo N (alg1Input n M ε δ) x → ∃ G, x = Hf G := by
    intro x hx
    rw [hN, (S0_run k n M ε δ).reach] at hx
    obtain ⟨G, hG⟩ := outerLoop_reach k N1 x M s0 a1 a3 a15 hpre hx
    refine ⟨G, ?_⟩
    have e1 : N1 = (N1 - 2 - mf G) + mf G + 2 := by have := hN1b G; omega
    rw [e1, exit_reach k _ x _ (hsEnd G).1 (hsEnd G).2] at hG
    rw [show exitSt (iterOuter M G s0) = xEnd k n M ε δ G from rfl, hreach G, reach_halted (hhalt G)] at hG
    exact hG
  refine ⟨?_, ?_, ?_⟩
  -- (1) halting and work
  · intro s hs
    obtain ⟨G, rfl⟩ := hreachN s hs
    refine ⟨hhalt G, ?_⟩
    rw [hwork G]
    obtain ⟨-, -, x3, -⟩ := xEnd_facts k n M ε δ G
    have := hmf G
    unfold mB at hWN this
    omega
  -- (2) success probability
  · classical
    set E : MState → Prop := fun s => Halted s ∧ ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k →
      ‖decode n k s Q - locFourier Φ Q‖ ≤ ε with hE
    have hmassN : mass (prog k) n evo N (alg1Input n M ε δ) E =
        ∑ G : Fin M → Rd n, (∏ i, wt evo (G i).1 (G i).2) * (if E (Hf G) then 1 else 0) := by
      rw [hN, (S0_run k n M ε δ).mass, outerLoop_mass k N1 E M s0 a1 a3 a15 hpre]
      refine Finset.sum_congr rfl fun G _ => ?_
      congr 1
      have e1 : N1 = (N1 - 2 - mf G) + mf G + 2 := by have := hN1b G; omega
      rw [e1, exit_mass k _ E _ (hsEnd G).1 (hsEnd G).2]
      rw [show exitSt (iterOuter M G s0) = xEnd k n M ε δ G from rfl, hmass G, mass_halted (hhalt G)]
    -- good samples succeed
    have hgood : ∀ G : Fin M → Rd n, (∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k →
        ‖avg G Q - locFourier Φ Q‖ ≤ ε) → E (Hf G) := by
      intro G hG
      refine ⟨hhalt G, fun Q hQ => ?_⟩
      obtain ⟨j0, hj0, hQ0, hdec⟩ := decode_H k n M hn (Hf G) (pEnd k n M) (tsum k n M G) (hout G) (hcnt G)
        (hrec G) (hval G) Q hQ
      rw [hdec]
      have : tsum k n M G j0 * (1 / (M : ℂ)) = avg G Q := by
        unfold tsum avg; rw [hQ0]; rfl
      rw [this]; exact hG Q hQ
    have hpg := prob_good Φ hΦ k hn M (by omega) ε hε
    have heb := exp_bound k n hk hn ε δ hε hδ hδ1 M hM
    -- convert to ENNReal
    have hwt : ∀ G : Fin M → Rd n, (∏ i, wt evo (G i).1 (G i).2) = ENNReal.ofReal (∏ i, pw Φ (G i)) := by
      intro G
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pw_nonneg Φ hΦ _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact wt_eq Φ hΦ (G i)
    rw [hmassN]
    calc 1 - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) := by
          rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
            (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
              then (1 : ℝ) else 0)) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ∑ ω : Fin M → Rd n, ENNReal.ofReal ((∏ i, pw Φ (ω i)) *
            (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
              then (1 : ℝ) else 0)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro ω _
          apply mul_nonneg (Hoeff.prod_weight_nonneg _ (pw_nonneg Φ hΦ) ω); split_ifs <;> norm_num
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro G _
          rw [hwt G, ENNReal.ofReal_mul (Hoeff.prod_weight_nonneg _ (pw_nonneg Φ hΦ) G)]
          gcongr
          split_ifs with h1 h2 h2
          · simp
          · exact absurd (hgood G h1) h2
          · simp
          · simp
  -- (3) durations
  · intro M' s hs
    by_cases hle : M' ≤ N
    · obtain ⟨y, hy⟩ := reach_ext (P := prog k) hevo (N - M') s
      have hy' : Reach (prog k) n evo N (alg1Input n M ε δ) y := by
        rw [show N = M' + (N - M') by omega, reach_add]; exact ⟨s, hs, hy⟩
      obtain ⟨G, rfl⟩ := hreachN y hy'
      have := reach_dur _ _ _ hy
      rw [hdur G] at this; simpa using this
    · rw [show M' = N + (M' - N) by omega, reach_add] at hs
      obtain ⟨y, hy, hys⟩ := hs
      obtain ⟨G, rfl⟩ := hreachN y hy
      rw [reach_halted (hhalt G)] at hys
      subst hys; rw [hdur G]; simp

end LindbladStructLearn.Mach.A1


open LindbladTolerant.Testing LindbladStructLearn in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ C' : ℝ, 0 < C' ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ M : ℕ,
      C ^ k * Real.log (2 * n / δ) / ε ^ 2 ≤ M →
      ∀ Φ : Super (Qubits n) (Qubits n), IsChannel Φ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun _ => Φ
        let N : ℕ := ⌈C' * M * (n : ℝ) ^ k⌉₊
        (∀ s, Reach P n evo N (alg1Input n M ε δ) s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N (alg1Input n M ε δ) (fun s => Halted s ∧
          ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k →
            ‖decode n k s Q - locFourier Φ Q‖ ≤ ε) ∧
        ∀ (M' : ℕ) (s : MState), Reach P n evo M' (alg1Input n M ε δ) s →
          s.durations.length ≤ M :=
  LindbladStructLearn.Mach.A1.lemma_2_10_aux
