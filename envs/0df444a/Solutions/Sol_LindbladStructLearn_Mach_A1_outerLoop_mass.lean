-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.outerLoop_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:29.576968+00:00
-- url     : https://prove2.me/submissions/3db0bcc6-1a41-4359-b106-516856914f90

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

lemma mass_succ (N : ℕ) (s : MState) (E : MState → Prop) :
    mass P n evo (N + 1) s E = ((branches P n evo s).map fun b => b.1 * mass P n evo N b.2 E).sum :=
  rfl

/-- a deterministic step: a single branch of weight one -/
lemma mass_det {s s' : MState} (h : branches P n evo s = [(1, s')]) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) s E = mass P n evo N s' E := by
  rw [mass_succ, h]; simp

/-- iterate deterministic steps -/
lemma mass_det_run (f : MState → MState) (m : ℕ) (s : MState)
    (h : ∀ i < m, branches P n evo (f^[i] s) = [(1, f^[i+1] s)]) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + m) s E = mass P n evo N (f^[m] s) E := by
  induction m generalizing N with
  | zero => rfl
  | succ m ih =>
    rw [show N + (m + 1) = (N + 1) + m by ring, ih (fun i hi => h i (by omega)) (N + 1)]
    exact mass_det (h m (by omega)) N E

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

lemma branches_coin {s : MState} {d : ℕ} (h : P[s.core.pc]? = some (.coin d)) (hout : s.output = none) :
    branches P n evo s = [(1 / 2, coinSt s d 0), (1 / 2, coinSt s d 1)] := by
  unfold branches; simp only [hout, Option.isSome_none, Bool.false_eq_true, if_false]; rw [h]
  simp only [coinSt, hout]

lemma mass_coin {s : MState} {d : ℕ} (h : P[s.core.pc]? = some (.coin d)) (hout : s.output = none)
    (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) s E =
      1 / 2 * mass P n evo N (coinSt s d 0) E + 1 / 2 * mass P n evo N (coinSt s d 1) E := by
  rw [mass_succ, branches_coin h hout]; simp

lemma branches_exp {s : MState} {addr tm : ℕ} (h : P[s.core.pc]? = some (.experiment addr tm))
    (hout : s.output = none) (hv : ExpValid n s addr tm) :
    branches P n evo s = (Finset.univ : Finset (Qubits n)).toList.map fun w =>
      (ENNReal.ofReal (bornAmp (evo (s.core.regs tm)) (expA n s addr) (expV n s addr)
        (expB n s addr) w).re, expSt n s addr tm w) := by
  unfold branches
  simp only [hout, Option.isSome_none, Bool.false_eq_true, if_false]
  rw [h]
  simp only
  rw [if_neg]
  · simp only [expSt, hout]; rfl
  · push Not
    refine ⟨hv.1, fun i => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hv.2 i
    have e2 : ((2 : ℤ) * n + i) = 2 * n + i := rfl
    refine ⟨h1, ?_, ?_⟩
    · simpa [add_comm, add_left_comm, add_assoc] using h2
    · simpa [add_assoc] using h3

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

lemma pjle_t' {s : MState} {a x y t : ℕ} (hf : P[(setpc s a).core.pc]? = some (.core (.pjle x y t)))
    (hc : s.core.ptrs x ≤ s.core.ptrs y) : dstep P (setpc s a) = setpc (tick s) t := by
  rw [ds_pjle_t hf hc]; rfl

lemma pjle_f' {s : MState} {a x y t : ℕ} (hf : P[(setpc s a).core.pc]? = some (.core (.pjle x y t)))
    (hc : ¬ s.core.ptrs x ≤ s.core.ptrs y) : dstep P (setpc s a) = setpc (tick s) (a + 1) := by
  rw [ds_pjle_f hf hc]; rfl

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

lemma placed_S1 (k : ℕ) : Placed (prog k) 71 (S1 71) := by
  intro i hi
  rw [prog_eq, List.getElem?_append_right (by rw [Stmt.comp_length, S0_len]; omega),
    Stmt.comp_length, S0_len, show 71 + i - 71 = i by omega, List.getElem?_append_left hi]

lemma fetch_S1 (k i : ℕ) (hi : i < 25) : (prog k)[71 + i]? = (S1 71)[i]? := placed_S1 k i hi

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

lemma f71 (k : ℕ) : (prog k)[71]? = some (.core (.pjle 1 3 95)) := fetch_S1 k 0 (by norm_num)
lemma f72 (k : ℕ) : (prog k)[72]? = some (.core (.pset 5 0)) := fetch_S1 k 1 (by norm_num)
lemma f73 (k : ℕ) : (prog k)[73]? = some (.core (.pjle 0 5 91)) := fetch_S1 k 2 (by norm_num)
lemma f74 (k : ℕ) : (prog k)[74]? = some (.coin 7) := fetch_S1 k 3 (by norm_num)
lemma f75 (k : ℕ) : (prog k)[75]? = some (.coin 8) := fetch_S1 k 4 (by norm_num)
lemma f76 (k : ℕ) : (prog k)[76]? = some (.pointerAdd 9 7 7) := fetch_S1 k 5 (by norm_num)
lemma f77 (k : ℕ) : (prog k)[77]? = some (.pointerAdd 9 9 8) := fetch_S1 k 6 (by norm_num)
lemma f78 (k : ℕ) : (prog k)[78]? = some (.pointerAdd 6 4 5) := fetch_S1 k 7 (by norm_num)
lemma f79 (k : ℕ) : (prog k)[79]? = some (.integerStore 6 9) := fetch_S1 k 8 (by norm_num)
lemma f80 (k : ℕ) : (prog k)[80]? = some (.coin 9) := fetch_S1 k 9 (by norm_num)
lemma f81 (k : ℕ) : (prog k)[81]? = some (.pointerAdd 6 6 0) := fetch_S1 k 10 (by norm_num)
lemma f82 (k : ℕ) : (prog k)[82]? = some (.integerStore 6 9) := fetch_S1 k 11 (by norm_num)
lemma f83 (k : ℕ) : (prog k)[83]? = some (.coin 7) := fetch_S1 k 12 (by norm_num)
lemma f84 (k : ℕ) : (prog k)[84]? = some (.coin 8) := fetch_S1 k 13 (by norm_num)
lemma f85 (k : ℕ) : (prog k)[85]? = some (.pointerAdd 9 7 7) := fetch_S1 k 14 (by norm_num)
lemma f86 (k : ℕ) : (prog k)[86]? = some (.pointerAdd 9 9 8) := fetch_S1 k 15 (by norm_num)
lemma f87 (k : ℕ) : (prog k)[87]? = some (.pointerAdd 6 6 0) := fetch_S1 k 16 (by norm_num)
lemma f88 (k : ℕ) : (prog k)[88]? = some (.integerStore 6 9) := fetch_S1 k 17 (by norm_num)
lemma f89 (k : ℕ) : (prog k)[89]? = some (.core (.pinc 5)) := fetch_S1 k 18 (by norm_num)
lemma f90 (k : ℕ) : (prog k)[90]? = some (.core (.pjle 0 0 73)) := fetch_S1 k 19 (by norm_num)
lemma f91 (k : ℕ) : (prog k)[91]? = some (.experiment 4 0) := fetch_S1 k 20 (by norm_num)
lemma f92 (k : ℕ) : (prog k)[92]? = some (.pointerAdd 4 4 2) := fetch_S1 k 21 (by norm_num)
lemma f93 (k : ℕ) : (prog k)[93]? = some (.core (.pinc 3)) := fetch_S1 k 22 (by norm_num)
lemma f94 (k : ℕ) : (prog k)[94]? = some (.core (.pjle 0 0 71)) := fetch_S1 k 23 (by norm_num)
end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {P : Program} {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma m_coin {t : MState} {a d : ℕ} (hf : P[a]? = some (.coin d)) (hout : t.output = none)
    (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) (setpc t a) E =
      ∑ c : Fin 2, 1 / 2 * mass P n evo N (setpc (cset t d c) (a + 1)) E := by
  rw [mass_coin (s := setpc t a) hf hout, Fin.sum_univ_two]; rfl

lemma m_plain {t : MState} {a : ℕ} {i : Instr} (hf : P[a]? = some i) (hp : Plain i)
    (hout : t.output = none) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) (setpc t a) E = mass P n evo N (setpc (ains i t) (a + 1)) E := by
  have h := branches_det (n := n) (evo := evo) P (setpc t a) i hf (Plain.isDet hp) hout
  rw [mass_det h, dstep_plain hf hp, ains_setpc, setpc_setpc]; rfl

lemma m_jt {t : MState} {a x y tg : ℕ} (hf : P[a]? = some (.core (.pjle x y tg)))
    (hc : t.core.ptrs x ≤ t.core.ptrs y) (hout : t.output = none) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) (setpc t a) E = mass P n evo N (setpc (tick t) tg) E := by
  have h := branches_det (n := n) (evo := evo) P (setpc t a) _ hf trivial hout
  rw [mass_det h, pjle_t' hf hc]

lemma m_jf {t : MState} {a x y tg : ℕ} (hf : P[a]? = some (.core (.pjle x y tg)))
    (hc : ¬ t.core.ptrs x ≤ t.core.ptrs y) (hout : t.output = none) (N : ℕ) (E : MState → Prop) :
    mass P n evo (N + 1) (setpc t a) E = mass P n evo N (setpc (tick t) (a + 1)) E := by
  have h := branches_det (n := n) (evo := evo) P (setpc t a) _ hf trivial hout
  rw [mass_det h, pjle_f' hf hc]

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

lemma inner_mass (k : ℕ) (s : MState) (hout : s.output = none)
    (hc : ¬ s.core.ptrs 0 ≤ s.core.ptrs 5) (N : ℕ) (E : MState → Prop) :
    mass (prog k) n evo (N + 18) (setpc s 73) E =
      ∑ c1 : Fin 2, ∑ c2 : Fin 2, ∑ c3 : Fin 2, ∑ c4 : Fin 2, ∑ c5 : Fin 2,
        1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 * (1 / 2 *
          mass (prog k) n evo N (setpc (innerPost s c1 c2 c3 c4 c5) 73) E)))) := by
  rw [m_jf (f73 k) hc hout]
  simp (disch := simp [hout]) only [m_coin (f74 k), m_coin (f75 k), m_coin (f80 k), m_coin (f83 k),
    m_coin (f84 k), m_plain (f76 k) trivial, m_plain (f77 k) trivial, m_plain (f78 k) trivial,
    m_plain (f79 k) trivial, m_plain (f81 k) trivial, m_plain (f82 k) trivial,
    m_plain (f85 k) trivial, m_plain (f86 k) trivial, m_plain (f87 k) trivial,
    m_plain (f88 k) trivial, m_plain (f89 k) trivial, m_jt (f90 k)]
  simp only [Finset.mul_sum]
  rfl

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

lemma inner_mass' (k : ℕ) (s : MState) (hout : s.output = none)
    (hc : ¬ s.core.ptrs 0 ≤ s.core.ptrs 5) (N : ℕ) (E : MState → Prop) :
    mass (prog k) n evo (N + 18) (setpc s 73) E =
      ∑ c : C5, 1 / 32 * mass (prog k) n evo N (setpc (innerC s c) 73) E := by
  rw [inner_mass k s hout hc]
  simp only [Fintype.sum_prod_type, innerC]
  congr 1; funext c1; congr 1; funext c2; congr 1; funext c3; congr 1; funext c4; congr 1; funext c5
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  norm_num [ENNReal.div_eq_inv_mul]
  have : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ * 2⁻¹ * 2⁻¹ * 2⁻¹ = 2⁻¹ ^ 5 := by ring
  rw [this, ← ENNReal.inv_pow]; norm_num

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

lemma loop_mass (k : ℕ) (N : ℕ) (E : MState → Prop) : ∀ (r : ℕ) (s : MState),
    s.output = none → s.core.ptrs 0 = s.core.ptrs 5 + r →
    mass (prog k) n evo (N + 18 * r + 1) (setpc s 73) E =
      ∑ g : Fin r → C5, (1 / 32) ^ r * mass (prog k) n evo N (setpc (tick (iterInner r g s)) 91) E := by
  intro r
  induction r with
  | zero =>
    intro s hout h0
    rw [m_jt (f73 k) (by simp at h0; rw [h0]) hout]
    simp [iterInner]
  | succ r ih =>
    intro s hout h0
    have hc : ¬ s.core.ptrs 0 ≤ s.core.ptrs 5 := by push_cast at h0; omega
    rw [show N + 18 * (r + 1) + 1 = (N + 18 * r + 1) + 18 by ring, inner_mass' k s hout hc]
    have key : ∀ c : C5, mass (prog k) n evo (N + 18 * r + 1) (setpc (innerC s c) 73) E =
        ∑ g : Fin r → C5, (1 / 32) ^ r *
          mass (prog k) n evo N (setpc (tick (iterInner r g (innerC s c))) 91) E := by
      intro c
      apply ih
      · obtain ⟨m1, -⟩ := innerPost_misc s c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2
        exact m1.trans hout
      · simp only [innerC]
        rw [innerPost_ptrs _ _ _ _ _ _ 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), innerPost_p5, h0]; push_cast; ring
    simp_rw [key, Finset.mul_sum]
    have hcomp := (Fin.consEquiv (fun _ : Fin (r + 1) => C5)).sum_comp (fun G =>
      (1 / 32 : ℝ≥0∞) ^ (r + 1) * mass (prog k) n evo N (setpc (tick (iterInner (r + 1) G s)) 91) E)
    rw [← hcomp]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun g _ => ?_))
    simp only [Fin.consEquiv_apply, iterInner, Fin.cons_zero, Fin.cons_succ]
    rw [← mul_assoc, pow_succ']

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

lemma m_exp (k : ℕ) (t : MState) (hout : t.output = none) (hv : ExpValid n (setpc t 91) 4 0)
    (N : ℕ) (E : MState → Prop) :
    mass (prog k) n evo (N + 1) (setpc t 91) E = ∑ w : Qubits n,
      ENNReal.ofReal (bornAmp (evo (t.core.regs 0)) (expA n (setpc t 91) 4) (expV n (setpc t 91) 4)
        (expB n (setpc t 91) 4) w).re * mass (prog k) n evo N (setpc (expSt0 n t w) 92) E := by
  rw [mass_succ, branches_exp (s := setpc t 91) (f91 k) hout hv, List.map_map]
  rw [Finset.sum_map_toList]
  rfl

lemma cA_range (c : C5) : 0 ≤ cA c ∧ cA c ≤ 3 := by
  unfold cA; have := c.1.isLt; have := c.2.2.1.isLt; omega
lemma cB_range (c : C5) : 0 ≤ cB c ∧ cB c ≤ 3 := by
  unfold cB; have := c.2.2.2.1.isLt; have := c.2.2.2.2.isLt; omega
lemma cV_range (c : C5) : cV c = 0 ∨ cV c = 1 := by
  unfold cV; have := c.2.2.1.isLt; omega

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

lemma pre2_valid (s : MState) (g : Fin n → C5) (h0 : s.core.ptrs 0 = n) (hr0 : s.core.regs 0 = 0) :
    ExpValid n (setpc (pre2 n s g) 91) 4 0 := by
  obtain ⟨-, -, -, f4, -, f6, f7, -⟩ := pre2_facts s g h0
  refine ⟨by simp [setpc, f4, hr0], fun i => ?_⟩
  simp only [setpc, f6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  obtain ⟨e1, e2, e3⟩ := f7 i
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact cA_range _
  · rw [e2]; exact cV_range _
  · rw [e3]; exact cB_range _

lemma pre2_exp (s : MState) (g : Fin n → C5) (h0 : s.core.ptrs 0 = n) :
    expA n (setpc (pre2 n s g) 91) 4 = (fun j => letA (g j)) ∧
    expV n (setpc (pre2 n s g) 91) 4 = (fun j => bitV (g j)) ∧
    expB n (setpc (pre2 n s g) 91) 4 = (fun j => letB (g j)) := by
  obtain ⟨-, -, -, -, -, f6, f7, -⟩ := pre2_facts s g h0
  have h4 := f6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨funext fun j => ?_, funext fun j => ?_, funext fun j => ?_⟩
  · simp only [expA, setpc, h4, (f7 j).1, letA]
  · simp only [expV, setpc, h4, (f7 j).2.1, bitV]
  · simp only [expB, setpc, h4, (f7 j).2.2, letB]

/-- one sampling round, from pc 71 back to pc 71 -/
lemma outer_mass (k : ℕ) (s : MState) (hout : s.output = none) (h0 : s.core.ptrs 0 = n)
    (hr0 : s.core.regs 0 = 0) (hlt : ¬ s.core.ptrs 1 ≤ s.core.ptrs 3) (N : ℕ) (E : MState → Prop) :
    mass (prog k) n evo (N + (18 * n + 7)) (setpc s 71) E =
      ∑ g : Fin n → C5, ∑ w : Qubits n, wt evo g w *
        mass (prog k) n evo N (setpc (outerPost n s g w) 71) E := by
  rw [show N + (18 * n + 7) = ((N + 3 + 1) + 18 * n + 1) + 1 + 1 by ring]
  rw [m_jf (f71 k) hlt hout, m_plain (f72 k) trivial (by simp [hout])]
  have hr : (pre1 s).core.ptrs 0 = (pre1 s).core.ptrs 5 + n := by
    rw [pre1_ptrs s 0 (by norm_num), pre1_p5, h0]; ring
  rw [show ains (.core (.pset 5 0)) (tick s) = pre1 s from rfl,
    loop_mass k (N + 3 + 1) E n (pre1 s) (by simp [pre1, hout]) hr]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨f1, -, -, f4, -, f6, -, -⟩ := pre2_facts s g h0
  have ho2 : (pre2 n s g).output = none := f1.trans hout
  rw [show tick (iterInner n g (pre1 s)) = pre2 n s g from rfl,
    m_exp k (pre2 n s g) ho2 (pre2_valid s g h0 hr0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc]
  obtain ⟨eA, eV, eB⟩ := pre2_exp s g h0
  have hreg : (setpc (pre2 n s g) 91).core.regs 0 = 0 := by simp [setpc, f4, hr0]
  rw [m_plain (f92 k) trivial (by simp [expSt0, ho2]), m_plain (f93 k) trivial (by simp [expSt0, ho2]),
    m_jt (f94 k) le_rfl (by simp [expSt0, ho2])]
  have hr2 : (pre2 n s g).core.regs 0 = 0 := by rw [f4, hr0]
  simp only [wt, eA, eV, eB, hr2]
  rfl

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

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

variable {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)}

lemma outerLoop_mass (k N : ℕ) (E : MState → Prop) : ∀ (r : ℕ) (s : MState),
    s.output = none → s.core.ptrs 0 = n → s.core.regs 0 = 0 → s.core.ptrs 3 + r ≤ s.core.ptrs 1 →
    mass (prog k) n evo (N + r * (18 * n + 7)) (setpc s 71) E =
      ∑ G : Fin r → Rd n, (∏ i, wt evo (G i).1 (G i).2) *
        mass (prog k) n evo N (setpc (iterOuter r G s) 71) E := by
  intro r
  induction r with
  | zero => intro s _ _ _ _; simp [iterOuter]
  | succ r ih =>
    intro s hout h0 hr0 hle
    rw [show N + (r + 1) * (18 * n + 7) = (N + r * (18 * n + 7)) + (18 * n + 7) by ring,
      outer_mass k s hout h0 hr0 (by push_cast at hle; omega)]
    have key : ∀ g w, mass (prog k) n evo (N + r * (18 * n + 7)) (setpc (outerPost n s g w) 71) E =
        ∑ G : Fin r → Rd n, (∏ i, wt evo (G i).1 (G i).2) *
          mass (prog k) n evo N (setpc (iterOuter r G (outerPost n s g w)) 71) E := by
      intro g w
      obtain ⟨o1, -, -, o4, -, o6, o7, -⟩ := outerPost_facts s g w h0
      apply ih
      · rw [o1, hout]
      · rw [o6 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), h0]
      · rw [o4, hr0]
      · rw [o7, o6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)]; push_cast at hle; omega
    simp_rw [key, Finset.mul_sum]
    have hcomp := (Fin.consEquiv (fun _ : Fin (r + 1) => Rd n)).sum_comp (fun G =>
      (∏ i, wt evo (G i).1 (G i).2) * mass (prog k) n evo N (setpc (iterOuter (r + 1) G s) 71) E)
    rw [← hcomp]
    conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun w _ =>
      Finset.sum_congr rfl (fun G _ => ?_)))
    simp only [Fin.consEquiv_apply, iterOuter, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    ring

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
theorem solution : ∀ {n : ℕ} {evo : ℝ → Super (Qubits n) (Qubits n)} (k N : ℕ) (E : MState → Prop),
    ∀ (r : ℕ) (s : MState),
    s.output = none → s.core.ptrs 0 = n → s.core.regs 0 = 0 → s.core.ptrs 3 + r ≤ s.core.ptrs 1 →
    mass (prog k) n evo (N + r * (18 * n + 7)) (setpc s 71) E =
      ∑ G : Fin r → Rd n, (∏ i, wt evo (G i).1 (G i).2) *
        mass (prog k) n evo N (setpc (iterOuter r G s) 71) E :=
  @LindbladStructLearn.Mach.A1.outerLoop_mass
