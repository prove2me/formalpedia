-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.odo_loop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:31.942344+00:00
-- url     : https://prove2.me/submissions/d88920ce-a2ae-436c-ada2-e6cbb35458be

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
end A1
end LindbladStructLearn.Mach

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

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

lemma odoBody_noLoop (k : ℕ) : (odoBody k).NoLoop := by
  simp [odoBody, seqs, Stmt.NoLoop, pset, padd, iload, pinc, pdec, pcopy, istore, Plain]

set_option maxHeartbeats 1000000 in
lemma odoBody_fin (k n : ℕ) (t : MState) (h46 : t.core.ptrs 46 = k) (h10 : t.core.ptrs 10 = 0)
    (h0 : t.core.ptrs 0 = n) :
    let u := (odoBody k).fin t
    let q := t.core.ptrs 15
    let d := t.intMem (cDIG k + q)
    Same t u ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 20 ∧
    (∀ p, p ≠ 6 → p ≠ 9 → p ≠ 15 → p ≠ 16 → p ≠ 17 → p ≠ 40 → p ≠ 42 → u.core.ptrs p = t.core.ptrs p) ∧
    (d + 1 < capZ k n q → u.intMem = Function.update t.intMem (cDIG k + q) (d + 1) ∧
      u.core.ptrs 42 = 0 ∧ u.core.ptrs 15 = q ∧ u.core.ptrs 40 = t.core.ptrs 40) ∧
    (capZ k n q ≤ d + 1 → u.intMem = Function.update t.intMem (cDIG k + q) 0 ∧
      (q ≤ 0 → u.core.ptrs 40 = 1 ∧ u.core.ptrs 42 = 0 ∧ u.core.ptrs 15 = q) ∧
      (¬ q ≤ 0 → u.core.ptrs 15 = q - 1 ∧ u.core.ptrs 42 = t.core.ptrs 42 ∧
        u.core.ptrs 40 = t.core.ptrs 40)) := by
  intro u q d
  simp only [u, q, d, odoBody, seqs, Stmt.fin, capZ]
  split_ifs <;> simp_all [Same, ains, tick, skip, pset, pcopy, padd, iload, pinc, pdec, istore,
    Stmt.fin, Function.update_apply] <;> omega

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma capZ_eq (k n q : ℕ) : capZ k n q = (rad k n q : ℤ) := by
  unfold capZ rad
  split_ifs <;> push_cast <;> omega

lemma odo_loop (k n : ℕ) : ∀ (q : ℕ) (t : MState) (D : ℕ → ℕ), q ≤ 3 * k →
    t.core.ptrs 15 = q → t.core.ptrs 42 = 1 → t.core.ptrs 40 = 0 → t.core.ptrs 46 = k →
    t.core.ptrs 10 = 0 → t.core.ptrs 0 = n → (∀ i ≤ 3 * k, t.intMem (cDIG k + i) = D i) →
    ∃ t' m, Exec (.loop 42 10 (odoBody k)) t t' m ∧ m ≤ (q + 1) * 23 + 1 ∧ Same t t' ∧
      (∀ p, p ≠ 6 → p ≠ 9 → p ≠ 15 → p ≠ 16 → p ≠ 17 → p ≠ 40 → p ≠ 42 →
        t'.core.ptrs p = t.core.ptrs p) ∧
      (∀ i ≤ 3 * k, t'.intMem (cDIG k + i) = (incAt k n q D).1 i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → t'.intMem z = t.intMem z) ∧
      t'.core.ptrs 40 = if (incAt k n q D).2 then 1 else 0 := by
  intro q
  induction q with
  | zero =>
    intro t D hq h15 h42 h40 h46 h10 h0 hD
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := odoBody_fin k n (tick t) h46 h10 h0
    have hex := (odoBody k).exec_fin (odoBody_noLoop k) (tick t)
    have hw := hex.work
    simp only [tick_core, tick_intMem, tick_work, h15, Nat.cast_zero, add_zero] at o1 o2 o3 o4 o5 o6 hw
    have hd := hD 0 (by omega)
    simp only [Nat.cast_zero, add_zero] at hd
    rw [hd, show (D 0 : ℤ) + 1 = ((D 0 + 1 : ℕ) : ℤ) by push_cast; ring,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) by simp, capZ_eq] at o5 o6
    by_cases hc : D 0 + 1 < rad k n 0
    · obtain ⟨m1, m2, m3, m4⟩ := o5 (by exact_mod_cast hc)
      refine ⟨_, _, Exec.loopStep (by rw [h42, h10]; norm_num) hex
        (Exec.loopDone (by simp [m2, o4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h10])), by omega, ?_, ?_, ?_, ?_, ?_⟩
      · exact (o1 : Same t _).tick.tick
      · intro p a1 a2 a3 a4 a5 a6 a7; simp only [tick_core]; exact o4 p a1 a2 a3 a4 a5 a6 a7
      · intro i hi
        simp only [tick_intMem, m1, incAt, if_pos hc]
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; simp
        · rw [Function.update_of_ne (by push_cast; omega), Function.update_of_ne (by omega), hD i hi]
      · intro z hz; simp only [tick_intMem, m1]; rw [Function.update_of_ne (by omega)]
      · simp only [tick_core, m4, h40, incAt, if_pos hc]; rfl
    · obtain ⟨m1, m2, -⟩ := o6 (by push Not at hc; exact_mod_cast hc)
      obtain ⟨n1, n2, n3⟩ := m2 le_rfl
      refine ⟨_, _, Exec.loopStep (by rw [h42, h10]; norm_num) hex
        (Exec.loopDone (by simp [n2, o4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h10])), by omega, ?_, ?_, ?_, ?_, ?_⟩
      · exact (o1 : Same t _).tick.tick
      · intro p a1 a2 a3 a4 a5 a6 a7; simp only [tick_core]; exact o4 p a1 a2 a3 a4 a5 a6 a7
      · intro i hi
        simp only [tick_intMem, m1, incAt, if_neg hc]
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; simp
        · rw [Function.update_of_ne (by push_cast; omega), Function.update_of_ne (by omega), hD i hi]
      · intro z hz; simp only [tick_intMem, m1]; rw [Function.update_of_ne (by omega)]
      · simp only [tick_core, n1, incAt, if_neg hc]; rfl
  | succ q ih =>
    intro t D hq h15 h42 h40 h46 h10 h0 hD
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := odoBody_fin k n (tick t) h46 h10 h0
    have hex := (odoBody k).exec_fin (odoBody_noLoop k) (tick t)
    have hw := hex.work
    simp only [tick_core, tick_intMem, tick_work, h15] at o1 o2 o3 o4 o5 o6 hw
    have hd := hD (q + 1) hq
    rw [hd, show (D (q + 1) : ℤ) + 1 = ((D (q + 1) + 1 : ℕ) : ℤ) by push_cast; ring, capZ_eq] at o5 o6
    by_cases hc : D (q + 1) + 1 < rad k n (q + 1)
    · obtain ⟨m1, m2, m3, m4⟩ := o5 (by exact_mod_cast hc)
      refine ⟨_, _, Exec.loopStep (by rw [h42, h10]; norm_num) hex
        (Exec.loopDone (by simp [m2, o4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h10])), by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · exact (o1 : Same t _).tick.tick
      · intro p a1 a2 a3 a4 a5 a6 a7; simp only [tick_core]; exact o4 p a1 a2 a3 a4 a5 a6 a7
      · intro i hi
        simp only [tick_intMem, m1, incAt, if_pos hc]
        by_cases h : i = q + 1
        · subst h; simp
        · rw [Function.update_of_ne (by push_cast; omega), Function.update_of_ne h, hD i hi]
      · intro z hz; simp only [tick_intMem, m1]; rw [Function.update_of_ne (by push_cast; omega)]
      · simp only [tick_core, m4, h40, incAt, if_pos hc]; rfl
    · obtain ⟨m1, -, m3⟩ := o6 (by push Not at hc; exact_mod_cast hc)
      obtain ⟨n1, n2, n3⟩ := m3 (by push_cast; omega)
      have hq' : q ≤ 3 * k := by omega
      obtain ⟨t', m', e1, e2, e3, e4, e5, e6, e7⟩ := ih (tick ((odoBody k).fin (tick t)))
        (Function.update D (q + 1) 0) hq'
        (by simp only [tick_core, n1]; push_cast; ring)
        (by simp only [tick_core, n2, h42])
        (by simp only [tick_core, n3, h40])
        (by simp only [tick_core]; rw [o4 46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h46])
        (by simp only [tick_core]; rw [o4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h10])
        (by simp only [tick_core]; rw [o4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num), h0])
        (by intro i hi
            simp only [tick_intMem, m1]
            by_cases h : i = q + 1
            · subst h; simp
            · rw [Function.update_of_ne (by push_cast; omega), Function.update_of_ne h, hD i hi])
      refine ⟨t', _, Exec.loopStep (by rw [h42, h10]; norm_num) hex e1, by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · exact ((o1 : Same t _).tick).trans e3
      · intro p a1 a2 a3 a4 a5 a6 a7
        rw [e4 p a1 a2 a3 a4 a5 a6 a7]; simp only [tick_core]; exact o4 p a1 a2 a3 a4 a5 a6 a7
      · intro i hi; rw [e5 i hi]; simp only [incAt, if_neg hc]
      · intro z hz; rw [e6 z hz]; simp only [tick_intMem, m1]
        rw [Function.update_of_ne (by push_cast; omega)]
      · rw [e7]; simp only [incAt, if_neg hc]

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
theorem solution : ∀ (k n : ℕ),
    ∀ (q : ℕ) (t : MState) (D : ℕ → ℕ), q ≤ 3 * k →
    t.core.ptrs 15 = q → t.core.ptrs 42 = 1 → t.core.ptrs 40 = 0 → t.core.ptrs 46 = k →
    t.core.ptrs 10 = 0 → t.core.ptrs 0 = n → (∀ i ≤ 3 * k, t.intMem (cDIG k + i) = D i) →
    ∃ t' m, Exec (.loop 42 10 (odoBody k)) t t' m ∧ m ≤ (q + 1) * 23 + 1 ∧ Same t t' ∧
      (∀ p, p ≠ 6 → p ≠ 9 → p ≠ 15 → p ≠ 16 → p ≠ 17 → p ≠ 40 → p ≠ 42 →
        t'.core.ptrs p = t.core.ptrs p) ∧
      (∀ i ≤ 3 * k, t'.intMem (cDIG k + i) = (incAt k n q D).1 i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → t'.intMem z = t.intMem z) ∧
      t'.core.ptrs 40 = if (incAt k n q D).2 then 1 else 0 :=
  @LindbladStructLearn.Mach.A1.odo_loop
