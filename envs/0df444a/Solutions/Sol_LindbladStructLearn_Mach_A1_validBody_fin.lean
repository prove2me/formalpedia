-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.validBody_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:30.403499+00:00
-- url     : https://prove2.me/submissions/e95f4c95-00d8-4506-a925-6b4828e280d5

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

lemma preV_facts (k : ℕ) (t : MState) (h46 : t.core.ptrs 46 = k) :
    let u := preV k t
    let r := t.core.ptrs 19
    Same t u ∧ u.intMem = t.intMem ∧ u.work = t.work + 8 ∧
    (∀ q, q ≠ 6 → q ≠ 21 → q ≠ 22 → q ≠ 23 → u.core.ptrs q = t.core.ptrs q) ∧
    u.core.ptrs 21 = t.intMem (cDIG k + r + 1) ∧ u.core.ptrs 22 = t.intMem (cDIG k + r + 1 + k) ∧
    u.core.ptrs 23 = t.intMem (cDIG k + r + 1 + k + k) := by
  intro u r
  simp only [u, r, preV, ains]
  refine ⟨⟨by trivial, by trivial, by trivial, by trivial⟩, by trivial, by trivial, fun q a b c d => ?_, ?_, ?_, ?_⟩
  · simp only [Function.update_apply, a, b, c, d, if_false]
  · simp [Function.update_apply]
  · simp [Function.update_apply, h46]
  · simp [Function.update_apply, h46]

lemma beyond_fin (t : MState) (h10 : t.core.ptrs 10 = 0) :
    let u := beyond.fin t
    Same t u ∧ u.intMem = t.intMem ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 8 ∧
    u.core.ptrs = if t.core.ptrs 21 ≤ 0 ∧ t.core.ptrs 22 ≤ 0 ∧ t.core.ptrs 23 ≤ 0 then t.core.ptrs
      else Function.update t.core.ptrs 41 0 := by
  intro u
  simp only [u, beyond, Stmt.fin, h10]
  split_ifs <;> simp_all [Same, ains, tick, skip, inval, pset, pcopy, Stmt.fin] <;> omega


lemma within_fin (k : ℕ) (t : MState) (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) :
    let u := (within k).fin t
    Same t u ∧ u.intMem = t.intMem ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 16 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 41 → u.core.ptrs q = t.core.ptrs q) ∧
    u.core.ptrs 41 = if (t.core.ptrs 22 ≤ 0 ∧ t.core.ptrs 23 ≤ 0) ∨
      (¬ t.core.ptrs 20 ≤ t.core.ptrs 19 + 1 ∧
        t.intMem (cDIG k + (t.core.ptrs 19 + 1) + 1) ≤ t.core.ptrs 21) then 0 else t.core.ptrs 41 := by
  intro u
  simp only [u, within, seqs, Stmt.fin, h10]
  split_ifs <;> simp_all [Same, ains, tick, skip, inval, pset, pcopy, padd, iload, pinc, Stmt.fin,
    Function.update_apply] <;> omega


lemma validBody_fin (k : ℕ) (t : MState) (h46 : t.core.ptrs 46 = k) (h10 : t.core.ptrs 10 = 0)
    (h11 : t.core.ptrs 11 = 1) :
    let u := (validBody k).fin t
    let r := t.core.ptrs 19
    Same t u ∧ u.intMem = t.intMem ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 30 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
      u.core.ptrs q = t.core.ptrs q) ∧ u.core.ptrs 19 = r + 1 ∧
    u.core.ptrs 41 = (if badM (t.core.ptrs 20) r (t.intMem (cDIG k + r + 1))
      (t.intMem (cDIG k + r + 1 + k)) (t.intMem (cDIG k + r + 1 + k + k))
      (t.intMem (cDIG k + (r + 1) + 1)) then 0 else t.core.ptrs 41) := by
  intro u r
  obtain ⟨p1, p2, p3, e, e21, e22, e23⟩ := preV_facts k t h46
  have hu : u = ains (.core (.pinc 19)) ((Stmt.ite 20 19 beyond (within k)).fin (preV k t)) := rfl
  have e19 := e 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 := e 20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 := e 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 := e 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 := e 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  by_cases hc : t.core.ptrs 20 ≤ t.core.ptrs 19
  · have hc' : (preV k t).core.ptrs 20 ≤ (preV k t).core.ptrs 19 := by rw [e19, e20]; exact hc
    obtain ⟨b1, b2, b3, b4, b5⟩ := beyond_fin (tick (preV k t)) (by simp [tick, e10, h10])
    have hu' : u = ains (.core (.pinc 19)) (beyond.fin (tick (preV k t))) := by
      rw [hu]; simp only [Stmt.fin, if_pos hc']
    rw [hu']
    have hw : (tick (preV k t)).work = t.work + 9 := by simp [tick, p3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (p1.trans b1 : Same t _)
    · simp only [ains]; rw [b2]; exact p2
    · simp only [ains]; omega
    · simp only [ains]; omega
    · intro q a1 a2 a3 a4 a5 a6 a7 a8
      simp only [ains, Function.update_of_ne a4, b5]
      split_ifs
      · exact e q a1 a5 a6 a7
      · rw [Function.update_of_ne a8]; exact e q a1 a5 a6 a7
    · simp only [ains, Function.update_self, b5]
      split_ifs <;> simp [e19, r, tick_core]
    · simp only [ains, Function.update_of_ne (show (41 : ℕ) ≠ 19 by norm_num), b5, e21, e22, e23]
      simp only [badM, r] at *
      split_ifs <;> simp_all
  · have hc' : ¬ (preV k t).core.ptrs 20 ≤ (preV k t).core.ptrs 19 := by rw [e19, e20]; exact hc
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := within_fin k (tick (preV k t)) (by simp [tick, e10, h10])
      (by simp [tick, e11, h11])
    have hu' : u = ains (.core (.pinc 19)) (tick ((within k).fin (tick (preV k t)))) := by
      rw [hu]; simp only [Stmt.fin, if_neg hc']
    rw [hu']
    have hw : (tick (preV k t)).work = t.work + 9 := by simp [tick, p3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (p1.trans w1 : Same t _)
    · simp only [ains, tick_core, tick_intMem, tick_work]; rw [show ((within k).fin (tick (preV k t))).intMem = _ from w2]; exact p2
    · simp only [ains, tick_core, tick_intMem, tick_work]; omega
    · simp only [ains, tick_core, tick_intMem, tick_work]; omega
    · intro q a1 a2 a3 a4 a5 a6 a7 a8
      simp only [ains, tick_core, tick_intMem, tick_work, Function.update_of_ne a4]
      rw [w5 q a1 a2 a3 a8]; exact e q a1 a5 a6 a7
    · simp only [ains, tick_core, tick_intMem, tick_work, Function.update_self]
      rw [w5 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp [e19, r]
    · simp only [ains, tick_core, tick_intMem, tick_work, Function.update_of_ne (show (41 : ℕ) ≠ 19 by norm_num), w6, e19, e20,
        e21, e22, e23, e41, p2]
      simp only [badM, r] at *
      split_ifs <;> first | rfl | omega

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
theorem solution : ∀ (k : ℕ) (t : MState) (h46 : t.core.ptrs 46 = k) (h10 : t.core.ptrs 10 = 0)
    (h11 : t.core.ptrs 11 = 1),
    let u := (validBody k).fin t
    let r := t.core.ptrs 19
    Same t u ∧ u.intMem = t.intMem ∧ t.work ≤ u.work ∧ u.work ≤ t.work + 30 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
      u.core.ptrs q = t.core.ptrs q) ∧ u.core.ptrs 19 = r + 1 ∧
    u.core.ptrs 41 = (if badM (t.core.ptrs 20) r (t.intMem (cDIG k + r + 1))
      (t.intMem (cDIG k + r + 1 + k)) (t.intMem (cDIG k + r + 1 + k + k))
      (t.intMem (cDIG k + (r + 1) + 1)) then 0 else t.core.ptrs 41) :=
  @LindbladStructLearn.Mach.A1.validBody_fin
