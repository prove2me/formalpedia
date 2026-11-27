-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.iterOuter_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:35.415114+00:00
-- url     : https://prove2.me/submissions/324c0e7a-4997-42b9-9dc5-7e087681147a

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

lemma iterOuter_frame (r : ℕ) (G : Fin r → Rd n) (s : MState) (h0 : s.core.ptrs 0 = n) :
    let t := iterOuter r G s
    t.output = s.output ∧ t.durations = s.durations ++ List.replicate r (s.core.regs 0) ∧
    t.work = s.work + r * (19 * n + 7) ∧ t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 3 = s.core.ptrs 3 + r ∧ t.core.ptrs 4 = s.core.ptrs 4 + r * s.core.ptrs 2 := by
  induction r generalizing s with
  | zero => simp [iterOuter]
  | succ r ih =>
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, -, -⟩ := outerPost_facts s (G 0).1 (G 0).2 h0
    have h0' : (outerPost n s (G 0).1 (G 0).2).core.ptrs 0 = n := by
      rw [o6 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), h0]
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih (fun j => G j.succ) _ h0'
    have h2 := o6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    simp only [iterOuter]
    refine ⟨i1.trans o1, ?_, ?_, i4.trans o4, i5.trans o5, fun q a b c d e f g' =>
      (i6 q a b c d e f g').trans (o6 q a b c d e f g'), ?_, ?_⟩
    · rw [i2, o2, o4, List.append_assoc]; simp [List.replicate_succ]
    · rw [i3, o3]; push_cast; ring
    · rw [i7, o7]; push_cast; ring
    · rw [i8, o8, h2]; push_cast; ring

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
theorem solution : ∀ {n : ℕ} (r : ℕ) (G : Fin r → Rd n) (s : MState) (h0 : s.core.ptrs 0 = n),
    let t := iterOuter r G s
    t.output = s.output ∧ t.durations = s.durations ++ List.replicate r (s.core.regs 0) ∧
    t.work = s.work + r * (19 * n + 7) ∧ t.core.regs = s.core.regs ∧ t.core.mem = s.core.mem ∧
    (∀ q, q ≠ 3 → q ≠ 4 → q ≠ 5 → q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 3 = s.core.ptrs 3 + r ∧ t.core.ptrs 4 = s.core.ptrs 4 + r * s.core.ptrs 2 :=
  @LindbladStructLearn.Mach.A1.iterOuter_frame
