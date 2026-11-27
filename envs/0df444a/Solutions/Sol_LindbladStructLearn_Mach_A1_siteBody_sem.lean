-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.siteBody_sem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:32.611006+00:00
-- url     : https://prove2.me/submissions/3bec4553-f5c7-4314-81ae-67bd53d7ca7a

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

lemma preSite_ptrs (t : MState) :
    let u := finL preSiteL t
    let b := t.core.ptrs 13
    let r := t.core.ptrs 19
    let k := t.core.ptrs 46
    let x := t.intMem (b + r + 1)
    let y := t.intMem (b + r + 1 + k)
    let z := t.intMem (b + r + 1 + k + k)
    let a := t.core.ptrs 4 + x
    let A := t.intMem a
    let B := t.intMem (a + t.core.ptrs 0 + t.core.ptrs 0)
    let m1 := t.intMem (4 + (z + z + (z + z) + A))
    let m2 := t.intMem (4 + (m1 + m1 + (m1 + m1) + y))
    u.core.ptrs 24 = A ∧ u.core.ptrs 25 = t.intMem (a + t.core.ptrs 0) ∧ u.core.ptrs 26 = B ∧
    u.core.ptrs 27 = t.intMem (a + t.core.ptrs 0 + t.core.ptrs 0 + t.core.ptrs 0) ∧
    u.core.ptrs 28 = m1 ∧ u.core.ptrs 29 = m2 ∧
    u.core.ptrs 31 = t.core.ptrs 31 + t.intMem (20 + (z + z + (z + z) + A)) +
      t.intMem (20 + (m1 + m1 + (m1 + m1) + y)) := by
  intro u b r k x y z a A B m1 m2
  simp only [u, preSiteL, finL, Stmt.fin, padd, pinc, iload, pset, ains]
  simp only [Function.update_apply]
  norm_num
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


lemma preSite_frame (t : MState) :
    let u := finL preSiteL t
    Same t u ∧ u.intMem = t.intMem ∧ u.work = t.work + 35 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 24 → q ≠ 25 → q ≠ 26 →
      q ≠ 27 → q ≠ 28 → q ≠ 29 → q ≠ 31 → u.core.ptrs q = t.core.ptrs q) := by
  intro u
  simp only [u, preSiteL, finL, Stmt.fin, padd, pinc, iload, pset, ains]
  refine ⟨⟨by trivial, by trivial, by trivial, by trivial⟩, by trivial, by trivial, ?_⟩
  intro q a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  simp only [Function.update_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, if_false]

lemma iteChk_fin (x y : ℕ) (u : MState) :
    let v := (Stmt.ite x y skip (pset 30 0)).fin u
    Same u v ∧ v.intMem = u.intMem ∧ u.work ≤ v.work ∧ v.work ≤ u.work + 3 ∧
    (∀ q, q ≠ 30 → v.core.ptrs q = u.core.ptrs q) ∧
    v.core.ptrs 30 = (if u.core.ptrs x ≤ u.core.ptrs y then u.core.ptrs 30 else 0) := by
  intro v
  simp only [v, Stmt.fin]
  split_ifs with h
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [skip, pcopy, ains, tick, Stmt.fin, Function.update_apply] <;> omega
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [pset, ains, tick, Stmt.fin, Function.update_apply] <;> omega

lemma iteAdd_fin (x y : ℕ) (hy : y ≠ 31) (u : MState) (h10 : u.core.ptrs 10 = 0) :
    let v := (Stmt.ite x 10 skip (seqs [padd 31 31 y, padd 31 31 y])).fin u
    Same u v ∧ v.intMem = u.intMem ∧ u.work ≤ v.work ∧ v.work ≤ u.work + 4 ∧
    (∀ q, q ≠ 31 → v.core.ptrs q = u.core.ptrs q) ∧
    v.core.ptrs 31 = u.core.ptrs 31 + (if u.core.ptrs x ≤ 0 then 0 else 2 * u.core.ptrs y) := by
  intro v
  simp only [v, Stmt.fin, tick_core, h10]
  split_ifs with h
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [skip, pcopy, ains, tick, Stmt.fin, Function.update_apply, h] <;> omega
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [seqs, padd, ains, tick, Stmt.fin, Function.update_apply, hy, h] <;> first | omega | ring

lemma postS_fin (u : MState) (h10 : u.core.ptrs 10 = 0) :
    let v := postS.fin u
    Same u v ∧ v.intMem = u.intMem ∧ u.work ≤ v.work ∧ v.work ≤ u.work + 20 ∧
    (∀ q, q ≠ 19 → q ≠ 30 → q ≠ 31 → v.core.ptrs q = u.core.ptrs q) ∧
    v.core.ptrs 19 = u.core.ptrs 19 + 1 ∧
    v.core.ptrs 30 = (if u.core.ptrs 26 = u.core.ptrs 29 then u.core.ptrs 30 else 0) ∧
    v.core.ptrs 31 = u.core.ptrs 31 + (if u.core.ptrs 24 ≤ 0 then 0 else 2 * u.core.ptrs 25) +
      (if u.core.ptrs 26 ≤ 0 then 0 else 2 * u.core.ptrs 27) := by
  intro v
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := iteChk_fin 26 29 u
  set u1 := (Stmt.ite 26 29 skip (pset 30 0)).fin u with hu1
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := iteChk_fin 29 26 u1
  set u2 := (Stmt.ite 29 26 skip (pset 30 0)).fin u1 with hu2
  have u1_10 : u1.core.ptrs 10 = 0 := by rw [a5 10 (by norm_num), h10]
  have u2_10 : u2.core.ptrs 10 = 0 := by rw [b5 10 (by norm_num), u1_10]
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := iteAdd_fin 24 25 (by norm_num) u2 u2_10
  set u3 := (Stmt.ite 24 10 skip (seqs [padd 31 31 25, padd 31 31 25])).fin u2 with hu3
  have u3_10 : u3.core.ptrs 10 = 0 := by rw [c5 10 (by norm_num), u2_10]
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := iteAdd_fin 26 27 (by norm_num) u3 u3_10
  set u4 := (Stmt.ite 26 10 skip (seqs [padd 31 31 27, padd 31 31 27])).fin u3 with hu4
  have hv : v = ains (.core (.pinc 19)) u4 := rfl
  have f : ∀ q, q ≠ 30 → q ≠ 31 → u4.core.ptrs q = u.core.ptrs q := by
    intro q h1 h2; rw [d5 q h2, c5 q h2, b5 q h1, a5 q h1]
  rw [hv]
  refine ⟨a1.trans (b1.trans (c1.trans d1)), by simp only [ains]; rw [d2, c2, b2, a2], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show u.work ≤ u4.work + 1; omega
  · show u4.work + 1 ≤ u.work + 20; omega
  · intro q h19 h30 h31; simp only [ains, Function.update_of_ne h19]; exact f q h30 h31
  · simp only [ains, Function.update_self]; rw [f 19 (by norm_num) (by norm_num)]
  · simp only [ains, Function.update_of_ne (show (30 : ℕ) ≠ 19 by norm_num)]
    rw [d5 30 (by norm_num), c5 30 (by norm_num), b6, a6, a5 29 (by norm_num), a5 26 (by norm_num)]
    by_cases h1 : u.core.ptrs 26 ≤ u.core.ptrs 29 <;> by_cases h2 : u.core.ptrs 29 ≤ u.core.ptrs 26 <;>
      simp [h1, h2] <;> omega
  · simp only [ains, Function.update_of_ne (show (31 : ℕ) ≠ 19 by norm_num)]
    have e2 : ∀ q, q ≠ 30 → u2.core.ptrs q = u.core.ptrs q := fun q h => (b5 q h).trans (a5 q h)
    have e3 : ∀ q, q ≠ 31 → q ≠ 30 → u3.core.ptrs q = u.core.ptrs q := fun q h h' => (c5 q h).trans (e2 q h')
    rw [d6, c6, e3 26 (by norm_num) (by norm_num), e3 27 (by norm_num) (by norm_num),
      e2 24 (by norm_num), e2 25 (by norm_num), e2 31 (by norm_num)]

lemma seqs_append_fin (l rest : List Stmt) (h : rest ≠ []) (s : MState) :
    (seqs (l ++ rest)).fin s = (seqs rest).fin (finL l s) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil =>
      obtain ⟨b, r, rfl⟩ := List.exists_cons_of_ne_nil h
      simp [seqs, Stmt.fin, finL]
    | cons a' l' =>
      simp only [List.cons_append] at ih ⊢
      simp only [seqs, Stmt.fin, finL]
      exact ih _

lemma siteBody_eq : siteBody = seqs (preSiteL ++ [.ite 26 29 skip (pset 30 0), .ite 29 26 skip (pset 30 0),
  .ite 24 10 skip (seqs [padd 31 31 25, padd 31 31 25]),
  .ite 26 10 skip (seqs [padd 31 31 27, padd 31 31 27]), pinc 19]) := rfl

lemma siteBody_fin_eq (t : MState) : siteBody.fin t = postS.fin (finL preSiteL t) := by
  rw [siteBody_eq, seqs_append_fin _ _ (by simp)]; rfl


lemma ifA (A : Fin 4) (V : Bool) : (if ((A : ℕ) : ℤ) ≤ 0 then (0 : ℤ) else 2 * (if V then 1 else 0)) =
    ((if A ≠ 0 ∧ V = true then 2 else 0 : ℕ) : ℤ) := by
  fin_cases A <;> cases V <;> simp

lemma siteBody_sem (t : MState) (k n : ℕ) (x : ℕ) (L1 L2 A B : Fin 4) (V W : Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (htab : Tab t.intMem)
    (hx : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1) = x)
    (hl1 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k) = (L1 : ℕ))
    (hl2 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k + k) = (L2 : ℕ))
    (hA : t.intMem (t.core.ptrs 4 + x) = (A : ℕ))
    (hV : t.intMem (t.core.ptrs 4 + x + n) = if V then 1 else 0)
    (hB : t.intMem (t.core.ptrs 4 + x + n + n) = (B : ℕ))
    (hW : t.intMem (t.core.ptrs 4 + x + n + n + n) = if W then 1 else 0) :
    let v := siteBody.fin t
    Same t v ∧ v.intMem = t.intMem ∧ t.work ≤ v.work ∧ v.work ≤ t.work + 55 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 24 → q ≠ 25 →
      q ≠ 26 → q ≠ 27 → q ≠ 28 → q ≠ 29 → q ≠ 30 → q ≠ 31 → v.core.ptrs q = t.core.ptrs q) ∧
    v.core.ptrs 19 = t.core.ptrs 19 + 1 ∧
    v.core.ptrs 30 = (if B = letterMul (letterMul L2 A) L1 then t.core.ptrs 30 else 0) ∧
    v.core.ptrs 31 = t.core.ptrs 31 + (siteExp L1 L2 A B V W : ℕ) := by
  intro v
  obtain ⟨p24, p25, p26, p27, p28, p29, p31⟩ := preSite_ptrs t
  obtain ⟨f1, f2, f3, f4⟩ := preSite_frame t
  have u10 : (finL preSiteL t).core.ptrs 10 = 0 := by
    rw [f4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), h10]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := postS_fin (finL preSiteL t) u10
  have hv : v = postS.fin (finL preSiteL t) := siteBody_fin_eq t
  simp only [h46, h0, hx, hA, hB, hV, hW, hl1, hl2] at p24 p25 p26 p27 p28 p29 p31
  have m1 : t.intMem (4 + ((L2 : ℕ) + (L2 : ℕ) + ((L2 : ℕ) + (L2 : ℕ)) + (A : ℕ) : ℤ)) =
      ((letterMul L2 A : ℕ) : ℤ) := by
    rw [← (htab L2 A).1]; congr 1; ring
  have ph1 : t.intMem (20 + ((L2 : ℕ) + (L2 : ℕ) + ((L2 : ℕ) + (L2 : ℕ)) + (A : ℕ) : ℤ)) =
      (phexp L2 A : ℤ) := by
    rw [← (htab L2 A).2]; congr 1; ring
  rw [m1] at p28 p29 p31
  have m2 : t.intMem (4 + (((letterMul L2 A : ℕ) : ℤ) + ((letterMul L2 A : ℕ) : ℤ) +
      (((letterMul L2 A : ℕ) : ℤ) + ((letterMul L2 A : ℕ) : ℤ)) + (L1 : ℕ))) =
      ((letterMul (letterMul L2 A) L1 : ℕ) : ℤ) := by
    rw [← (htab (letterMul L2 A) L1).1]; congr 1; ring
  have ph2 : t.intMem (20 + (((letterMul L2 A : ℕ) : ℤ) + ((letterMul L2 A : ℕ) : ℤ) +
      (((letterMul L2 A : ℕ) : ℤ) + ((letterMul L2 A : ℕ) : ℤ)) + (L1 : ℕ))) =
      (phexp (letterMul L2 A) L1 : ℤ) := by
    rw [← (htab (letterMul L2 A) L1).2]; congr 1; ring
  rw [m2] at p29
  rw [ph1, ph2] at p31
  rw [hv]
  refine ⟨f1.trans g1, by rw [g2, f2], by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro q a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
    rw [g5 q a5 a15 a16, f4 q a1 a2 a3 a4 a6 a7 a8 a9 a10 a11 a12 a13 a14 a16]
  · rw [g6, f4 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  · rw [g7, p26, p29, f4 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    congr 1
    apply propext
    rw [Nat.cast_inj, Fin.val_inj]
  · rw [g8, p24, p25, p26, p27, p31]
    unfold siteExp
    rw [ifA, ifA]
    push_cast; ring

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
theorem solution : ∀ (t : MState) (k n : ℕ) (x : ℕ) (L1 L2 A B : Fin 4) (V W : Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (htab : Tab t.intMem)
    (hx : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1) = x)
    (hl1 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k) = (L1 : ℕ))
    (hl2 : t.intMem (t.core.ptrs 13 + t.core.ptrs 19 + 1 + k + k) = (L2 : ℕ))
    (hA : t.intMem (t.core.ptrs 4 + x) = (A : ℕ))
    (hV : t.intMem (t.core.ptrs 4 + x + n) = if V then 1 else 0)
    (hB : t.intMem (t.core.ptrs 4 + x + n + n) = (B : ℕ))
    (hW : t.intMem (t.core.ptrs 4 + x + n + n + n) = if W then 1 else 0),
    let v := siteBody.fin t
    Same t v ∧ v.intMem = t.intMem ∧ t.work ≤ v.work ∧ v.work ≤ t.work + 55 ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 8 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 24 → q ≠ 25 →
      q ≠ 26 → q ≠ 27 → q ≠ 28 → q ≠ 29 → q ≠ 30 → q ≠ 31 → v.core.ptrs q = t.core.ptrs q) ∧
    v.core.ptrs 19 = t.core.ptrs 19 + 1 ∧
    v.core.ptrs 30 = (if B = letterMul (letterMul L2 A) L1 then t.core.ptrs 30 else 0) ∧
    v.core.ptrs 31 = t.core.ptrs 31 + (siteExp L1 L2 A B V W : ℕ) :=
  @LindbladStructLearn.Mach.A1.siteBody_sem
