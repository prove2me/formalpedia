-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.valid_loop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:31.122805+00:00
-- url     : https://prove2.me/submissions/43ea88ac-3925-4f95-8268-d172ecef0eb8

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_validBody_fin

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

lemma DetRun.refl (s : MState) : DetRun P 0 s s := ⟨fun i hi => absurd hi (by omega), rfl⟩

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

/-- loop rule with an indexed invariant -/
lemma loop_rule {x y : ℕ} {b : Stmt} (Inv : ℕ → MState → Prop) (T cost : ℕ)
    (hstep : ∀ j < T, ∀ s, Inv j s → ¬ s.core.ptrs x ≤ s.core.ptrs y ∧
      ∃ s1 m, Exec b (tick s) s1 m ∧ m ≤ cost ∧ Inv (j + 1) (tick s1))
    (hend : ∀ s, Inv T s → s.core.ptrs x ≤ s.core.ptrs y) :
    ∀ s, Inv 0 s → ∃ sT m, Inv T sT ∧ Exec (.loop x y b) s (tick sT) m ∧ m ≤ T * (cost + 2) + 1 := by
  suffices H : ∀ r j, j + r = T → ∀ s, Inv j s →
      ∃ sT m, Inv T sT ∧ Exec (.loop x y b) s (tick sT) m ∧ m ≤ r * (cost + 2) + 1 by
    intro s hs; exact H T 0 (by ring) s hs
  intro r
  induction r with
  | zero =>
    intro j hj s hs
    simp only [add_zero] at hj; subst hj
    exact ⟨s, 1, hs, Exec.loopDone (hend s hs), by simp⟩
  | succ r ih =>
    intro j hj s hs
    obtain ⟨hc, s1, m, hb, hm, hinv⟩ := hstep j (by omega) s hs
    obtain ⟨sT, m', hT, he, hm'⟩ := ih (j + 1) (by omega) (tick s1) hinv
    refine ⟨sT, m + m' + 2, hT, Exec.loopStep hc hb he, ?_⟩
    nlinarith

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

lemma Same.refl (s : MState) : Same s s := ⟨rfl, rfl, rfl, rfl⟩
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

lemma validBody_noLoop (k : ℕ) : (validBody k).NoLoop := by
  simp [validBody, beyond, within, inval, skip, seqs, Stmt.NoLoop, pset, padd, iload, pinc, pcopy, Plain]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma valid_loop (k : ℕ) (s : MState) (h46 : s.core.ptrs 46 = k) (h10 : s.core.ptrs 10 = 0)
    (h11 : s.core.ptrs 11 = 1) (h19 : s.core.ptrs 19 = 0) (h41 : s.core.ptrs 41 = 1) :
    ∃ s' m, Exec (.loop 46 19 (validBody k)) s s' m ∧ m ≤ k * 32 + 1 ∧ Same s s' ∧
      s'.intMem = s.intMem ∧
      (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
        s'.core.ptrs q = s.core.ptrs q) ∧
      s'.core.ptrs 41 = if ∃ r : ℕ, r < k ∧ badM (s.core.ptrs 20) r (s.intMem (cDIG k + r + 1))
        (s.intMem (cDIG k + r + 1 + k)) (s.intMem (cDIG k + r + 1 + k + k))
        (s.intMem (cDIG k + (r + 1) + 1)) then 0 else 1 := by
  let bad : ℕ → Prop := fun r => badM (s.core.ptrs 20) r (s.intMem (cDIG k + r + 1))
        (s.intMem (cDIG k + r + 1 + k)) (s.intMem (cDIG k + r + 1 + k + k))
        (s.intMem (cDIG k + (r + 1) + 1))
  let Inv : ℕ → MState → Prop := fun j t => t.core.ptrs 19 = j ∧ Same s t ∧ t.intMem = s.intMem ∧
    (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
        t.core.ptrs q = s.core.ptrs q) ∧
    t.core.ptrs 41 = if ∃ r : ℕ, r < j ∧ bad r then 0 else 1
  have hstep : ∀ j < k, ∀ t, Inv j t → ¬ t.core.ptrs 46 ≤ t.core.ptrs 19 ∧
      ∃ s1 m, Exec (validBody k) (tick t) s1 m ∧ m ≤ 30 ∧ Inv (j + 1) (tick s1) := by
    intro j hj t ⟨i19, isame, imem, iptr, i41⟩
    have f := fun q (a1 : q ≠ 6) (a2 : q ≠ 7) (a3 : q ≠ 9) (a4 : q ≠ 19) (a5 : q ≠ 21) (a6 : q ≠ 22)
      (a7 : q ≠ 23) (a8 : q ≠ 41) => iptr q a1 a2 a3 a4 a5 a6 a7 a8
    have t46 : t.core.ptrs 46 = k := by rw [f 46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), h46]
    have t10 : t.core.ptrs 10 = 0 := by rw [f 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10]
    have t11 : t.core.ptrs 11 = 1 := by rw [f 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), h11]
    have t20 : t.core.ptrs 20 = s.core.ptrs 20 := f 20 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := validBody_fin k (tick t) t46 t10 t11
    have hex := (validBody k).exec_fin (validBody_noLoop k) (tick t)
    have hw := hex.work
    refine ⟨by rw [t46, i19]; push_cast; omega, _, _, hex, by simp at hw v4; omega, ?_⟩
    refine ⟨?_, isame.trans (v1.tick), ?_, ?_, ?_⟩
    · show ((validBody k).fin (tick t)).core.ptrs 19 = _
      rw [v6]; simp [i19]
    · show ((validBody k).fin (tick t)).intMem = _
      rw [v2]; exact imem
    · intro q a1 a2 a3 a4 a5 a6 a7 a8
      show ((validBody k).fin (tick t)).core.ptrs q = _
      rw [v5 q a1 a2 a3 a4 a5 a6 a7 a8]; exact iptr q a1 a2 a3 a4 a5 a6 a7 a8
    · show ((validBody k).fin (tick t)).core.ptrs 41 = _
      rw [v7]
      simp only [tick_core, tick_intMem, i19, t20, imem, i41]
      have hb : bad j ↔ badM (s.core.ptrs 20) (j : ℤ) (s.intMem (cDIG k + j + 1))
        (s.intMem (cDIG k + j + 1 + k)) (s.intMem (cDIG k + j + 1 + k + k))
        (s.intMem (cDIG k + (j + 1) + 1)) := Iff.rfl
      by_cases hj' : bad j
      · rw [if_pos (hb.mp hj'), if_pos ⟨j, by omega, hj'⟩]
      · rw [if_neg (fun h => hj' (hb.mpr h))]
        have : (∃ r : ℕ, r < j + 1 ∧ bad r) ↔ ∃ r : ℕ, r < j ∧ bad r := by
          constructor
          · rintro ⟨r, hr, hr'⟩
            refine ⟨r, ?_, hr'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
            · exact h
            · subst h; exact absurd hr' hj'
          · rintro ⟨r, hr, hr'⟩; exact ⟨r, by omega, hr'⟩
        simp only [this]
  have hend : ∀ t, Inv k t → t.core.ptrs 46 ≤ t.core.ptrs 19 := by
    rintro t ⟨i19, -, -, iptr, -⟩
    rw [iptr 46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h46, i19]
  obtain ⟨sT, m, ⟨i19, isame, imem, iptr, i41⟩, hex, hm⟩ := loop_rule Inv k 30 hstep hend s
    ⟨h19, Same.refl s, rfl, fun q _ _ _ _ _ _ _ _ => rfl, by simp [h41]⟩
  exact ⟨tick sT, m, hex, by linarith, isame.tick, imem, iptr, i41⟩

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

lemma RegFix.refl (s : MState) (S : Finset ℕ) : RegFix s s S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

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
theorem solution : ∀ (k : ℕ) (s : MState) (h46 : s.core.ptrs 46 = k) (h10 : s.core.ptrs 10 = 0)
    (h11 : s.core.ptrs 11 = 1) (h19 : s.core.ptrs 19 = 0) (h41 : s.core.ptrs 41 = 1),
    ∃ s' m, Exec (.loop 46 19 (validBody k)) s s' m ∧ m ≤ k * 32 + 1 ∧ Same s s' ∧
      s'.intMem = s.intMem ∧
      (∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 19 → q ≠ 21 → q ≠ 22 → q ≠ 23 → q ≠ 41 →
        s'.core.ptrs q = s.core.ptrs q) ∧
      s'.core.ptrs 41 = if ∃ r : ℕ, r < k ∧ badM (s.core.ptrs 20) r (s.intMem (cDIG k + r + 1))
        (s.intMem (cDIG k + r + 1 + k)) (s.intMem (cDIG k + r + 1 + k + k))
        (s.intMem (cDIG k + (r + 1) + 1)) then 0 else 1 :=
  @LindbladStructLearn.Mach.A1.valid_loop
