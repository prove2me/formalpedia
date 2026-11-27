-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.S2_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:27.932265+00:00
-- url     : https://prove2.me/submissions/4b22a4b8-bc40-46fb-be71-080b2d8d2223

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_valid_loop
import Theorems.Thm_LindbladStructLearn_Mach_A1_odo_loop

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

lemma copyBody_noLoop (k : ℕ) : (copyBody k).NoLoop := by
  simp [copyBody, seqs, Stmt.NoLoop, pset, padd, iload, istore, pinc, Plain]

lemma copyBody_fin (k : ℕ) (t : MState) :
    let u := (copyBody k).fin t
    u.output = t.output ∧ u.durations = t.durations ∧ u.core.regs = t.core.regs ∧
    u.core.mem = t.core.mem ∧ u.work = t.work + 6 ∧
    u.core.ptrs = Function.update (Function.update (Function.update t.core.ptrs 6
      (t.core.ptrs 13 + t.core.ptrs 19)) 16 (t.intMem (cDIG k + t.core.ptrs 19))) 19 (t.core.ptrs 19 + 1) ∧
    u.intMem = Function.update t.intMem (t.core.ptrs 13 + t.core.ptrs 19) (t.intMem (cDIG k + t.core.ptrs 19)) := by
  simp only [Stmt.fin, copyBody, seqs, pset, padd, iload, istore, pinc, ains]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · funext q; simp [Function.update_apply]; split_ifs <;> simp_all
  · simp [Function.update_apply]
lemma copy_loop (k : ℕ) (s : MState) (b : ℤ) (h13 : s.core.ptrs 13 = b)
    (h19 : s.core.ptrs 19 = 0) (h17 : s.core.ptrs 17 = 3 * k + 1) (hb : cDIG k + 3 * k < b) :
    ∃ s' m, Exec (.loop 17 19 (copyBody k)) s s' m ∧ m ≤ (3 * k + 1) * 8 + 1 ∧ Same s s' ∧
      (∀ q, q ≠ 6 → q ≠ 16 → q ≠ 19 → s'.core.ptrs q = s.core.ptrs q) ∧
      s'.intMem = fun z => if b ≤ z ∧ z ≤ b + 3 * k then s.intMem (cDIG k + (z - b)) else s.intMem z := by
  let Inv : ℕ → MState → Prop := fun j t => t.core.ptrs 19 = j ∧ Same s t ∧
    (∀ q, q ≠ 6 → q ≠ 16 → q ≠ 19 → t.core.ptrs q = s.core.ptrs q) ∧
    t.intMem = fun z => if b ≤ z ∧ z < b + j then s.intMem (cDIG k + (z - b)) else s.intMem z
  have hstep : ∀ j < 3 * k + 1, ∀ t, Inv j t → ¬ t.core.ptrs 17 ≤ t.core.ptrs 19 ∧
      ∃ s1 m, Exec (copyBody k) (tick t) s1 m ∧ m ≤ 6 ∧ Inv (j + 1) (tick s1) := by
    intro j hj t ⟨i19, isame, iptr, imem⟩
    have t17 : t.core.ptrs 17 = 3 * k + 1 := by rw [iptr 17 (by norm_num) (by norm_num) (by norm_num), h17]
    have t13 : t.core.ptrs 13 = b := by rw [iptr 13 (by norm_num) (by norm_num) (by norm_num), h13]
    obtain ⟨u1, u2, u3, u4, -, u6, u7⟩ := copyBody_fin k (tick t)
    refine ⟨by rw [t17, i19]; push_cast; omega, _, _, (copyBody k).exec_fin (copyBody_noLoop k) _,
      by simp [Stmt.steps, copyBody, seqs, pset, padd, iload, istore, pinc], ?_⟩
    refine ⟨?_, ⟨u1.trans isame.1, u2.trans isame.2.1, u3.trans isame.2.2.1, u4.trans isame.2.2.2⟩,
      ?_, ?_⟩
    · show ((copyBody k).fin (tick t)).core.ptrs 19 = _
      rw [u6]; simp [tick, i19]
    · intro q h6 h16 h19
      show ((copyBody k).fin (tick t)).core.ptrs q = _
      rw [u6]
      simp [tick, Function.update_of_ne h6, Function.update_of_ne h16, Function.update_of_ne h19,
        iptr q h6 h16 h19]
    · funext z
      show ((copyBody k).fin (tick t)).intMem z = _
      rw [u7]
      simp only [tick, i19, t13, Function.update_apply]
      rw [imem]
      dsimp only
      push_cast at hj ⊢
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
  have hend : ∀ t, Inv (3 * k + 1) t → t.core.ptrs 17 ≤ t.core.ptrs 19 := by
    rintro t ⟨i19, -, iptr, -⟩
    rw [iptr 17 (by norm_num) (by norm_num) (by norm_num), h17, i19]; push_cast; exact le_rfl
  obtain ⟨sT, m, ⟨i19, isame, iptr, imem⟩, hex, hm⟩ := loop_rule Inv (3 * k + 1) 6 hstep hend s
    ⟨h19, Same.refl s, fun q _ _ _ => rfl, by funext z; simp⟩
  refine ⟨tick sT, m, hex, hm, isame.tick, iptr, ?_⟩
  simp only [tick, imem]
  funext z
  congr 1
  apply propext; push_cast; constructor <;> intro h <;> omega

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

theorem incAt_flag (k n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j < Kc k n) :
    (incAt k n (3 * k) (Dseq k n j)).2 = true ↔ j + 1 = Kc k n := by
  rw [incAt_flag_iff k n hn _ _ (Dseq_inRange k n hn j), Dseq_val k n hn j hj, Kc_eq_oW]

theorem Kc_pos (k n : ℕ) (hn : 1 ≤ n) : 0 < Kc k n :=
  Finset.prod_pos (fun i _ => rad_pos k n hn i)

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

lemma bad_iff_not_valid (k n : ℕ) (D : ℕ → ℕ) (im : ℤ → ℤ) (hD : InRange k n D)
    (him : ∀ i ≤ 3 * k, im (cDIG k + i) = D i) :
    (∃ r : ℕ, r < k ∧ badM (D 0) r (im (cDIG k + r + 1)) (im (cDIG k + r + 1 + k))
      (im (cDIG k + r + 1 + k + k)) (im (cDIG k + (r + 1) + 1))) ↔ ¬ validD k D := by
  have hD' : ∀ i ≤ 3 * k, ∀ z, z = cDIG k + i → im z = D i := by
    intro i hi z hz; rw [hz]; exact him i hi
  have h0k : D 0 ≤ k := by have := hD 0 (by omega); simp [rad] at this; omega
  unfold validD
  rw [Classical.not_forall]
  apply exists_congr
  intro r
  rw [Classical.not_imp]
  apply and_congr_right
  intro hr
  rw [hD' (1 + r) (by omega) _ (by push_cast; ring), hD' (1 + k + r) (by omega) _ (by push_cast; ring),
    hD' (1 + 2 * k + r) (by omega) _ (by push_cast; ring)]
  unfold badM
  push_cast
  constructor
  · intro h h'
    obtain ⟨a1, a2⟩ := h'
    rcases h with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · obtain ⟨c1, c2, c3⟩ := a1 (by omega); apply b2; omega
    · obtain ⟨a2b, a2c⟩ := a2 (by omega)
      rcases b2 with b2 | ⟨b2, b3⟩
      · apply a2b; omega
      · have hc : r + 1 < D 0 := by omega
        have := a2c hc
        rw [hD' (1 + (r + 1)) (by omega) _ (by push_cast; ring)] at b3
        omega
  · intro h
    by_contra hh
    apply h
    refine ⟨fun h1 => ?_, fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩⟩
    · refine ⟨?_, ?_, ?_⟩ <;> (by_contra h3; apply hh; left; refine ⟨by omega, ?_⟩; omega)
    · apply hh; right; refine ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    · rw [hD' (1 + (r + 1)) (by omega) _ (by push_cast; ring)] at hh
      by_contra h3; apply hh; right; refine ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma iteS2_noLoop (k : ℕ) : (iteS2 k).NoLoop := by
  simp [iteS2, seqs, Stmt.NoLoop, pset, istore, skip, pcopy, Plain]

lemma iteS2_fin (k : ℕ) (v : MState) (h10 : v.core.ptrs 10 = 0) :
    let w := (iteS2 k).fin v
    Same v w ∧ w.work ≤ v.work + 4 ∧
    (∀ q, q ≠ 9 → w.core.ptrs q = v.core.ptrs q) ∧
    w.intMem = if v.core.ptrs 41 ≤ 0 then Function.update v.intMem (v.core.ptrs 13) (k + 1)
      else v.intMem := by
  intro w
  simp only [w, iteS2, seqs, Stmt.fin, h10]
  split_ifs <;> simp_all [Same, ains, tick, skip, pset, pcopy, istore, Stmt.fin, Function.update_apply]
    <;> omega

open Classical in
lemma body2_exec (k n : ℕ) (t : MState) (D : ℕ → ℕ) (b : ℤ) (j : ℤ)
    (h0 : t.core.ptrs 0 = n) (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1)
    (h46 : t.core.ptrs 46 = k) (h18 : t.core.ptrs 18 = 3 * k + 3) (h13 : t.core.ptrs 13 = b)
    (h14 : t.core.ptrs 14 = j) (h40 : t.core.ptrs 40 = 0)
    (hDr : InRange k n D) (hD : ∀ i ≤ 3 * k, t.intMem (cDIG k + i) = D i) (hb : cDIG k + 3 * k < b) :
    ∃ o m, Exec (body2 k) t o m ∧ m ≤ 130 * k + 60 ∧ Same t o ∧
      (∀ q, q ∉ ({6, 7, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 40, 41, 42} : Finset ℕ) →
        o.core.ptrs q = t.core.ptrs q) ∧
      o.core.ptrs 13 = b + (3 * k + 3) ∧ o.core.ptrs 14 = j + 1 ∧
      o.core.ptrs 40 = (if (incAt k n (3 * k) D).2 then 1 else 0) ∧
      (∀ i ≤ 3 * k, o.intMem (b + i) = if i = 0 then (if validD k D then (D 0 : ℤ) else k + 1)
        else D i) ∧
      (∀ i ≤ 3 * k, o.intMem (cDIG k + i) = (incAt k n (3 * k) D).1 i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → (z < b ∨ b + 3 * k < z) → o.intMem z = t.intMem z) := by
  -- stage 1: copy
  let t2 := ains (.core (.pset 17 (3 * k + 1))) (ains (.core (.pset 19 0)) t)
  obtain ⟨c, mc, ec, hmc, csame, cptr, cmem⟩ := copy_loop k t2 b (by simp [t2, ains, h13])
    (by simp [t2, ains]) (by simp [t2, ains]) hb
  have c_dig : ∀ i ≤ 3 * k, c.intMem (cDIG k + i) = D i := by
    intro i hi; rw [cmem]; simp only [t2, ains]; rw [if_neg (by omega)]; exact hD i hi
  have c_ptr : ∀ q, q ≠ 6 → q ≠ 16 → q ≠ 19 → q ≠ 17 → c.core.ptrs q = t.core.ptrs q := by
    intro q a b' c' d; rw [cptr q a b' c']; simp [t2, ains, Function.update_of_ne d, Function.update_of_ne c']
  -- stage 2: validation
  let t6 := ains (.core (.pset 19 0)) (ains (.core (.pset 41 1)) (ains (.integerLoad 20 6)
    (ains (.core (.pset 6 (cDIG k))) c)))
  have t6_20 : t6.core.ptrs 20 = D 0 := by
    have := c_dig 0 (by omega); simp only [Nat.cast_zero, add_zero] at this
    simp [t6, ains, this]
  have t6_mem : t6.intMem = c.intMem := rfl
  have t6_ptr : ∀ q, q ≠ 6 → q ≠ 16 → q ≠ 19 → q ≠ 17 → q ≠ 20 → q ≠ 41 → t6.core.ptrs q = t.core.ptrs q := by
    intro q a b' c' d e f
    simp [t6, ains, Function.update_of_ne a, Function.update_of_ne c', Function.update_of_ne e,
      Function.update_of_ne f, c_ptr q a b' c' d]
  obtain ⟨v, mv, ev, hmv, vsame, vmem, vptr, v41⟩ := valid_loop k t6
    (by rw [t6_ptr 46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h46])
    (by rw [t6_ptr 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h10])
    (by rw [t6_ptr 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h11])
    (by simp [t6, ains]) (by simp [t6, ains])
  have v41' : v.core.ptrs 41 = if validD k D then 1 else 0 := by
    rw [v41]
    have hiff := bad_iff_not_valid k n D c.intMem hDr c_dig
    by_cases hv : validD k D
    · rw [if_neg, if_pos hv]; rw [t6_20, t6_mem, hiff]; exact not_not.mpr hv
    · rw [if_pos, if_neg hv]; rw [t6_20, t6_mem, hiff]; exact hv
  -- stage 3: mark invalid
  have v10 : v.core.ptrs 10 = 0 := by
    rw [vptr 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), t6_ptr 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h10]
  have v13 : v.core.ptrs 13 = b := by
    rw [vptr 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), t6_ptr 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), h13]
  obtain ⟨w1, w2, w3, w4⟩ := iteS2_fin k v v10
  have ew := (iteS2 k).exec_fin (iteS2_noLoop k) v
  have hww := ew.work
  -- stage 4: advance and increment
  let w := (iteS2 k).fin v
  let t10 := ains (.core (.pset 15 (3 * k))) (ains (.core (.pset 42 1)) (ains (.core (.pinc 14))
    (ains (.pointerAdd 13 13 18) w)))
  have v_ptr : ∀ q, q ≠ 6 → q ≠ 7 → q ≠ 9 → q ≠ 16 → q ≠ 17 → q ≠ 19 → q ≠ 20 → q ≠ 21 → q ≠ 22 →
      q ≠ 23 → q ≠ 41 → w.core.ptrs q = t.core.ptrs q := by
    intro q a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    rw [w3 q a3, vptr q a1 a2 a3 a6 a8 a9 a10 a11, t6_ptr q a1 a4 a6 a5 a7 a11]
  have t10_ptr : ∀ q, q ∉ ({6, 7, 9, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 40, 41, 42} : Finset ℕ) →
      t10.core.ptrs q = t.core.ptrs q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hq
    simp [t10, ains, Function.update_of_ne a4, Function.update_of_ne a5, Function.update_of_ne a6,
      Function.update_of_ne a16, v_ptr q a1 a2 a3 a7 a8 a9 a10 a11 a12 a13 a15]
  have wmem : w.intMem = if validD k D then c.intMem else Function.update c.intMem b (k + 1) := by
    show ((iteS2 k).fin v).intMem = _
    rw [w4, vmem, v13, v41']
    by_cases hv : validD k D
    · simp [hv, t6_mem]
    · simp [hv, t6_mem]
  have t10_dig : ∀ i ≤ 3 * k, t10.intMem (cDIG k + i) = D i := by
    intro i hi
    show w.intMem _ = _
    rw [wmem]; split_ifs
    · exact c_dig i hi
    · rw [Function.update_of_ne (by omega)]; exact c_dig i hi
  obtain ⟨o, mo, eo, hmo, osame, optr, odig, omem, o40⟩ := odo_loop k n (3 * k) t10 D le_rfl
    (by simp [t10, ains]) (by simp [t10, ains])
    (by simp only [t10, ains]; simp [Function.update_of_ne]
        rw [v_ptr 40 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h40])
    (by rw [t10_ptr 46 (by simp), h46]) (by rw [t10_ptr 10 (by simp), h10]) (by rw [t10_ptr 0 (by simp), h0])
    t10_dig
  have hsw : (iteS2 k).steps v ≤ 4 := by
    have h1 : ((iteS2 k).fin v).work ≤ v.work + 4 := w2
    omega
  have ex : Exec (body2 k) t o (1 + (1 + (mc + (1 + (1 + (1 + (1 + (mv + ((iteS2 k).steps v +
      (1 + (1 + (1 + (1 + mo))))))))))))) := by
    unfold body2
    simp only [seqs]
    exact Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq ec
      (Exec.seq (Exec.ins _ c trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial)
      (Exec.seq (Exec.ins _ _ trivial) (Exec.seq ev (Exec.seq ew (Exec.seq (Exec.ins _ _ trivial)
      (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial)
      eo))))))))))))
  have w13 : w.core.ptrs 13 = b := by
    rw [v_ptr 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h13]
  have w18 : w.core.ptrs 18 = 3 * k + 3 := by
    rw [v_ptr 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h18]
  have w14 : w.core.ptrs 14 = j := by
    rw [v_ptr 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), h14]
  have t10mem : t10.intMem = w.intMem := rfl
  have cm : ∀ z, c.intMem z = if b ≤ z ∧ z ≤ b + 3 * k then t.intMem (cDIG k + (z - b)) else t.intMem z := by
    intro z; rw [cmem]; rfl
  refine ⟨o, _, ex, by omega, ?_, ?_, ?_, ?_, o40, ?_, odig, ?_⟩
  · have s1 : Same t t2 := ⟨rfl, rfl, rfl, rfl⟩
    have s2 : Same c t6 := ⟨rfl, rfl, rfl, rfl⟩
    have s3 : Same w t10 := ⟨rfl, rfl, rfl, rfl⟩
    exact ((((s1.trans csame).trans s2).trans vsame).trans w1).trans (s3.trans osame)
  · intro q hq
    have hq' := hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hq'
    rw [optr q a1 a3 a6 a7 a8 a14 a16, t10_ptr q hq]
  · rw [optr 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    simp [t10, ains, w13, w18]
  · rw [optr 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    simp [t10, ains, w14]
  · intro i hi
    rw [omem _ (Or.inr (by omega)), t10mem, wmem]
    by_cases hv : validD k D
    · rw [if_pos hv, cm, if_pos (by omega)]
      split_ifs with h0
      · subst h0; simp only [Nat.cast_zero, add_zero, sub_self] at *
        have := hD 0 (by omega); simpa using this
      · rw [show b + (i : ℤ) - b = i by ring]; exact hD i hi
    · rw [if_neg hv]
      split_ifs with h0
      · subst h0; simp
      · rw [Function.update_of_ne (by omega), cm, if_pos (by omega),
          show b + (i : ℤ) - b = i by ring]; exact hD i hi
  · intro z hz1 hz2
    rw [omem z hz1, t10mem, wmem]
    have : c.intMem z = t.intMem z := by rw [cm, if_neg (by omega)]
    split_ifs
    · exact this
    · rw [Function.update_of_ne (by omega)]; exact this

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma main2_loop (k n : ℕ) (hn : 1 ≤ n) (s : MState) (p : ℤ)
    (h0 : s.core.ptrs 0 = n) (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1)
    (h46 : s.core.ptrs 46 = k) (h18 : s.core.ptrs 18 = 3 * k + 3) (h13 : s.core.ptrs 13 = p + 1)
    (h14 : s.core.ptrs 14 = 0) (h40 : s.core.ptrs 40 = 0)
    (hD : ∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) (hp : cDIG k + 3 * k < p) :
    ∃ s' m, Exec (.loop 11 40 (body2 k)) s s' m ∧ m ≤ Kc k n * (130 * k + 62) + 1 ∧ Same s s' ∧
      (∀ q, q ∉ scr2 → s'.core.ptrs q = s.core.ptrs q) ∧ s'.core.ptrs 14 = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, s'.intMem (recAddr k p j + i) = recCell k n j i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → z ≤ p → s'.intMem z = s.intMem z) := by
  let K := Kc k n
  let Inv : ℕ → MState → Prop := fun j u =>
    u.core.ptrs 13 = recAddr k p j ∧ u.core.ptrs 14 = j ∧
    u.core.ptrs 40 = (if j = K then 1 else 0) ∧ Same s u ∧
    (∀ q, q ∉ scr2 → u.core.ptrs q = s.core.ptrs q) ∧
    (j < K → ∀ i ≤ 3 * k, u.intMem (cDIG k + i) = Dseq k n j i) ∧
    (∀ j' < j, ∀ i ≤ 3 * k, u.intMem (recAddr k p j' + i) = recCell k n j' i) ∧
    (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → z ≤ p → u.intMem z = s.intMem z)
  have hK : 0 < K := Kc_pos k n hn
  have hstep : ∀ j < K, ∀ u, Inv j u → ¬ u.core.ptrs 11 ≤ u.core.ptrs 40 ∧
      ∃ s1 m, Exec (body2 k) (tick u) s1 m ∧ m ≤ 130 * k + 60 ∧ Inv (j + 1) (tick s1) := by
    intro j hj u ⟨i13, i14, i40, isame, iptr, idig, irec, imem⟩
    have u11 : u.core.ptrs 11 = 1 := by rw [iptr 11 (by simp [scr2]), h11]
    have u40 : u.core.ptrs 40 = 0 := by rw [i40, if_neg (by omega)]
    have hb : cDIG k + 3 * k < recAddr k p j := by
      unfold recAddr; have : (0 : ℤ) ≤ j * (3 * k + 3) := by positivity
      omega
    obtain ⟨o, m, eo, hm, osame, optr, o13, o14, o40, orec, odig, omem⟩ := body2_exec k n (tick u)
      (Dseq k n j) (recAddr k p j) j
      (by simp only [tick_core]; rw [iptr 0 (by simp [scr2]), h0])
      (by simp only [tick_core]; rw [iptr 10 (by simp [scr2]), h10])
      (by simp only [tick_core]; rw [u11])
      (by simp only [tick_core]; rw [iptr 46 (by simp [scr2]), h46])
      (by simp only [tick_core]; rw [iptr 18 (by simp [scr2]), h18])
      (by simp only [tick_core]; rw [i13]) (by simp only [tick_core]; rw [i14])
      (by simp only [tick_core]; rw [u40])
      (Dseq_inRange k n hn j) (by simp only [tick_intMem]; exact idig hj) hb
    refine ⟨by rw [u11, u40]; norm_num, o, m, eo, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tick_core, o13]; unfold recAddr; push_cast; ring
    · simp only [tick_core, o14]; push_cast; ring
    · simp only [tick_core, o40]
      by_cases hj1 : j + 1 = K
      · rw [if_pos ((incAt_flag k n hn j hj).mpr hj1), if_pos hj1]
      · rw [if_neg (fun h => hj1 ((incAt_flag k n hn j hj).mp h)), if_neg hj1]
    · exact isame.trans (Same.trans (⟨rfl, rfl, rfl, rfl⟩ : Same u (tick u)) osame).tick
    · intro q hq; simp only [tick_core]; rw [optr q hq]; exact iptr q hq
    · intro _ i hi; simp only [tick_intMem]; rw [odig i hi, Dseq_succ]; rfl
    · intro j' hj' i hi
      simp only [tick_intMem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · have hge : p + 1 ≤ recAddr k p j' := by
          unfold recAddr; have : (0 : ℤ) ≤ j' * (3 * k + 3) := by positivity
          omega
        have hle : recAddr k p j' + 3 * k < recAddr k p j := by
          unfold recAddr
          have h1 : (j' : ℤ) + 1 ≤ j := by exact_mod_cast h
          have h2 : ((j' : ℤ) + 1) * (3 * k + 3) ≤ j * (3 * k + 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          linarith
        rw [omem _ (Or.inr (by omega)) (Or.inl (by omega))]
        exact irec j' h i hi
      · subst h
        rw [orec i hi]; rfl
    · intro z hz1 hz2
      simp only [tick_intMem]
      have hge : p + 1 ≤ recAddr k p j := by
        unfold recAddr; have : (0 : ℤ) ≤ j * (3 * k + 3) := by positivity
        omega
      rw [omem z hz1 (Or.inl (by omega))]; exact imem z hz1 hz2
  have hend : ∀ u, Inv K u → u.core.ptrs 11 ≤ u.core.ptrs 40 := by
    rintro u ⟨-, -, i40, -, iptr, -⟩
    rw [i40, if_pos rfl, iptr 11 (by simp [scr2]), h11]
  obtain ⟨sT, m, ⟨i13, i14, i40, isame, iptr, idig, irec, imem⟩, hex, hm⟩ :=
    loop_rule Inv K (130 * k + 60) hstep hend s
      ⟨by rw [h13]; simp [recAddr], h14, by rw [h40, if_neg (by omega)], Same.refl s,
        fun q _ => rfl, fun _ i hi => by rw [hD i hi]; simp [Dseq], fun j' hj' => absurd hj' (by omega),
        fun z _ _ => rfl⟩
  exact ⟨tick sT, m, hex, by linarith, isame.tick, iptr, i14, irec, imem⟩

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma S2_exec (k n : ℕ) (hn : 1 ≤ n) (s : MState) (p : ℤ)
    (h0 : s.core.ptrs 0 = n) (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1)
    (h46 : s.core.ptrs 46 = k) (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p)
    (hD : ∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) (hp : cDIG k + 3 * k < p) :
    ∃ s' m, Exec (S2 k) s s' m ∧ m ≤ Kc k n * (130 * k + 62) + 5 ∧ Same s s' ∧
      (∀ q, q ∉ scr2 → s'.core.ptrs q = s.core.ptrs q) ∧ s'.core.ptrs 14 = Kc k n ∧
      s'.intMem p = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, s'.intMem (recAddr k p j + i) = recCell k n j i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → z < p → s'.intMem z = s.intMem z) := by
  let t3 := ains (.core (.pset 40 0)) (ains (.core (.pset 14 0)) (ains (.pointerAdd 13 12 11) s))
  have e : ∀ q, q ≠ 13 → q ≠ 14 → q ≠ 40 → t3.core.ptrs q = s.core.ptrs q := by
    intro q a b c; simp [t3, ains, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c]
  obtain ⟨u, m, eu, hm, usame, uptr, u14, urec, umem⟩ := main2_loop k n hn t3 p
    (by rw [e 0 (by norm_num) (by norm_num) (by norm_num), h0])
    (by rw [e 10 (by norm_num) (by norm_num) (by norm_num), h10])
    (by rw [e 11 (by norm_num) (by norm_num) (by norm_num), h11])
    (by rw [e 46 (by norm_num) (by norm_num) (by norm_num), h46])
    (by rw [e 18 (by norm_num) (by norm_num) (by norm_num), h18])
    (by simp [t3, ains, h12, h11]) (by simp [t3, ains]) (by simp [t3, ains]) hD hp
  have u12 : u.core.ptrs 12 = p := by
    rw [uptr 12 (by simp [scr2]), e 12 (by norm_num) (by norm_num) (by norm_num), h12]
  have ex : Exec (S2 k) s (ains (.integerStore 12 14) u) (1 + (1 + (1 + (m + 1)))) := by
    unfold S2; simp only [seqs]
    exact Exec.seq (Exec.ins _ s trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial)
      (Exec.seq eu (Exec.ins _ u trivial))))
  refine ⟨_, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Same.trans (⟨rfl, rfl, rfl, rfl⟩ : Same s t3) usame).trans ⟨rfl, rfl, rfl, rfl⟩
  · intro q hq
    have : q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 40 := by simp [scr2] at hq; omega
    simp only [ains]; rw [uptr q hq, e q this.1 this.2.1 this.2.2]
  · simp only [ains]; exact u14
  · simp [ains, u12, u14]
  · intro j hj i hi
    have : p < recAddr k p j + i := by
      unfold recAddr; have : (0 : ℤ) ≤ j * (3 * k + 3) := by positivity
      omega
    simp only [ains, u12]; rw [Function.update_of_ne (by omega)]; exact urec j hj i hi
  · intro z hz1 hz2
    simp only [ains, u12]; rw [Function.update_of_ne (by omega), umem z hz1 (by omega)]; rfl

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
theorem solution : ∀ (k n : ℕ) (hn : 1 ≤ n) (s : MState) (p : ℤ)
    (h0 : s.core.ptrs 0 = n) (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1)
    (h46 : s.core.ptrs 46 = k) (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p)
    (hD : ∀ i ≤ 3 * k, s.intMem (cDIG k + i) = 0) (hp : cDIG k + 3 * k < p),
    ∃ s' m, Exec (S2 k) s s' m ∧ m ≤ Kc k n * (130 * k + 62) + 5 ∧ Same s s' ∧
      (∀ q, q ∉ scr2 → s'.core.ptrs q = s.core.ptrs q) ∧ s'.core.ptrs 14 = Kc k n ∧
      s'.intMem p = Kc k n ∧
      (∀ j < Kc k n, ∀ i ≤ 3 * k, s'.intMem (recAddr k p j + i) = recCell k n j i) ∧
      (∀ z, (z < cDIG k ∨ cDIG k + 3 * k < z) → z < p → s'.intMem z = s.intMem z) :=
  @LindbladStructLearn.Mach.A1.S2_exec
