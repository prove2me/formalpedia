-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.site_loop
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:38.524562+00:00
-- url     : https://prove2.me/submissions/4ca3df2c-7127-4444-a35a-0dfad8ebe89d

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_siteBody_sem

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

lemma siteBody_noLoop : siteBody.NoLoop := by
  simp [siteBody, seqs, Stmt.NoLoop, pset, padd, iload, pinc, skip, pcopy, Plain]

lemma site_loop (t : MState) (k n S : ℕ) (xs : ℕ → ℕ) (L1f L2f Af Bf : ℕ → Fin 4) (Vf Wf : ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (h19 : t.core.ptrs 19 = 0) (h20 : t.core.ptrs 20 = S) (htab : Tab t.intMem)
    (hm : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r) = (Af r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n) = (if Vf r then 1 else 0) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n) = (Bf r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n + n) = (if Wf r then 1 else 0)) :
    ∃ t' m, Exec (.loop 20 19 siteBody) t t' m ∧ m ≤ S * 57 + 1 ∧ Same t t' ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ scrS → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.ptrs 30 = (if ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r)
        then t.core.ptrs 30 else 0) ∧
      t'.core.ptrs 31 = t.core.ptrs 31 +
        ((∑ r ∈ Finset.range S, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r) : ℕ) : ℤ) := by
  let Inv : ℕ → MState → Prop := fun j u => u.core.ptrs 19 = j ∧ Same t u ∧ u.intMem = t.intMem ∧
    (∀ q, q ∉ scrS → u.core.ptrs q = t.core.ptrs q) ∧
    u.core.ptrs 30 = (if ∀ r < j, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r)
        then t.core.ptrs 30 else 0) ∧
    u.core.ptrs 31 = t.core.ptrs 31 +
        ((∑ r ∈ Finset.range j, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r) : ℕ) : ℤ)
  have hstep : ∀ j < S, ∀ u, Inv j u → ¬ u.core.ptrs 20 ≤ u.core.ptrs 19 ∧
      ∃ s1 m, Exec siteBody (tick u) s1 m ∧ m ≤ 55 ∧ Inv (j + 1) (tick s1) := by
    intro j hj u ⟨i19, isame, imem, iptr, i30, i31⟩
    have e : ∀ q, q ∉ scrS → u.core.ptrs q = t.core.ptrs q := iptr
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hm j hj
    have u13 := e 13 (by simp [scrS])
    have u4 := e 4 (by simp [scrS])
    obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := siteBody_sem (tick u) k n (xs j) (L1f j) (L2f j) (Af j) (Bf j)
      (Vf j) (Wf j) (by simp only [tick_core]; rw [e 10 (by simp [scrS]), h10])
      (by simp only [tick_core]; rw [e 46 (by simp [scrS]), h46])
      (by simp only [tick_core]; rw [e 0 (by simp [scrS]), h0]) (by simp only [tick_intMem, imem]; exact htab)
      (by simp only [tick_intMem, tick_core, imem, u13, i19]; exact a1)
      (by simp only [tick_intMem, tick_core, imem, u13, i19]; exact a2)
      (by simp only [tick_intMem, tick_core, imem, u13, i19]; exact a3)
      (by simp only [tick_intMem, tick_core, imem, u4]; exact a4)
      (by simp only [tick_intMem, tick_core, imem, u4]; exact a5)
      (by simp only [tick_intMem, tick_core, imem, u4]; exact a6)
      (by simp only [tick_intMem, tick_core, imem, u4]; exact a7)
    have hex := siteBody.exec_fin siteBody_noLoop (tick u)
    have hw := hex.work
    refine ⟨by rw [e 20 (by simp [scrS]), h20, i19]; push_cast; omega, _, _, hex, by omega, ?_⟩
    have su : Same u (tick u) := ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨?_, (isame.trans (su.trans v1)).tick, ?_, ?_, ?_, ?_⟩
    · simp only [tick_core]; rw [v6]; simp [i19]
    · simp only [tick_intMem]; rw [v2]; exact imem
    · intro q hq
      have hq' := hq
      simp only [scrS, Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩ := hq'
      simp only [tick_core]
      rw [v5 q b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16]; exact e q hq
    · simp only [tick_core]; rw [v7]
      simp only [tick_core, i30]
      by_cases hc : Bf j = letterMul (letterMul (L2f j) (Af j)) (L1f j)
      · rw [if_pos hc]
        congr 1
        apply propext
        constructor
        · intro h r hr; rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h' | h'
          · exact h r h'
          · subst h'; exact hc
        · intro h r hr; exact h r (by omega)
      · rw [if_neg hc, if_neg (fun h => hc (h j (by omega)))]
    · simp only [tick_core]; rw [v8]; simp only [tick_core, i31, Finset.sum_range_succ]; push_cast; ring
  have hend : ∀ u, Inv S u → u.core.ptrs 20 ≤ u.core.ptrs 19 := by
    rintro u ⟨i19, -, -, iptr, -⟩
    rw [iptr 20 (by simp [scrS]), h20, i19]
  obtain ⟨sT, m, ⟨i19, isame, imem, iptr, i30, i31⟩, hex, hm'⟩ := loop_rule Inv S 55 hstep hend t
    ⟨h19, Same.refl t, rfl, fun q _ => rfl, by simp, by simp⟩
  exact ⟨tick sT, m, hex, by linarith, isame.tick, imem, iptr, i30, i31⟩

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
theorem solution : ∀ (t : MState) (k n S : ℕ) (xs : ℕ → ℕ) (L1f L2f Af Bf : ℕ → Fin 4) (Vf Wf : ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h46 : t.core.ptrs 46 = k) (h0 : t.core.ptrs 0 = n)
    (h19 : t.core.ptrs 19 = 0) (h20 : t.core.ptrs 20 = S) (htab : Tab t.intMem)
    (hm : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r) = (Af r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n) = (if Vf r then 1 else 0) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n) = (Bf r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n + n) = (if Wf r then 1 else 0)),
    ∃ t' m, Exec (.loop 20 19 siteBody) t t' m ∧ m ≤ S * 57 + 1 ∧ Same t t' ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ scrS → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.ptrs 30 = (if ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r)
        then t.core.ptrs 30 else 0) ∧
      t'.core.ptrs 31 = t.core.ptrs 31 +
        ((∑ r ∈ Finset.range S, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r) : ℕ) : ℤ) :=
  @LindbladStructLearn.Mach.A1.site_loop
