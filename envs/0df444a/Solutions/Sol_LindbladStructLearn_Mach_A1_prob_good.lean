-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.prob_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:37.878604+00:00
-- url     : https://prove2.me/submissions/44dee87e-6043-4087-8ec6-284686e54d87

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

end LindbladStructLearn.Mach

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth

lemma letterPhase_eq (a b : Fin 4) : letterPhase a b = Complex.I ^ phexp a b := by
  fin_cases a <;> fin_cases b <;> simp [letterPhase, phexp, pow_three]

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

theorem Dseq_surj (k n : ℕ) (hn : 1 ≤ n) (D : ℕ → ℕ) (hD : InRange k n D) :
    ∃ j < Kc k n, ∀ i ≤ 3 * k, Dseq k n j i = D i := by
  have hlt : oval k n (3 * k) D < Kc k n := oval_lt k n _ D hD
  refine ⟨oval k n (3 * k) D, hlt, ?_⟩
  exact oval_inj k n _ _ _ (Dseq_inRange k n hn _) hD (Dseq_val k n hn _ hlt)

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

theorem alg1Sample_code (hD : InRange k n D) (hv : validD k D) (A : Pauli n) (v : Qubits n)
    (B : Pauli n) (w : Qubits n) :
    ∃ σ : Fin (D 0) → Fin n, (∀ r, (σ r : ℕ) = D (1 + r)) ∧
      alg1Sample (pairOf n k D) A v B w =
        if ∀ r : Fin (D 0), B (σ r) = letterMul (letterMul (L2 k D r) (A (σ r))) (L1 k D r) then
          (4 : ℂ) ^ D 0 * Complex.I ^ (∑ r : Fin (D 0),
            (phexp (L2 k D r) (A (σ r)) + phexp (letterMul (L2 k D r) (A (σ r))) (L1 k D r) +
              (if A (σ r) ≠ 0 ∧ v (σ r) = true then 2 else 0) +
              (if B (σ r) ≠ 0 ∧ w (σ r) = true then 2 else 0)))
        else 0 := by
  refine ⟨sig hD, fun r => rfl, ?_⟩
  unfold alg1Sample
  dsimp only
  have hSeq : pairSupport (pairOf n k D) = Finset.univ.map (sigE hD hv) := supp_eq hD hv
  have hcard : (pairSupport (pairOf n k D)).card = D 0 := card_pairOf hD hv
  set P := pairOf n k D with hP
  set S := pairSupport P with hS
  have hmem : ∀ r, sig hD r ∈ S := by
    intro r; rw [hSeq]; exact Finset.mem_map_of_mem _ (Finset.mem_univ r)
  have hP1 : ∀ r : Fin (D 0), P.1 (sig hD r) = L1 k D r := fun r => (pairOf_site hD hv r r.2 _ rfl).1
  have hP2 : ∀ r : Fin (D 0), P.2 (sig hD r) = L2 k D r := fun r => (pairOf_site hD hv r r.2 _ rfl).2
  have hoff : ∀ i, i ∉ S → P.1 i = 0 ∧ P.2 i = 0 := fun i hi => by
    rw [hS, mem_pairSupport] at hi; push Not at hi; exact hi
  have hR : ∀ (C : Pauli n) r, restrict S C (sig hD r) = C (sig hD r) := fun C r => if_pos (hmem r)
  have hRoff : ∀ (C : Pauli n) i, i ∉ S → restrict S C i = 0 := fun C i hi => if_neg hi
  have transport : ∀ f : Fin n → ℂ, (∀ i ∉ S, f i = 1) →
      ∏ i, f i = ∏ r : Fin (D 0), f (sig hD r) := by
    intro f hf
    rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => hf i hi), hSeq, Finset.prod_map]
    rfl
  have hcond : (restrict S B = pauliProd (pauliProd P.2 (restrict S A)) P.1) ↔
      ∀ r : Fin (D 0), B (sig hD r) =
        letterMul (letterMul (L2 k D r) (A (sig hD r))) (L1 k D r) := by
    constructor
    · intro h r
      have := congrFun h (sig hD r)
      simp only [pauliProd] at this
      rwa [hR, hR, hP1, hP2] at this
    · intro h
      funext i
      simp only [pauliProd]
      by_cases hi : i ∈ S
      · rw [hSeq] at hi
        obtain ⟨r, -, rfl⟩ := Finset.mem_map.1 hi
        change restrict S B (sig hD r) = letterMul (letterMul (P.2 (sig hD r))
          (restrict S A (sig hD r))) (P.1 (sig hD r))
        rw [hR, hR, hP1, hP2]; exact h r
      · rw [hRoff B i hi, hRoff A i hi, (hoff i hi).1, (hoff i hi).2]; rfl
  have hph1 : pauliPhase P.2 (restrict S A) =
      ∏ r : Fin (D 0), Complex.I ^ phexp (L2 k D r) (A (sig hD r)) := by
    unfold pauliPhase
    rw [transport]
    · exact Finset.prod_congr rfl (fun r _ => by rw [hR, hP2, letterPhase_eq])
    · intro i hi; rw [hRoff A i hi, (hoff i hi).2]; rfl
  have hph2 : pauliPhase (pauliProd P.2 (restrict S A)) P.1 =
      ∏ r : Fin (D 0), Complex.I ^ phexp (letterMul (L2 k D r) (A (sig hD r))) (L1 k D r) := by
    unfold pauliPhase pauliProd
    rw [transport]
    · exact Finset.prod_congr rfl (fun r _ => by rw [hR, hP2, hP1, letterPhase_eq])
    · intro i hi; rw [hRoff A i hi, (hoff i hi).2, (hoff i hi).1]; rfl
  have hbc : ∀ (C : Pauli n) (u : Qubits n), boolChar (support (restrict S C)) u =
      ∏ r : Fin (D 0), Complex.I ^ (if C (sig hD r) ≠ 0 ∧ u (sig hD r) = true then 2 else 0) := by
    intro C u
    unfold boolChar support
    rw [Finset.prod_filter, transport]
    · refine Finset.prod_congr rfl (fun r _ => ?_)
      rw [hR]
      by_cases h1 : C (sig hD r) ≠ 0 <;> by_cases h2 : u (sig hD r) = true <;>
        simp [h1, h2, Complex.I_sq]
    · intro i hi; rw [hRoff C i hi]; simp
  by_cases hc : ∀ r : Fin (D 0), B (sig hD r) =
      letterMul (letterMul (L2 k D r) (A (sig hD r))) (L1 k D r)
  · rw [if_pos (hcond.2 hc), if_pos hc, hcard, hph1, hph2, hbc A v, hbc B w]
    simp only [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, pow_add]
    ring
  · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc]

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

lemma pauliMatrix_eq_tens {n : ℕ} (p : Pauli n) :
    pauliMatrix p = tens (fun i => onePauli (p i)) := rfl

lemma onePauli_conjTranspose (a : Fin 4) : (onePauli a)ᴴ = onePauli a := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;> simp [onePauli, Matrix.conjTranspose_apply]

lemma onePauli_zero : onePauli 0 = 1 := by
  ext x y; cases x <;> cases y <;> simp [onePauli]

end LindbladStructLearn.FourierAux


namespace LindbladStructLearn.AAux
open LindbladTolerant.Testing LindbladStructLearn LindbladStructLearn.FourierAux

variable {n : ℕ}

lemma onePauli_mul (a b : Fin 4) :
    onePauli a * onePauli b = letterPhase a b • onePauli (letterMul a b) := by
  ext x y
  fin_cases a <;> fin_cases b <;> cases x <;> cases y <;>
    simp [onePauli, letterPhase, letterMul, Matrix.mul_apply]

lemma tens_smul (c : Fin n → ℂ) (a : Fin n → Op Bool) :
    tens (fun i => c i • a i) = (∏ i, c i) • tens a := by
  ext x y
  simp [tens, Finset.prod_mul_distrib]

lemma pauliMatrix_mul (P Q : Pauli n) :
    pauliMatrix P * pauliMatrix Q = pauliPhase P Q • pauliMatrix (pauliProd P Q) := by
  rw [pauliMatrix_eq_tens, pauliMatrix_eq_tens, tens_mul]
  simp_rw [onePauli_mul]
  rw [tens_smul]
  rfl

lemma mem_support_iff (p : Pauli n) (i : Fin n) : i ∈ support p ↔ p i ≠ 0 := by
  simp [support]

lemma letterMul_self (x : Fin 4) : letterMul x x = 0 := by
  fin_cases x <;> simp [letterMul]

lemma not_mem_support_iff (p : Pauli n) (i : Fin n) : i ∉ support p ↔ p i = 0 := by
  simp [support]

lemma restrict_support_sub (S : Finset (Fin n)) (Q : Pauli n) : support (restrict S Q) ⊆ S := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  exact hi (by simp [restrict, h])

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

lemma boolChar_eq (S : Finset (Fin n)) (v : Qubits n) :
    boolChar S v = ∏ i, (if i ∈ S then (if v i then (-1 : ℂ) else 1) else 1) := by
  rw [boolChar, Finset.prod_ite_mem, Finset.univ_inter]

lemma one_eigen_sum (a : Fin 4) :
    ∑ b : Bool, oneEigenProj a b = 1 := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;>
    simp [oneEigenProj, onePauli, Fintype.sum_bool] <;> norm_num

lemma one_eigen_signed (a : Fin 4) (ha : a ≠ 0) :
    ∑ b : Bool, (if b then (-1 : ℂ) else 1) • oneEigenProj a b = onePauli a := by
  ext x y
  fin_cases a <;> cases x <;> cases y <;>
    simp_all [oneEigenProj, onePauli, Fintype.sum_bool] <;> ring

/-- eigendecomposition: `Σ_w χ_{S_Z}(w) |B,w⟩⟨B,w| = Z` for `Z = B^S` -/
lemma eigen_decomp (S : Finset (Fin n)) (B : Pauli n) :
    ∑ w : Qubits n, boolChar (support (restrict S B)) w • eigenProj B w =
      pauliMatrix (restrict S B) := by
  simp_rw [boolChar_eq, eigenProj_eq, ← tens_smul]
  rw [sum_tens (fun i b => (if i ∈ support (restrict S B) then (if b = true then (-1 : ℂ) else 1)
    else 1) • oneEigenProj (B i) b), pauliMatrix_eq_tens]
  congr 1
  funext i
  by_cases hi : i ∈ support (restrict S B)
  · simp only [hi, if_true]
    have hz : restrict S B i ≠ 0 := (mem_support_iff _ _).1 hi
    have hB : restrict S B i = B i := by
      simp only [restrict] at hz ⊢; split_ifs at hz ⊢ with h; rfl; exact absurd rfl hz
    rw [hB] at hz ⊢
    exact one_eigen_signed _ hz
  · simp only [hi, if_false, one_smul]
    rw [(not_mem_support_iff _ _).1 hi, one_eigen_sum, onePauli_zero]

lemma applySuper_add_right (g : Super (Qubits n) (Qubits n)) (X Y : Op (Qubits n)) :
    applySuper g (X + Y) = applySuper g X + applySuper g Y := by
  ext i j
  simp only [applySuper, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma applySuper_smul_right (g : Super (Qubits n) (Qubits n)) (c : ℂ) (X : Op (Qubits n)) :
    applySuper g (c • X) = c • applySuper g X := by
  ext i j
  simp only [applySuper, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  ring

lemma applySuper_sum_smul {ι : Type*} (s : Finset ι) (g : Super (Qubits n) (Qubits n))
    (c : ι → ℂ) (X : ι → Op (Qubits n)) :
    applySuper g (∑ v ∈ s, c v • X v) = ∑ v ∈ s, c v • applySuper g (X v) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i j; simp [applySuper]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, applySuper_add_right, applySuper_smul_right, ih]

/-- sum of `bornAmp` against the two characters -/
lemma born_sum (Φ : Super (Qubits n) (Qubits n)) (S : Finset (Fin n)) (A B : Pauli n) :
    ∑ v : Qubits n, ∑ w : Qubits n, bornAmp Φ A v B w *
      (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w) =
      (pauliMatrix (restrict S B) * applySuper Φ (pauliMatrix (restrict S A))).trace := by
  rw [← eigen_decomp S A, ← eigen_decomp S B, applySuper_sum_smul]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
  rw [bornAmp]
  ring

/-- fibres of the restriction map -/
lemma card_restrict_fibre (S : Finset (Fin n)) (R : Pauli n) (hR : R ∈ paulisOn S) :
    (Finset.univ.filter (fun A : Pauli n => restrict S A = R)).card = 4 ^ (n - S.card) := by
  have hR' : ∀ i, i ∉ S → R i = 0 := by
    intro i hi
    simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    by_contra h
    exact hi (hR ((mem_support_iff R i).2 h))
  have : Finset.univ.filter (fun A : Pauli n => restrict S A = R) =
      Fintype.piFinset (fun i => if i ∈ S then {R i} else (Finset.univ : Finset (Fin 4))) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, funext_iff,
      restrict]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · have := h i; simp only [hi, if_true] at this; simp [hi, this]
      · simp [hi]
    · intro h i
      by_cases hi : i ∈ S
      · have := h i; simp only [hi, if_true, Finset.mem_singleton] at this; simp [hi, this]
      · simp [hi, hR' i hi]
  rw [this, Fintype.card_piFinset]
  have : ∀ i, ((if i ∈ S then {R i} else (Finset.univ : Finset (Fin 4))) : Finset (Fin 4)).card =
      if i ∈ S then 1 else 4 := by
    intro i; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

lemma sum_restrict (S : Finset (Fin n)) (f : Pauli n → ℂ) :
    ∑ A : Pauli n, f (restrict S A) = (4 : ℂ) ^ (n - S.card) * ∑ R ∈ paulisOn S, f R := by
  classical
  have hmem : ∀ A : Pauli n, restrict S A ∈ paulisOn S := by
    intro A
    simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact restrict_support_sub S A
  rw [← Finset.sum_fiberwise_of_maps_to (fun A _ => hmem A)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun R hR => ?_)
  rw [Finset.sum_congr rfl (fun A hA => by rw [(Finset.mem_filter.1 hA).2]),
    Finset.sum_const, card_restrict_fibre S R hR]
  simp


lemma pauliMatrix_conjTranspose (P : Pauli n) : (pauliMatrix P)ᴴ = pauliMatrix P := by
  rw [pauliMatrix_eq_tens, tens_conjTranspose]
  simp_rw [onePauli_conjTranspose]

lemma pauliProd_mem (S : Finset (Fin n)) (P Q : Pauli n) (hP : support P ⊆ S) (hQ : support Q ⊆ S) :
    support (pauliProd P Q) ⊆ S := by
  intro i hi
  rw [mem_support_iff] at hi
  by_contra h
  apply hi
  have h1 := (not_mem_support_iff P i).1 (fun x => h (hP x))
  have h2 := (not_mem_support_iff Q i).1 (fun x => h (hQ x))
  simp [pauliProd, h1, h2, letterMul_self]

open Classical in
theorem proposition_2_9_aux (Φ : Super (Qubits n) (Qubits n)) (P : Pauli n × Pauli n) :
    ∑ A : Pauli n, ∑ v : Qubits n, ∑ B : Pauli n, ∑ w : Qubits n,
      ((1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n)) * bornAmp Φ A v B w * alg1Sample P A v B w =
      locFourier Φ P := by
  set S := pairSupport P with hS
  have hP1 : support P.1 ⊆ S := Finset.subset_union_left
  have hP2 : support P.2 ⊆ S := Finset.subset_union_right
  set c0 : ℂ := (1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n) with hc0
  set W : Pauli n → Pauli n := fun R => pauliProd (pauliProd P.2 R) P.1 with hW
  set g : Pauli n → ℂ := fun R =>
    (pauliMatrix P.2 * pauliMatrix R * pauliMatrix P.1 * applySuper Φ (pauliMatrix R)).trace with hg
  -- step 1+2+3: inner sums
  have inner : ∀ A B : Pauli n, ∑ v : Qubits n, ∑ w : Qubits n,
      c0 * bornAmp Φ A v B w * alg1Sample P A v B w =
      c0 * (4 : ℂ) ^ S.card * ((if restrict S B = W (restrict S A) then 1 else 0) *
        g (restrict S A)) := by
    intro A B
    by_cases hZ : restrict S B = W (restrict S A)
    · have hsamp : ∀ v w, alg1Sample P A v B w = (4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) *
          (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w) := by
        intro v w
        simp only [alg1Sample]
        rw [if_pos hZ]
        ring
      simp_rw [hsamp]
      have : ∀ v w, c0 * bornAmp Φ A v B w * ((4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) *
          (boolChar (support (restrict S A)) v * boolChar (support (restrict S B)) w)) =
          (c0 * (4 : ℂ) ^ S.card *
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1)) *
          (bornAmp Φ A v B w * (boolChar (support (restrict S A)) v *
            boolChar (support (restrict S B)) w)) := by intro v w; ring
      simp_rw [this, ← Finset.mul_sum]
      rw [born_sum, if_pos hZ, one_mul, hZ]
      simp only [hg, hW]
      have hm : pauliMatrix P.2 * pauliMatrix (restrict S A) * pauliMatrix P.1 =
          (pauliPhase P.2 (restrict S A) * pauliPhase (pauliProd P.2 (restrict S A)) P.1) •
            pauliMatrix (pauliProd (pauliProd P.2 (restrict S A)) P.1) := by
        rw [pauliMatrix_mul P.2, Matrix.smul_mul, pauliMatrix_mul, smul_smul]
      rw [hm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      ring
    · have hsamp : ∀ v w, alg1Sample P A v B w = 0 := by
        intro v w; simp only [alg1Sample]; rw [if_neg hZ]
      simp [hsamp, hZ]
  rw [Finset.sum_congr rfl (fun A _ => by rw [Finset.sum_comm])]
  simp_rw [inner]
  -- sum over B
  have hB : ∀ A : Pauli n, ∑ B : Pauli n, c0 * (4 : ℂ) ^ S.card *
      ((if restrict S B = W (restrict S A) then 1 else 0) * g (restrict S A)) =
      c0 * (4 : ℂ) ^ S.card * ((4 : ℂ) ^ (n - S.card) * g (restrict S A)) := by
    intro A
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    rw [sum_restrict S (fun Z => if Z = W (restrict S A) then (1 : ℂ) else 0)]
    rw [Finset.sum_ite_eq', if_pos]
    · ring
    · simp only [paulisOn, Finset.mem_filter, Finset.mem_univ, true_and, hW]
      exact pauliProd_mem S _ _ (pauliProd_mem S _ _ hP2 (restrict_support_sub S A)) hP1
  simp_rw [hB]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    sum_restrict S (fun R => g R)]
  -- the local Fourier coefficient
  have hloc : locFourier Φ P = (∑ R ∈ paulisOn S, g R) / (2 : ℂ) ^ n / (4 : ℂ) ^ S.card := by
    unfold locFourier pauliAvg
    rw [← hS]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    simp only [ntr, chi, hg, Matrix.conjTranspose_mul, pauliMatrix_conjTranspose, Matrix.mul_assoc]
  rw [hloc, hc0]
  have hsn : S.card ≤ n := by
    calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have h4 : (4 : ℂ) ^ (n - S.card) * (4 : ℂ) ^ S.card = 4 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hsn]
  have h4ne : (4 : ℂ) ^ S.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4n : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  have h4' : (4 : ℂ) ^ (S.card * 2) * 4 ^ ((n - S.card) * 2) = 4 ^ (n * 2) := by
    rw [← pow_add]; congr 1; omega
  linear_combination (∑ R ∈ paulisOn S, g R) * h4'

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

lemma bornAmp_im (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) (w : Qubits n) : (bornAmp Φ A v B w).im = 0 :=
  ((Complex.nonneg_iff.1 (bornAmp_nonneg Φ hΦ A v B w)).2).symm

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

/-- Sum over `ω : Fin M → X` of a product factors as a power. -/
theorem sum_prod_factor (q : X → ℝ) (M : ℕ) :
    ∑ ω : Fin M → X, ∏ i, q (ω i) = (∑ x, q x) ^ M := by
  rw [← Fintype.prod_sum (fun (_ : Fin M) x => q x)]
  simp

/-- The product weights sum to one. -/
theorem prod_weight_sum (p : X → ℝ) (hp1 : ∑ x, p x = 1) (M : ℕ) :
    ∑ ω : Fin M → X, ∏ i, p (ω i) = 1 := by
  rw [sum_prod_factor, hp1, one_pow]

/-- Single-variable MGF bound for a centered bounded variable. -/
theorem mgf_le (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (g : X → ℝ) (b : ℝ) (hg : ∀ x, |g x| ≤ b) (hmean : ∑ x, p x * g x = 0)
    (l : ℝ) (hl : 0 ≤ l) (hlb : l * b ≤ 1) :
    ∑ x, p x * Real.exp (l * g x) ≤ Real.exp (l ^ 2 * b ^ 2) := by
  have key : ∀ x, Real.exp (l * g x) ≤ 1 + l * g x + l ^ 2 * b ^ 2 := by
    intro x
    have h1 : |l * g x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hl]
      calc l * |g x| ≤ l * b := mul_le_mul_of_nonneg_left (hg x) hl
        _ ≤ 1 := hlb
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 : (l * g x) ^ 2 ≤ l ^ 2 * b ^ 2 := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg l)
      exact sq_le_sq' (abs_le.mp (hg x)).1 (abs_le.mp (hg x)).2
    have := (abs_le.mp h2).2
    linarith
  calc ∑ x, p x * Real.exp (l * g x) ≤ ∑ x, p x * (1 + l * g x + l ^ 2 * b ^ 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (key x) (hp x)
    _ = (∑ x, p x) + l * (∑ x, p x * g x) + (∑ x, p x) * (l ^ 2 * b ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = 1 + l ^ 2 * b ^ 2 := by rw [hp1, hmean]; ring
    _ ≤ Real.exp (l ^ 2 * b ^ 2) := by
        have := Real.add_one_le_exp (l ^ 2 * b ^ 2); linarith

/-- One-sided Chernoff bound for a sum of i.i.d. centered bounded variables. -/
theorem one_sided (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (g : X → ℝ) (b : ℝ) (hg : ∀ x, |g x| ≤ b) (hmean : ∑ x, p x * g x = 0)
    (l : ℝ) (hl : 0 ≤ l) (hlb : l * b ≤ 1) (M : ℕ) (s : ℝ) :
    ∑ ω : Fin M → X, (∏ i, p (ω i)) * (if s < ∑ i, g (ω i) then (1 : ℝ) else 0)
      ≤ Real.exp (-(l * s) + M * (l ^ 2 * b ^ 2)) := by
  have hind : ∀ ω : Fin M → X, (if s < ∑ i, g (ω i) then (1 : ℝ) else 0)
      ≤ Real.exp (-(l * s)) * ∏ i, Real.exp (l * g (ω i)) := by
    intro ω
    rw [← Real.exp_sum, ← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      rw [← Finset.mul_sum]; nlinarith
    · exact (Real.exp_pos _).le
  calc _ ≤ ∑ ω : Fin M → X,
        (∏ i, p (ω i)) * (Real.exp (-(l * s)) * ∏ i, Real.exp (l * g (ω i))) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hind ω) (prod_weight_nonneg p hp ω)
    _ = Real.exp (-(l * s)) * ∑ ω : Fin M → X, ∏ i, (p (ω i) * Real.exp (l * g (ω i))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = Real.exp (-(l * s)) * (∑ x, p x * Real.exp (l * g x)) ^ M := by
        rw [sum_prod_factor (fun x => p x * Real.exp (l * g x))]
    _ ≤ Real.exp (-(l * s)) * Real.exp (l ^ 2 * b ^ 2) ^ M := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀
          (Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (Real.exp_pos _).le)
        exact mgf_le p hp hp1 g b hg hmean l hl hlb
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

/-- One-sided Hoeffding bound with the optimized parameter. -/
theorem one_sided_hoeffding (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (g : X → ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, |g x| ≤ 2 * c)
    (hmean : ∑ x, p x * g x = 0) (M : ℕ) (t : ℝ) (ht : 0 < t) :
    ∑ ω : Fin M → X, (∏ i, p (ω i)) * (if (M : ℝ) * t < ∑ i, g (ω i) then (1 : ℝ) else 0)
      ≤ Real.exp (-(M * t ^ 2) / (16 * c ^ 2)) := by
  by_cases htc : t ≤ 2 * c
  · have hlb : t / (8 * c ^ 2) * (2 * c) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
    have h := one_sided p hp hp1 g (2 * c) hg hmean (t / (8 * c ^ 2)) (by positivity) hlb
      M (M * t)
    have e : -(t / (8 * c ^ 2) * (M * t)) + M * ((t / (8 * c ^ 2)) ^ 2 * (2 * c) ^ 2)
        = -(M * t ^ 2) / (16 * c ^ 2) := by
      field_simp; ring
    rw [e] at h; exact h
  · have hz : ∀ ω : Fin M → X,
        (if (M : ℝ) * t < ∑ i, g (ω i) then (1 : ℝ) else 0) = 0 := by
      intro ω
      rw [if_neg (not_lt.mpr ?_)]
      calc ∑ i, g (ω i) ≤ ∑ _i : Fin M, 2 * c :=
            Finset.sum_le_sum fun i _ => (abs_le.mp (hg (ω i))).2
        _ = M * (2 * c) := by simp
        _ ≤ M * t := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    simp only [hz, mul_zero, Finset.sum_const_zero]
    exact (Real.exp_pos _).le


/-- Finite Hoeffding bound with a union bound over a finite family of test functions. -/
theorem finite_hoeffding_union {X J : Type*} [Fintype X] [Fintype J] (p : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (f : J → X → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ j x, |f j x| ≤ c)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 < t) :
    ∑ ω : Fin M → X, (∏ i, p (ω i)) *
      (if ∃ j, t < |(∑ i, f j (ω i)) / M - ∑ x, p x * f j x| then (1 : ℝ) else 0)
    ≤ 2 * Fintype.card J * Real.exp (-(M * t ^ 2) / (16 * c ^ 2)) := by
  set m : J → ℝ := fun j => ∑ x, p x * f j x with hm
  set E := Real.exp (-(M * t ^ 2) / (16 * c ^ 2)) with hE
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hmb : ∀ j, |m j| ≤ c := by
    intro j
    calc |m j| ≤ ∑ x, |p x * f j x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, p x * |f j x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (hp x)]
      _ ≤ ∑ x, p x * c := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hf j x) (hp x)
      _ = c := by rw [← Finset.sum_mul, hp1, one_mul]
  have hmean1 : ∀ j, ∑ x, p x * (f j x - m j) = 0 := by
    intro j
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hm]
    ring
  have hmean2 : ∀ j, ∑ x, p x * (m j - f j x) = 0 := by
    intro j
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hm]
    ring
  have hb1 : ∀ j x, |f j x - m j| ≤ 2 * c := by
    intro j x
    calc |f j x - m j| ≤ |f j x| + |m j| := abs_sub _ _
      _ ≤ 2 * c := by linarith [hf j x, hmb j]
  have hb2 : ∀ j x, |m j - f j x| ≤ 2 * c := by
    intro j x; rw [abs_sub_comm]; exact hb1 j x
  -- pointwise union bound
  have hind : ∀ ω : Fin M → X,
      (if ∃ j, t < |(∑ i, f j (ω i)) / M - m j| then (1 : ℝ) else 0) ≤
      ∑ j, ((if (M : ℝ) * t < ∑ i, (f j (ω i) - m j) then (1 : ℝ) else 0) +
            (if (M : ℝ) * t < ∑ i, (m j - f j (ω i)) then (1 : ℝ) else 0)) := by
    intro ω
    have hnn : ∀ j ∈ (Finset.univ : Finset J), (0 : ℝ) ≤
        (if (M : ℝ) * t < ∑ i, (f j (ω i) - m j) then (1 : ℝ) else 0) +
        (if (M : ℝ) * t < ∑ i, (m j - f j (ω i)) then (1 : ℝ) else 0) := by
      intro j _
      apply add_nonneg <;> split_ifs <;> norm_num
    by_cases h : ∃ j, t < |(∑ i, f j (ω i)) / M - m j|
    · rw [if_pos h]
      obtain ⟨j, hj⟩ := h
      refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ j))
      set S := ∑ i, f j (ω i) with hS
      have e1 : ∑ i, (f j (ω i) - m j) = S - M * m j := by
        simp [Finset.sum_sub_distrib, hS]
      have e2 : ∑ i, (m j - f j (ω i)) = M * m j - S := by
        simp [Finset.sum_sub_distrib, hS]
      have hSq : S = M * (S / M) := by field_simp
      rw [e1, e2]
      rcases lt_abs.mp hj with h1 | h1
      · have : (M : ℝ) * t < S - M * m j := by
          rw [hSq]
          have := mul_lt_mul_of_pos_left h1 hMpos
          linarith
        rw [if_pos this]
        split_ifs <;> norm_num
      · have : (M : ℝ) * t < M * m j - S := by
          rw [hSq]
          have := mul_lt_mul_of_pos_left h1 hMpos
          linarith
        rw [if_pos this]
        split_ifs <;> norm_num
    · rw [if_neg h]
      exact Finset.sum_nonneg hnn
  calc _ ≤ ∑ ω : Fin M → X, (∏ i, p (ω i)) *
        ∑ j, ((if (M : ℝ) * t < ∑ i, (f j (ω i) - m j) then (1 : ℝ) else 0) +
            (if (M : ℝ) * t < ∑ i, (m j - f j (ω i)) then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hind ω) (prod_weight_nonneg p hp ω)
    _ = ∑ j, ((∑ ω : Fin M → X, (∏ i, p (ω i)) *
            (if (M : ℝ) * t < ∑ i, (f j (ω i) - m j) then (1 : ℝ) else 0)) +
          (∑ ω : Fin M → X, (∏ i, p (ω i)) *
            (if (M : ℝ) * t < ∑ i, (m j - f j (ω i)) then (1 : ℝ) else 0))) := by
        simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
    _ ≤ ∑ _j : J, (E + E) := by
        refine Finset.sum_le_sum fun j _ => add_le_add ?_ ?_
        · exact one_sided_hoeffding p hp hp1 (fun x => f j x - m j) c hc (hb1 j)
            (hmean1 j) M t ht
        · exact one_sided_hoeffding p hp hp1 (fun x => m j - f j x) c hc (hb2 j)
            (hmean2 j) M t ht
    _ = 2 * Fintype.card J * E := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end LindbladStructLearn.Hoeff

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

def c5e (c : C5) : Fin 4 × Bool × Fin 4 := (letA c, bitV c, letB c)

lemma c5e_bij : Function.Bijective c5e := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro a b h
  revert a b
  decide

def c5equiv : C5 ≃ Fin 4 × Bool × Fin 4 := Equiv.ofBijective c5e c5e_bij

def strEquiv (n : ℕ) : (Fin n → C5) ≃ Pauli n × Qubits n × Pauli n :=
  (Equiv.arrowCongr (Equiv.refl _) c5equiv).trans
    ((Equiv.arrowProdEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.arrowProdEquivProdArrow _ _ _)))

lemma strEquiv_apply (n : ℕ) (g : Fin n → C5) :
    strEquiv n g = (fun j => letA (g j), fun j => bitV (g j), fun j => letB (g j)) := rfl

lemma reindex {β : Type*} [AddCommMonoid β] (n : ℕ) (F : Pauli n → Qubits n → Pauli n → β) :
    ∑ g : Fin n → C5, F (fun j => letA (g j)) (fun j => bitV (g j)) (fun j => letB (g j)) =
      ∑ A : Pauli n, ∑ v : Qubits n, ∑ B : Pauli n, F A v B := by
  rw [← (strEquiv n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun A => Fintype.sum_congr _ _ fun v => Fintype.sum_congr _ _ fun B => ?_
  have : strEquiv n ((strEquiv n).symm (A, v, B)) = (A, v, B) := Equiv.apply_symm_apply _ _
  rw [strEquiv_apply] at this
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2, h3⟩ := this
  rw [h1, h2, h3]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

lemma pw_nonneg (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (x : Rd n) : 0 ≤ pw Φ x :=
  mul_nonneg (by positivity) (bornAmp_re_nonneg Φ hΦ _ _ _ _)

lemma pw_sum (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) : ∑ x : Rd n, pw Φ x = 1 := by
  rw [Fintype.sum_prod_type]
  have hA : ∀ (g : Fin n → C5) (w : Qubits n), xA (g, w) = fun j => letA (g j) := fun _ _ => rfl
  have hV : ∀ (g : Fin n → C5) (w : Qubits n), xV (g, w) = fun j => bitV (g j) := fun _ _ => rfl
  have hB : ∀ (g : Fin n → C5) (w : Qubits n), xB (g, w) = fun j => letB (g j) := fun _ _ => rfl
  simp only [pw, hA, hV, hB, ← Finset.mul_sum]
  simp only [bornAmp_re_sum Φ hΦ, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card (Fin n → C5) = 32 ^ n := by
    rw [Fintype.card_fun]; simp [C5]
  rw [hc]; push_cast; rw [← mul_pow]; norm_num

lemma pw_mean (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (Q : Pauli n × Pauli n) :
    ∑ x : Rd n, (pw Φ x : ℂ) * alg1Sample Q (xA x) (xV x) (xB x) x.2 = locFourier Φ Q := by
  rw [← AAux.proposition_2_9_aux Φ Q, Fintype.sum_prod_type]
  rw [← reindex n (fun A v B => ∑ w : Qubits n, ((1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n)) *
    bornAmp Φ A v B w * alg1Sample Q A v B w)]
  refine Fintype.sum_congr _ _ fun g => Fintype.sum_congr _ _ fun w => ?_
  have him := bornAmp_im Φ hΦ (xA (g, w)) (xV (g, w)) (xB (g, w)) w
  have hb : bornAmp Φ (xA (g, w)) (xV (g, w)) (xB (g, w)) w =
      ((bornAmp Φ (xA (g, w)) (xV (g, w)) (xB (g, w)) w).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  simp only [pw]
  rw [show (fun j => letA (g j)) = xA (g, w) from rfl, show (fun j => bitV (g j)) = xV (g, w) from rfl,
    show (fun j => letB (g j)) = xB (g, w) from rfl]
  rw [hb]
  push_cast
  have : (1 / 32 : ℂ) ^ n = (1 / 4 ^ n) * (1 / 2 ^ n) * (1 / 4 ^ n) := by
    rw [div_pow, one_pow, show (32 : ℂ) ^ n = 4 ^ n * 2 ^ n * 4 ^ n by
      rw [← mul_pow, ← mul_pow]; norm_num]
    field_simp
  rw [this]; simp only [Complex.ofReal_re]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

variable {n : ℕ}

lemma alg1Sample_norm_le (k : ℕ) (hn : 0 < n) (Q : Pauli n × Pauli n) (hQ : (pairSupport Q).card ≤ k)
    (A : Pauli n) (v : Qubits n) (B : Pauli n) (w : Qubits n) :
    ‖alg1Sample Q A v B w‖ ≤ 4 ^ k := by
  obtain ⟨D, hD, hv, rfl⟩ := exists_code hn Q hQ
  obtain ⟨σ, -, he⟩ := alg1Sample_code hD hv A v B w
  rw [he]
  have hs := s_le hD
  split_ifs
  · rw [norm_mul, norm_pow, norm_pow, Complex.norm_I, one_pow, mul_one]
    simp only [Complex.norm_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hs
  · simp

lemma card_JQ (k : ℕ) (hn : 1 ≤ n) : Fintype.card (JQ n k) ≤ Kc k n := by
  have key : ∀ Q : JQ n k, ∃ j : Fin (Kc k n), pairOf n k (Dseq k n j) = Q.1 := by
    intro Q
    obtain ⟨D, hD, hv, hDQ⟩ := exists_code hn Q.1 Q.2
    obtain ⟨j0, hj0, hag⟩ := Dseq_surj k n hn D hD
    exact ⟨⟨j0, hj0⟩, by rw [← hDQ]; exact pairOf_congr k n _ _ (Dseq_inRange k n hn j0) hag⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    rw [← hf a, ← hf b, h]
  simpa using Fintype.card_le_of_injective f hinj

lemma prob_good (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (k : ℕ) (hn : 1 ≤ n) (M : ℕ)
    (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    1 - 4 * Kc k n * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤
      ∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
        (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
          then (1 : ℝ) else 0) := by
  classical
  let f : JQ n k × Bool → Rd n → ℝ := fun j x =>
    if j.2 then (alg1Sample j.1.1 (xA x) (xV x) (xB x) x.2).re
    else (alg1Sample j.1.1 (xA x) (xV x) (xB x) x.2).im
  have hf : ∀ j x, |f j x| ≤ 4 ^ k := by
    intro j x
    have := alg1Sample_norm_le k (by omega) j.1.1 j.1.2 (xA x) (xV x) (xB x) x.2
    simp only [f]; split_ifs
    · exact (Complex.abs_re_le_norm _).trans this
    · exact (Complex.abs_im_le_norm _).trans this
  have hH := Hoeff.finite_hoeffding_union (pw Φ) (pw_nonneg Φ hΦ) (pw_sum Φ hΦ) f (4 ^ k) (by positivity)
    hf M hM (ε / 2) (by positivity)
  have hcard : (Fintype.card (JQ n k × Bool) : ℝ) ≤ 2 * Kc k n := by
    rw [Fintype.card_prod, Fintype.card_bool]; push_cast
    have := card_JQ k hn (n := n); have : (Fintype.card (JQ n k) : ℝ) ≤ Kc k n := by exact_mod_cast this
    linarith
  have hexp : Real.exp (-(M * (ε / 2) ^ 2) / (16 * (4 ^ k) ^ 2)) = Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) := by
    congr 1
    rw [← pow_mul, show (4 : ℝ) ^ (k * 2) = 16 ^ k by rw [pow_mul']; norm_num]
    ring
  rw [hexp] at hH
  have hmean : ∀ j : JQ n k × Bool, ∑ x, pw Φ x * f j x =
      if j.2 then (locFourier Φ j.1.1).re else (locFourier Φ j.1.1).im := by
    intro j
    have hm := pw_mean Φ hΦ j.1.1
    simp only [f]
    split_ifs
    · rw [← hm, Complex.re_sum]; refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.re_ofReal_mul]
    · rw [← hm, Complex.im_sum]; refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.im_ofReal_mul]
  -- pointwise: good ≥ 1 - bad
  have hpt : ∀ ω : Fin M → Rd n,
      (1 : ℝ) - (if ∃ j, ε / 2 < |(∑ i, f j (ω i)) / M - ∑ x, pw Φ x * f j x| then 1 else 0) ≤
      (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
          then (1 : ℝ) else 0) := by
    intro ω
    by_cases hb : ∃ j, ε / 2 < |(∑ i, f j (ω i)) / M - ∑ x, pw Φ x * f j x|
    · rw [if_pos hb]; split_ifs <;> norm_num
    · rw [if_neg hb, if_pos]; · norm_num
      intro Q hQ
      push Not at hb
      have h1 := hb (⟨Q, hQ⟩, true)
      have h2 := hb (⟨Q, hQ⟩, false)
      rw [hmean] at h1 h2
      simp only [f, if_true, if_false, Bool.false_eq_true] at h1 h2
      have hre : (avg ω Q - locFourier Φ Q).re = (∑ i, (alg1Sample Q (xA (ω i)) (xV (ω i)) (xB (ω i)) (ω i).2).re) / M
          - (locFourier Φ Q).re := by
        simp only [avg, Complex.sub_re, Complex.mul_re, Complex.re_sum, Complex.im_sum]
        have : (1 / (M : ℂ)).re = 1 / M := by simp
        have h' : (1 / (M : ℂ)).im = 0 := by simp
        rw [this, h']; ring
      have him : (avg ω Q - locFourier Φ Q).im = (∑ i, (alg1Sample Q (xA (ω i)) (xV (ω i)) (xB (ω i)) (ω i).2).im) / M
          - (locFourier Φ Q).im := by
        simp only [avg, Complex.sub_im, Complex.mul_im, Complex.re_sum, Complex.im_sum]
        have : (1 / (M : ℂ)).re = 1 / M := by simp
        have h' : (1 / (M : ℂ)).im = 0 := by simp
        rw [this, h']; ring
      calc ‖avg ω Q - locFourier Φ Q‖ ≤ |(avg ω Q - locFourier Φ Q).re| + |(avg ω Q - locFourier Φ Q).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ ε / 2 + ε / 2 := by rw [hre, him]; exact add_le_add h1 h2
        _ = ε := by ring
  have hsum1 := Hoeff.prod_weight_sum (pw Φ) (pw_sum Φ hΦ) M
  calc 1 - 4 * Kc k n * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k))
      ≤ 1 - 2 * Fintype.card (JQ n k × Bool) * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) := by
        have := Real.exp_pos (-(M * ε ^ 2) / (64 * 16 ^ k)); nlinarith
    _ ≤ 1 - ∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
          (if ∃ j, ε / 2 < |(∑ i, f j (ω i)) / M - ∑ x, pw Φ x * f j x| then (1 : ℝ) else 0) := by linarith
    _ = ∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
          (1 - (if ∃ j, ε / 2 < |(∑ i, f j (ω i)) / M - ∑ x, pw Φ x * f j x| then (1 : ℝ) else 0)) := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum1]
    _ ≤ _ := Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hpt ω) (Hoeff.prod_weight_nonneg _ (pw_nonneg Φ hΦ) ω)

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
theorem solution : ∀ {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (hΦ : IsChannel Φ) (k : ℕ) (hn : 1 ≤ n) (M : ℕ)
    (hM : 0 < M) (ε : ℝ) (hε : 0 < ε),
    1 - 4 * Kc k n * Real.exp (-(M * ε ^ 2) / (64 * 16 ^ k)) ≤
      ∑ ω : Fin M → Rd n, (∏ i, pw Φ (ω i)) *
        (if ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k → ‖avg ω Q - locFourier Φ Q‖ ≤ ε
          then (1 : ℝ) else 0) :=
  @LindbladStructLearn.Mach.A1.prob_good
