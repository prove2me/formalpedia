-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.S3_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:28.483939+00:00
-- url     : https://prove2.me/submissions/fdfecd98-6a03-4e74-8f0a-0af98a52cd24

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_core3_exec

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

lemma rad_pos (k n : ℕ) (hn : 1 ≤ n) (i : ℕ) : 0 < rad k n i := by
  unfold rad; split_ifs <;> omega

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

lemma Dseq_succ (k n j : ℕ) : Dseq k n (j + 1) = succD k n (Dseq k n j) :=
  Function.iterate_succ_apply' _ _ _

theorem Dseq_inRange (k n : ℕ) (hn : 1 ≤ n) (j : ℕ) : InRange k n (Dseq k n j) := by
  unfold InRange
  induction j with
  | zero => intro i _; simpa [Dseq] using rad_pos k n hn i
  | succ j ih =>
      rw [Dseq_succ, succD]
      exact incAt_inRange k n hn _ _ ih

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

lemma contrib_eq (k n : ℕ) (D : ℕ → ℕ) (hD : InRange k n D) (hv : validD k D) (A : Pauli n)
    (v : Qubits n) (B : Pauli n) (w : Qubits n) :
    contrib (D 0) (fun r => L1 k D r) (fun r => L2 k D r) (fun r => atP A (D (1 + r)))
      (fun r => atP B (D (1 + r))) (fun r => atB v (D (1 + r))) (fun r => atB w (D (1 + r))) =
      alg1Sample (pairOf n k D) A v B w := by
  obtain ⟨σ, hσ, he⟩ := alg1Sample_code hD hv A v B w
  rw [he]
  have hs := s_le hD
  have key : ∀ r : Fin (D 0), ∃ h : D (1 + r) < n, (⟨D (1 + r), h⟩ : Fin n) = σ r := by
    intro r
    exact ⟨site_lt hD r (by omega), Fin.ext (hσ r).symm⟩
  have hA : ∀ r : Fin (D 0), atP A (D (1 + r)) = A (σ r) := by
    intro r; obtain ⟨h, e⟩ := key r; simp [atP, h, e]
  have hB : ∀ r : Fin (D 0), atP B (D (1 + r)) = B (σ r) := by
    intro r; obtain ⟨h, e⟩ := key r; simp [atP, h, e]
  have hvv : ∀ r : Fin (D 0), atB v (D (1 + r)) = v (σ r) := by
    intro r; obtain ⟨h, e⟩ := key r; simp [atB, h, e]
  have hw : ∀ r : Fin (D 0), atB w (D (1 + r)) = w (σ r) := by
    intro r; obtain ⟨h, e⟩ := key r; simp [atB, h, e]
  unfold contrib
  have hc : (∀ r < D 0, atP B (D (1 + r)) = letterMul (letterMul (L2 k D r) (atP A (D (1 + r)))) (L1 k D r)) ↔
      ∀ r : Fin (D 0), B (σ r) = letterMul (letterMul (L2 k D r) (A (σ r))) (L1 k D r) := by
    constructor
    · intro h r; rw [← hA, ← hB]; exact h r r.isLt
    · intro h r hr; have := h ⟨r, hr⟩; rw [hA ⟨r, hr⟩, hB ⟨r, hr⟩]; exact this
  have hsum : ∑ r ∈ Finset.range (D 0), siteExp (L1 k D r) (L2 k D r) (atP A (D (1 + r))) (atP B (D (1 + r)))
      (atB v (D (1 + r))) (atB w (D (1 + r))) =
      ∑ r : Fin (D 0), (phexp (L2 k D r) (A (σ r)) + phexp (letterMul (L2 k D r) (A (σ r))) (L1 k D r) +
        (if A (σ r) ≠ 0 ∧ v (σ r) = true then 2 else 0) +
        (if B (σ r) ≠ 0 ∧ w (σ r) = true then 2 else 0)) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold siteExp
    rw [hA r, hB r, hvv r, hw r]
  by_cases h : ∀ r : Fin (D 0), B (σ r) = letterMul (letterMul (L2 k D r) (A (σ r))) (L1 k D r)
  · rw [if_pos (hc.mpr h), if_pos h, hsum]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma cA_eq (c : C5) : cA c = ((letA c : ℕ) : ℤ) := by
  obtain ⟨h1, h2⟩ := cA_range c; simp only [letA]; omega
lemma cB_eq (c : C5) : cB c = ((letB c : ℕ) : ℤ) := by
  obtain ⟨h1, h2⟩ := cB_range c; simp only [letB]; omega
lemma cV_eq (c : C5) : cV c = if bitV c then 1 else 0 := by
  rcases cV_range c with h | h <;> simp [bitV, h]

lemma body3_valid (t : MState) (k n M : ℕ) (hn : 1 ≤ n) (smp : Fin M → Rd n) (p : ℤ) (j : ℕ)
    (hvj : validD k (Dseq k n j))
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h1 : t.core.ptrs 1 = M)
    (h13 : t.core.ptrs 13 = recAddr k p j) (hr4 : t.core.regs 4 = 4) (htab : Tab t.intMem)
    (h20 : t.core.ptrs 20 = Dseq k n j 0)
    (hrecm : ∀ i ≤ 3 * k, t.intMem (recAddr k p j + i) = recCell k n j i)
    (hsm : SampMem k n M smp t.intMem) :
    let b := recAddr k p j
    ∃ t' m, Exec (core3 k) t t' m ∧ m ≤ M * (70 * k + 32) + 4 * k + 20 ∧
      t'.output = t.output ∧ t'.durations = t.durations ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → t'.core.regs q = t.core.regs q) ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 7 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.mem = Function.update (Function.update t.core.mem (b + (3 * k + 1))
        ((∑ i : Fin M, alg1Sample (pairOf n k (Dseq k n j)) (sA smp i) (sV smp i) (sB smp i)
          (sW smp i)).re * t.core.regs 6)) (b + (3 * k + 1) + 1)
        ((∑ i : Fin M, alg1Sample (pairOf n k (Dseq k n j)) (sA smp i) (sV smp i) (sB smp i)
          (sW smp i)).im * t.core.regs 6) := by
  intro b
  set D := Dseq k n j with hDdef
  have hD : InRange k n D := Dseq_inRange k n hn j
  have hs := s_le hD
  have hrec0 : ∀ i, 1 ≤ i → i ≤ 3 * k → t.intMem (recAddr k p j + i) = D i := by
    intro i h1 h2; rw [hrecm i h2]; unfold recCell; rw [if_neg (by omega)]
  let Af : ℕ → ℕ → Fin 4 := fun i r => if h : i < M then atP (sA smp ⟨i, h⟩) (D (1 + r)) else 0
  let Bf : ℕ → ℕ → Fin 4 := fun i r => if h : i < M then atP (sB smp ⟨i, h⟩) (D (1 + r)) else 0
  let Vf : ℕ → ℕ → Bool := fun i r => if h : i < M then atB (sV smp ⟨i, h⟩) (D (1 + r)) else false
  let Wf : ℕ → ℕ → Bool := fun i r => if h : i < M then atB (sW smp ⟨i, h⟩) (D (1 + r)) else false
  have hrec : ∀ r < D 0, t.intMem (t.core.ptrs 13 + r + 1) = (D (1 + r) : ℤ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = ((L1 k D r : ℕ) : ℤ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = ((L2 k D r : ℕ) : ℤ) := by
    intro r hr
    rw [h13, L1_val hD r (by omega), L2_val hD r (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hrec0 (1 + r) (by omega) (by omega)]; congr 1; push_cast; ring
    · rw [← hrec0 (1 + k + r) (by omega) (by omega)]; congr 1; push_cast; ring
    · rw [← hrec0 (1 + 2 * k + r) (by omega) (by omega)]; congr 1; push_cast; ring
  have hsm' : ∀ i < M, ∀ r < D 0, t.intMem (cSAMP k + 4 * n * i + (D (1 + r) : ℕ)) = (Af i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + (D (1 + r) : ℕ) + n) = (if Vf i r then 1 else 0) ∧
      t.intMem (cSAMP k + 4 * n * i + (D (1 + r) : ℕ) + n + n) = (Bf i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + (D (1 + r) : ℕ) + n + n + n) = (if Wf i r then 1 else 0) := by
    intro i hi r hr
    have hx : D (1 + r) < n := site_lt hD r (by omega)
    obtain ⟨e1, e2, e3, e4⟩ := hsm ⟨i, hi⟩ ⟨D (1 + r), hx⟩
    simp only [Af, Bf, Vf, Wf, dif_pos hi, atP, atB, dif_pos hx, sA, sB, sV, sW]
    simp only [Fin.val_mk] at e1 e2 e3 e4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, cA_eq]
    · rw [show cSAMP k + 4 * n * i + (D (1 + r) : ℤ) + n = cSAMP k + 4 * n * i + (n + D (1 + r)) by ring, e2,
        cV_eq]
    · rw [show cSAMP k + 4 * n * i + (D (1 + r) : ℤ) + n + n = cSAMP k + 4 * n * i + (2 * n + D (1 + r)) by
        ring, e3, cB_eq]
    · rw [show cSAMP k + 4 * n * i + (D (1 + r) : ℤ) + n + n + n = cSAMP k + 4 * n * i + (3 * n + D (1 + r))
        by ring, e4]
  obtain ⟨t', m, ex, hm, o1, o2, o3, o4, o5, o6⟩ := core3_exec t k n (D 0) M (fun r => D (1 + r))
    (fun r => L1 k D r) (fun r => L2 k D r) Af Bf Vf Wf h10 h11 h45 h43 h47 h46 h0 h2 h20 h1 hr4 htab
    hrec hsm'
  have htot : ∑ i ∈ Finset.range M, contrib (D 0) (fun r => L1 k D r) (fun r => L2 k D r) (Af i) (Bf i)
      (Vf i) (Wf i) = ∑ i : Fin M, alg1Sample (pairOf n k D) (sA smp i) (sV smp i) (sB smp i) (sW smp i) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← contrib_eq k n D hD hvj]
    simp only [Af, Bf, Vf, Wf, dif_pos i.isLt]
  rw [htot] at o6
  refine ⟨t', m, ex, ?_, o1, o2, o3, o4, o5, ?_⟩
  · have : M * (70 * D 0 + 32) ≤ M * (70 * k + 32) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [o6, h13]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

open Classical in
lemma body3_exec (t : MState) (k n M : ℕ) (hn : 1 ≤ n) (smp : Fin M → Rd n) (p : ℤ) (j : ℕ)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h1 : t.core.ptrs 1 = M)
    (h18 : t.core.ptrs 18 = 3 * k + 3)
    (h13 : t.core.ptrs 13 = recAddr k p j) (hr4 : t.core.regs 4 = 4) (htab : Tab t.intMem)
    (hrecm : ∀ i ≤ 3 * k, t.intMem (recAddr k p j + i) = recCell k n j i)
    (hsm : SampMem k n M smp t.intMem) :
    let b := recAddr k p j
    ∃ t' m, Exec (body3 k) t t' m ∧ m ≤ M * (70 * k + 32) + 4 * k + 30 ∧
      t'.output = t.output ∧ t'.durations = t.durations ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → t'.core.regs q = t.core.regs q) ∧
      (∀ q, q ∉ scr3 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.ptrs 13 = recAddr k p (j + 1) ∧ t'.core.ptrs 32 = t.core.ptrs 32 + 1 ∧
      t'.core.mem = if validD k (Dseq k n j) then
        Function.update (Function.update t.core.mem (b + (3 * k + 1))
          ((tsum k n M smp j).re * t.core.regs 6)) (b + (3 * k + 1) + 1)
          ((tsum k n M smp j).im * t.core.regs 6) else t.core.mem := by
  intro b
  let u := ains (.integerLoad 20 13) t
  have u20 : u.core.ptrs 20 = recCell k n j 0 := by
    simp only [u, ains, Function.update_self, h13]
    have := hrecm 0 (by omega); simpa using this
  have up : ∀ q, q ≠ 20 → u.core.ptrs q = t.core.ptrs q := by
    intro q hq; simp [u, ains, Function.update_of_ne hq]
  have hD : InRange k n (Dseq k n j) := Dseq_inRange k n hn j
  by_cases hv : validD k (Dseq k n j)
  · have hc : (tick u).core.ptrs 20 ≤ (tick u).core.ptrs 46 := by
      simp only [tick_core]; rw [u20, up 46 (by norm_num), h46]; unfold recCell; rw [if_pos rfl, if_pos hv]
      exact_mod_cast s_le hD
    obtain ⟨t', m, ex, hm, o1, o2, o3, o4, o5, o6⟩ := body3_valid (tick u) k n M hn smp p j hv
      (by simp only [tick_core]; rw [up 10 (by norm_num), h10])
      (by simp only [tick_core]; rw [up 11 (by norm_num), h11])
      (by simp only [tick_core]; rw [up 45 (by norm_num), h45])
      (by simp only [tick_core]; rw [up 43 (by norm_num), h43])
      (by simp only [tick_core]; rw [up 47 (by norm_num), h47])
      (by simp only [tick_core]; rw [up 46 (by norm_num), h46])
      (by simp only [tick_core]; rw [up 0 (by norm_num), h0])
      (by simp only [tick_core]; rw [up 2 (by norm_num), h2])
      (by simp only [tick_core]; rw [up 1 (by norm_num), h1])
      (by simp only [tick_core]; rw [up 13 (by norm_num), h13])
      (by simp only [tick_core]; simp [u, ains, hr4]) (by simp only [tick_intMem]; exact htab)
      (by simp only [tick_core]; rw [u20]; unfold recCell; simp [hv])
      (by simp only [tick_intMem]; exact hrecm) (by simp only [tick_intMem]; exact hsm)
    have ex' : Exec (body3 k) t (ains (.core (.pinc 32)) (ains (.pointerAdd 13 13 18) t'))
        (1 + ((m + 1) + (1 + 1))) := by
      unfold body3; simp only [seqs]
      exact Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.iteT hc ex)
        (Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial)))
    refine ⟨_, _, ex', by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ains]; rw [o1]; rfl
    · simp only [ains]; rw [o2]; rfl
    · simp only [ains]; rw [o3]; rfl
    · intro q hq; simp only [ains]; rw [o4 q hq]; rfl
    · intro q hq
      have hq' := hq
      simp only [scr3, Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
      have hs : q ∉ scrS := by simp [scrS]; omega
      simp only [ains, Function.update_of_ne hq'.2.2.2.2.2.1, Function.update_of_ne hq'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
      rw [o5 q hs hq'.1 hq'.2.2.1 hq'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
      simp only [tick_core]; exact up q hq'.2.2.2.2.2.2.2.1
    · simp only [ains, Function.update_of_ne (show (13 : ℕ) ≠ 32 by norm_num), Function.update_self]
      rw [o5 13 (by simp [scrS]) (by norm_num) (by norm_num) (by norm_num),
        o5 18 (by simp [scrS]) (by norm_num) (by norm_num) (by norm_num)]
      simp only [tick_core]; rw [up 13 (by norm_num), up 18 (by norm_num), h13, h18]
      unfold recAddr; push_cast; ring
    · simp only [ains, Function.update_self]
      rw [Function.update_of_ne (by norm_num), o5 32 (by simp [scrS]) (by norm_num) (by norm_num)
        (by norm_num)]
      simp only [tick_core]; rw [up 32 (by norm_num)]
    · simp only [ains]; rw [o6, if_pos hv]; simp only [tick_core]; rfl
  · have hc : ¬ (tick u).core.ptrs 20 ≤ (tick u).core.ptrs 46 := by
      simp only [tick_core]; rw [u20, up 46 (by norm_num), h46]; unfold recCell; rw [if_pos rfl, if_neg hv]
      omega
    have ex' : Exec (body3 k) t (ains (.core (.pinc 32)) (ains (.pointerAdd 13 13 18)
        (tick (ains (.core (.pcopy 0 0)) (tick u))))) (1 + ((1 + 2) + (1 + 1))) := by
      unfold body3; simp only [seqs]
      exact Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.iteF hc (Exec.ins (.core (.pcopy 0 0)) _ trivial))
        (Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial)))
    refine ⟨_, _, ex', by omega, rfl, rfl, rfl, fun q _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have hq' := hq
      simp only [scr3, Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
      simp only [ains, tick, Function.update_apply]
      split_ifs <;> simp_all [up]
    · simp only [ains, tick, Function.update_apply]
      simp [up 13 (by norm_num), up 18 (by norm_num), h13, h18]
      unfold recAddr; push_cast; ring
    · simp [ains, tick, Function.update_apply, up 32 (by norm_num)]
    · simp only [ains, tick]; rw [if_neg hv]; rfl

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma recAddr_mono (k : ℕ) (p : ℤ) {j j' : ℕ} (h : j' < j) :
    recAddr k p j' + (3 * k + 1) + 1 < recAddr k p j + (3 * k + 1) := by
  unfold recAddr
  have : ((j' : ℤ) + 1) * (3 * k + 3) ≤ j * (3 * k + 3) := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)
  linarith

lemma S3_exec (s : MState) (k n M : ℕ) (hn : 1 ≤ n) (smp : Fin M → Rd n) (p : ℤ)
    (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1) (h45 : s.core.ptrs 45 = 2)
    (h43 : s.core.ptrs 43 = 3) (h47 : s.core.ptrs 47 = 4) (h46 : s.core.ptrs 46 = k)
    (h0 : s.core.ptrs 0 = n) (h2 : s.core.ptrs 2 = 4 * n) (h1 : s.core.ptrs 1 = M)
    (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p) (h14 : s.core.ptrs 14 = Kc k n)
    (hr4 : s.core.regs 4 = 4) (htab : Tab s.intMem)
    (hrecm : ∀ j < Kc k n, ∀ i ≤ 3 * k, s.intMem (recAddr k p j + i) = recCell k n j i)
    (hsm : SampMem k n M smp s.intMem) :
    ∃ s' m, Exec (S3 k) s s' m ∧ m ≤ Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3 ∧
      s'.output = s.output ∧ s'.durations = s.durations ∧ s'.intMem = s.intMem ∧
      s'.core.ptrs 12 = p ∧
      ∀ j < Kc k n, validD k (Dseq k n j) →
        s'.core.mem (recAddr k p j + (3 * k + 1)) = (tsum k n M smp j).re * s.core.regs 6 ∧
        s'.core.mem (recAddr k p j + (3 * k + 1) + 1) = (tsum k n M smp j).im * s.core.regs 6 := by
  let t2 := ains (.core (.pset 32 0)) (ains (.pointerAdd 13 12 11) s)
  have tp : ∀ q, q ≠ 13 → q ≠ 32 → t2.core.ptrs q = s.core.ptrs q := by
    intro q a b; simp [t2, ains, Function.update_of_ne a, Function.update_of_ne b]
  let K := Kc k n
  let Inv : ℕ → MState → Prop := fun j u => u.core.ptrs 32 = j ∧ u.core.ptrs 13 = recAddr k p j ∧
    u.output = s.output ∧ u.durations = s.durations ∧ u.intMem = s.intMem ∧
    (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → u.core.regs q = s.core.regs q) ∧
    (∀ q, q ∉ scr3 → u.core.ptrs q = s.core.ptrs q) ∧
    ∀ j' < j, validD k (Dseq k n j') →
      u.core.mem (recAddr k p j' + (3 * k + 1)) = (tsum k n M smp j').re * s.core.regs 6 ∧
      u.core.mem (recAddr k p j' + (3 * k + 1) + 1) = (tsum k n M smp j').im * s.core.regs 6
  have hstep : ∀ j < K, ∀ u, Inv j u → ¬ u.core.ptrs 14 ≤ u.core.ptrs 32 ∧
      ∃ s1 m, Exec (body3 k) (tick u) s1 m ∧ m ≤ M * (70 * k + 32) + 4 * k + 30 ∧
        Inv (j + 1) (tick s1) := by
    intro j hj u ⟨i32, i13, iout, idur, imem, ireg, iptr, ival⟩
    have e : ∀ q, q ∉ scr3 → (tick u).core.ptrs q = s.core.ptrs q := iptr
    obtain ⟨t', m, ex, hm, o1, o2, o3, o4, o5, o13, o32, o6⟩ := body3_exec (tick u) k n M hn smp p j
      (by rw [e 10 (by simp [scr3]), h10]) (by rw [e 11 (by simp [scr3]), h11])
      (by rw [e 45 (by simp [scr3]), h45]) (by rw [e 43 (by simp [scr3]), h43])
      (by rw [e 47 (by simp [scr3]), h47]) (by rw [e 46 (by simp [scr3]), h46])
      (by rw [e 0 (by simp [scr3]), h0]) (by rw [e 2 (by simp [scr3]), h2])
      (by rw [e 1 (by simp [scr3]), h1]) (by rw [e 18 (by simp [scr3]), h18])
      (by simp only [tick_core]; exact i13)
      (by simp only [tick_core]; rw [ireg 4 (by simp), hr4])
      (by simp only [tick_intMem]; rw [imem]; exact htab)
      (by simp only [tick_intMem]; rw [imem]; exact hrecm j hj)
      (by simp only [tick_intMem]; rw [imem]; exact hsm)
    have u6 : (tick u).core.regs 6 = s.core.regs 6 := by simp only [tick_core]; exact ireg 6 (by simp)
    have u14 : u.core.ptrs 14 = K := by rw [iptr 14 (by simp [scr3]), h14]
    refine ⟨by rw [u14, i32]; push_cast; omega, t', m, ex, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tick_core]; rw [o32]; simp only [tick_core, i32]; push_cast; ring
    · simp only [tick_core]; exact o13
    · simp only [tick]; rw [o1]; exact iout
    · simp only [tick]; rw [o2]; exact idur
    · simp only [tick]; rw [o3]; exact imem
    · intro q hq; simp only [tick_core]; rw [o4 q hq]; simp only [tick_core]; exact ireg q hq
    · intro q hq; simp only [tick_core]; rw [o5 q hq]; exact e q hq
    · intro j' hj' hv'
      simp only [tick_core]
      rw [o6]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
      · have hlt := recAddr_mono k p h
        obtain ⟨v1, v2⟩ := ival j' h hv'
        split_ifs
        · simp only [tick_core]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact ⟨v1, v2⟩
        · exact ⟨v1, v2⟩
      · subst h
        rw [if_pos hv']
        simp only [tick_core, u6]
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by omega), Function.update_self, ireg 6 (by simp)]
        · rw [Function.update_self, ireg 6 (by simp)]
  have hend : ∀ u, Inv K u → u.core.ptrs 14 ≤ u.core.ptrs 32 := by
    rintro u ⟨i32, -, -, -, -, -, iptr, -⟩
    rw [iptr 14 (by simp [scr3]), h14, i32]
  obtain ⟨sT, m, ⟨i32, i13, iout, idur, imem, ireg, iptr, ival⟩, hex, hm⟩ :=
    loop_rule Inv K (M * (70 * k + 32) + 4 * k + 30) hstep hend t2
      ⟨by simp [t2, ains], by simp [t2, ains, h12, h11, recAddr], rfl, rfl, rfl, fun q _ => rfl,
        fun q hq => tp q (by intro h; subst h; simp [scr3] at hq) (by intro h; subst h; simp [scr3] at hq),
        fun j' hj' => absurd hj' (by omega)⟩
  have ex : Exec (S3 k) s (tick sT) (1 + (1 + m)) := by
    unfold S3; simp only [seqs]
    exact Exec.seq (Exec.ins _ s trivial) (Exec.seq (Exec.ins _ _ trivial) hex)
  refine ⟨tick sT, _, ex, by linarith, iout, idur, imem, ?_, fun j hj hv => ival j hj hv⟩
  simp only [tick_core]; rw [iptr 12 (by simp [scr3]), h12]

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
theorem solution : ∀ (s : MState) (k n M : ℕ) (hn : 1 ≤ n) (smp : Fin M → Rd n) (p : ℤ)
    (h10 : s.core.ptrs 10 = 0) (h11 : s.core.ptrs 11 = 1) (h45 : s.core.ptrs 45 = 2)
    (h43 : s.core.ptrs 43 = 3) (h47 : s.core.ptrs 47 = 4) (h46 : s.core.ptrs 46 = k)
    (h0 : s.core.ptrs 0 = n) (h2 : s.core.ptrs 2 = 4 * n) (h1 : s.core.ptrs 1 = M)
    (h18 : s.core.ptrs 18 = 3 * k + 3) (h12 : s.core.ptrs 12 = p) (h14 : s.core.ptrs 14 = Kc k n)
    (hr4 : s.core.regs 4 = 4) (htab : Tab s.intMem)
    (hrecm : ∀ j < Kc k n, ∀ i ≤ 3 * k, s.intMem (recAddr k p j + i) = recCell k n j i)
    (hsm : SampMem k n M smp s.intMem),
    ∃ s' m, Exec (S3 k) s s' m ∧ m ≤ Kc k n * (M * (70 * k + 32) + 4 * k + 32) + 3 ∧
      s'.output = s.output ∧ s'.durations = s.durations ∧ s'.intMem = s.intMem ∧
      s'.core.ptrs 12 = p ∧
      ∀ j < Kc k n, validD k (Dseq k n j) →
        s'.core.mem (recAddr k p j + (3 * k + 1)) = (tsum k n M smp j).re * s.core.regs 6 ∧
        s'.core.mem (recAddr k p j + (3 * k + 1) + 1) = (tsum k n M smp j).im * s.core.regs 6 :=
  @LindbladStructLearn.Mach.A1.S3_exec
