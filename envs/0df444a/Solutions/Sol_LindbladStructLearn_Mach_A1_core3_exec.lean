-- Prove2me | solution 1 for LindbladStructLearn.Mach.A1.core3_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:45:39.709348+00:00
-- url     : https://prove2.me/submissions/55a6eb41-c85f-4b0e-a142-502527d4317b

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
import Theorems.Thm_LindbladStructLearn_Mach_A1_site_loop

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

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma phexp_le (a b : Fin 4) : phexp a b ≤ 3 := by
  unfold phexp; split_ifs <;> norm_num

lemma siteExp_le (L1 L2 A B : Fin 4) (V W : Bool) : siteExp L1 L2 A B V W ≤ 10 := by
  unfold siteExp
  have := phexp_le L2 A; have := phexp_le (letterMul L2 A) L1
  split_ifs <;> omega

lemma mod_loop (t : MState) (e : ℕ) (h31 : t.core.ptrs 31 = e) (h43 : t.core.ptrs 43 = 3)
    (h47 : t.core.ptrs 47 = 4) :
    ∃ t' m, Exec (.loop 31 43 (psub 31 31 47)) t t' m ∧ m ≤ e + 1 ∧ Same t t' ∧ t'.intMem = t.intMem ∧
      (∀ q, q ≠ 31 → t'.core.ptrs q = t.core.ptrs q) ∧ t'.core.ptrs 31 = (e % 4 : ℕ) := by
  let Inv : ℕ → MState → Prop := fun j u => Same t u ∧ u.intMem = t.intMem ∧
    (∀ q, q ≠ 31 → u.core.ptrs q = t.core.ptrs q) ∧ u.core.ptrs 31 = (e : ℤ) - 4 * j
  have hstep : ∀ j < e / 4, ∀ u, Inv j u → ¬ u.core.ptrs 31 ≤ u.core.ptrs 43 ∧
      ∃ s1 m, Exec (psub 31 31 47) (tick u) s1 m ∧ m ≤ 1 ∧ Inv (j + 1) (tick s1) := by
    intro j hj u ⟨isame, imem, iptr, i31⟩
    refine ⟨by rw [i31, iptr 43 (by norm_num), h43]; omega, _, _, Exec.ins _ _ trivial, le_rfl, ?_⟩
    refine ⟨isame.trans ⟨rfl, rfl, rfl, rfl⟩, imem, ?_, ?_⟩
    · intro q hq; simp [ains, Function.update_of_ne hq, iptr q hq]
    · simp [ains, i31, iptr 47 (by norm_num), h47]; push_cast; ring
  have hend : ∀ u, Inv (e / 4) u → u.core.ptrs 31 ≤ u.core.ptrs 43 := by
    rintro u ⟨-, -, iptr, i31⟩
    rw [i31, iptr 43 (by norm_num), h43]; omega
  obtain ⟨sT, m, ⟨isame, imem, iptr, i31⟩, hex, hm⟩ := loop_rule Inv (e / 4) 1 hstep hend t
    ⟨Same.refl t, rfl, fun q _ => rfl, by simp [h31]⟩
  refine ⟨tick sT, m, hex, by omega, isame.tick, imem, iptr, ?_⟩
  simp only [tick_core, i31]; omega

lemma caseE_fin (u : MState) (h10 : u.core.ptrs 10 = 0) (h11 : u.core.ptrs 11 = 1)
    (h45 : u.core.ptrs 45 = 2) (e : ℕ) (h31 : u.core.ptrs 31 = (e % 4 : ℕ)) :
    let v := caseE.fin u
    RegFix u v {1, 2} ∧ v.intMem = u.intMem ∧ v.core.ptrs = u.core.ptrs ∧ v.work ≤ u.work + 8 ∧
    u.work ≤ v.work ∧
    v.core.regs 1 = u.core.regs 1 + ((u.core.regs 3 : ℂ) * Complex.I ^ e).re ∧
    v.core.regs 2 = u.core.regs 2 + ((u.core.regs 3 : ℂ) * Complex.I ^ e).im := by
  intro v
  have hI : Complex.I ^ e = Complex.I ^ (e % 4) := by
    conv_lhs => rw [← Nat.div_add_mod e 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hI]
  have hlt : e % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize e % 4 = r at h31 hlt ⊢
  have hv : v = caseE.fin u := rfl
  interval_cases r
  all_goals
    simp only [hv, caseE, Stmt.fin, tick_core, h10, h11, h45, h31]
    norm_num
    refine ⟨⟨rfl, rfl, rfl, fun q hq => ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  all_goals simp_all [ains, tick, radd, rsub, Stmt.fin, Function.update_apply, Complex.I_sq, pow_three]
  all_goals first | omega | ring | skip

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma caseE_noLoop : caseE.NoLoop := by
  simp [caseE, Stmt.NoLoop, radd, rsub, Plain]

lemma sum_siteExp_le (S : ℕ) (f : ℕ → ℕ) (hf : ∀ r, f r ≤ 10) : ∑ r ∈ Finset.range S, f r ≤ 10 * S := by
  calc ∑ r ∈ Finset.range S, f r ≤ ∑ _r ∈ Finset.range S, 10 := Finset.sum_le_sum fun r _ => hf r
    _ = 10 * S := by simp [mul_comm]

open Classical in
lemma sampBody_exec (t : MState) (k n S : ℕ) (xs : ℕ → ℕ) (L1f L2f Af Bf : ℕ → Fin 4) (Vf Wf : ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h20 : t.core.ptrs 20 = S)
    (htab : Tab t.intMem)
    (hm : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r) = (Af r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n) = (if Vf r then 1 else 0) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n) = (Bf r : ℕ) ∧
      t.intMem (t.core.ptrs 4 + xs r + n + n + n) = (if Wf r then 1 else 0)) :
    let c : ℂ := if ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r) then
      (t.core.regs 3 : ℂ) * Complex.I ^ (∑ r ∈ Finset.range S,
        siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r)) else 0
    ∃ t' m, Exec sampBody t t' m ∧ m ≤ 70 * S + 30 ∧ RegFix t t' {1, 2} ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.ptrs 4 = t.core.ptrs 4 + 4 * n ∧ t'.core.ptrs 34 = t.core.ptrs 34 + 1 ∧
      t'.core.regs 1 = t.core.regs 1 + c.re ∧ t'.core.regs 2 = t.core.regs 2 + c.im := by
  intro c
  let t3 := ains (.core (.pset 19 0)) (ains (.core (.pset 31 0)) (ains (.core (.pset 30 1)) t))
  have e3 : ∀ q, q ≠ 19 → q ≠ 30 → q ≠ 31 → t3.core.ptrs q = t.core.ptrs q := by
    intro q a b c'; simp [t3, ains, Function.update_of_ne a, Function.update_of_ne b, Function.update_of_ne c']
  have r3 : ∀ q, q ∉ scrS → t3.core.ptrs q = t.core.ptrs q := by
    intro q hq; exact e3 q (by intro h; subst h; simp [scrS] at hq) (by intro h; subst h; simp [scrS] at hq)
      (by intro h; subst h; simp [scrS] at hq)
  obtain ⟨u, mu, eu, hmu, usame, umem, uptr, u30, u31⟩ := site_loop t3 k n S xs L1f L2f Af Bf Vf Wf
    (by rw [r3 10 (by simp [scrS]), h10]) (by rw [r3 46 (by simp [scrS]), h46])
    (by rw [r3 0 (by simp [scrS]), h0]) (by simp [t3, ains]) (by rw [r3 20 (by simp [scrS]), h20])
    htab (by rw [show t3.core.ptrs 13 = t.core.ptrs 13 from r3 13 (by simp [scrS]),
      show t3.core.ptrs 4 = t.core.ptrs 4 from r3 4 (by simp [scrS])]; exact hm)
  have t30 : t3.core.ptrs 30 = 1 := by simp [t3, ains]
  have t31 : t3.core.ptrs 31 = 0 := by simp [t3, ains]
  rw [t30] at u30; rw [t31, zero_add] at u31
  set E := ∑ r ∈ Finset.range S, siteExp (L1f r) (L2f r) (Af r) (Bf r) (Vf r) (Wf r) with hE
  have hEle : E ≤ 10 * S := sum_siteExp_le S _ (fun r => siteExp_le _ _ _ _ _ _)
  have u10 : u.core.ptrs 10 = 0 := by rw [uptr 10 (by simp [scrS]), r3 10 (by simp [scrS]), h10]
  have ufix : ∀ q, q ∉ scrS → u.core.ptrs q = t.core.ptrs q := fun q hq => (uptr q hq).trans (r3 q hq)
  -- the conditional accumulation
  by_cases hc : ∀ r < S, Bf r = letterMul (letterMul (L2f r) (Af r)) (L1f r)
  · rw [if_pos hc] at u30
    obtain ⟨w, mw, ew, hmw, wsame, wmem, wptr, w31⟩ := mod_loop (tick u) E (by simp [u31])
      (by simp only [tick_core]; rw [ufix 43 (by simp [scrS]), h43])
      (by simp only [tick_core]; rw [ufix 47 (by simp [scrS]), h47])
    have w10 : w.core.ptrs 10 = 0 := by rw [wptr 10 (by norm_num)]; exact u10
    obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := caseE_fin w w10
      (by rw [wptr 11 (by norm_num)]; simp only [tick_core]; rw [ufix 11 (by simp [scrS]), h11])
      (by rw [wptr 45 (by norm_num)]; simp only [tick_core]; rw [ufix 45 (by simp [scrS]), h45]) E w31
    have ecase := caseE.exec_fin caseE_noLoop w
    have hcw := ecase.work
    have ex : Exec sampBody t (ains (.core (.pinc 34)) (ains (.pointerAdd 4 4 2) (tick (caseE.fin w))))
        (1 + (1 + (1 + (mu + ((mw + caseE.steps w) + 2 + (1 + 1)))))) := by
      unfold sampBody; simp only [seqs]
      exact Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial)
        (Exec.seq eu (Exec.seq (Exec.iteF (x := 30) (y := 10) (by simp [tick_core, u30, u10]) (Exec.seq ew ecase))
          (Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial))))))
    have wreg : ∀ q, w.core.regs q = t.core.regs q := by
      intro q; rw [show w.core.regs = (tick u).core.regs from wsame.2.2.1]
      simp only [tick_core]; rw [usame.2.2.1]; simp [t3, ains]
    refine ⟨_, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
      · simp only [ains, tick]; rw [x1.1, wsame.1]; simp only [tick]; rw [usame.1]; rfl
      · simp only [ains, tick]; rw [x1.2.1, wsame.2.1]; simp only [tick]; rw [usame.2.1]; rfl
      · simp only [ains, tick]; rw [x1.2.2.1, wsame.2.2.2]; simp only [tick]; rw [usame.2.2.2]; rfl
      · simp only [ains, tick]; rw [x1.2.2.2 q hq, wreg]
    · simp only [ains, tick]; rw [x2, wmem]; simp only [tick_intMem]; rw [umem]; rfl
    · intro q hq h4 h34
      have h31 : q ≠ 31 := by intro h; subst h; simp [scrS] at hq
      simp only [ains, tick, Function.update_of_ne h4, Function.update_of_ne h34, x3]
      rw [wptr q h31]; simp only [tick_core]; exact ufix q hq
    · simp only [ains, tick, Function.update_of_ne (show (4 : ℕ) ≠ 34 by norm_num), Function.update_self, x3]
      rw [wptr 4 (by norm_num), wptr 2 (by norm_num)]; simp only [tick_core]
      rw [ufix 4 (by simp [scrS]), ufix 2 (by simp [scrS]), h2]
    · simp only [ains, tick, Function.update_self, x3]
      rw [Function.update_apply, if_neg (by norm_num), wptr 34 (by norm_num)]; simp only [tick_core]
      rw [ufix 34 (by simp [scrS])]
    · simp only [ains, tick]; rw [x6, wreg, wreg 3]
      simp only [c, if_pos hc]; rfl
    · simp only [ains, tick]; rw [x7, wreg, wreg 3]
      simp only [c, if_pos hc]; rfl
  · rw [if_neg hc] at u30
    have ex : Exec sampBody t (ains (.core (.pinc 34)) (ains (.pointerAdd 4 4 2)
        (ains (.core (.pcopy 0 0)) (tick u)))) (1 + (1 + (1 + (mu + ((1 + 1) + (1 + 1)))))) := by
      unfold sampBody; simp only [seqs]
      exact Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial)
        (Exec.seq eu (Exec.seq (Exec.iteT (x := 30) (y := 10) (by simp [tick_core, u30, u10]) (Exec.ins (.core (.pcopy 0 0)) _ trivial))
          (Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial))))))
    have ureg : ∀ q, u.core.regs q = t.core.regs q := by
      intro q; rw [usame.2.2.1]; simp [t3, ains]
    refine ⟨_, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, fun q _ => ?_⟩
      · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [usame.1]; rfl
      · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [usame.2.1]; rfl
      · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [usame.2.2.2]; rfl
      · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [ureg]
    · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [umem]; rfl
    · intro q hq h4 h34
      simp only [ains, skip, Stmt.fin, pcopy, tick, Function.update_of_ne h4, Function.update_of_ne h34]
      rw [Function.update_apply]; split_ifs with h
      · subst h; rw [ufix 0 (by simp [scrS])]
      · exact ufix q hq
    · simp [ains, skip, Stmt.fin, pcopy, tick, Function.update_apply, ufix 4 (by simp [scrS]),
        ufix 2 (by simp [scrS]), h2]
    · simp [ains, skip, Stmt.fin, pcopy, tick, Function.update_apply, ufix 34 (by simp [scrS])]
    · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [ureg]; simp [c, if_neg hc]
    · simp only [ains, skip, Stmt.fin, pcopy, tick]; rw [ureg]; simp [c, if_neg hc]

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma RegFix.trans {s t u : MState} {S : Finset ℕ} (h1 : RegFix s t S) (h2 : RegFix t u S) : RegFix s u S :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    fun q hq => (h2.2.2.2 q hq).trans (h1.2.2.2 q hq)⟩

lemma RegFix.refl (s : MState) (S : Finset ℕ) : RegFix s s S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma RegFix.tick {s t : MState} {S : Finset ℕ} (h : RegFix s t S) : RegFix s (tick t) S := h

lemma samp_loop (t : MState) (k n S M : ℕ) (xs : ℕ → ℕ) (L1f L2f : ℕ → Fin 4)
    (Af Bf : ℕ → ℕ → Fin 4) (Vf Wf : ℕ → ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h20 : t.core.ptrs 20 = S)
    (h1 : t.core.ptrs 1 = M) (h34 : t.core.ptrs 34 = 0) (h4 : t.core.ptrs 4 = cSAMP k)
    (hr1 : t.core.regs 1 = 0) (hr2 : t.core.regs 2 = 0) (hr3 : t.core.regs 3 = 4 ^ S)
    (htab : Tab t.intMem)
    (hrec : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ))
    (hsm : ∀ i < M, ∀ r < S, t.intMem (cSAMP k + 4 * n * i + xs r) = (Af i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n) = (if Vf i r then 1 else 0) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n) = (Bf i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n + n) = (if Wf i r then 1 else 0)) :
    ∃ t' m, Exec (.loop 1 34 sampBody) t t' m ∧ m ≤ M * (70 * S + 32) + 1 ∧ RegFix t t' {1, 2} ∧
      t'.intMem = t.intMem ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.regs 1 = (∑ i ∈ Finset.range M, contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i)).re ∧
      t'.core.regs 2 = (∑ i ∈ Finset.range M, contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i)).im := by
  let Inv : ℕ → MState → Prop := fun i u => u.core.ptrs 34 = i ∧ u.core.ptrs 4 = cSAMP k + 4 * n * i ∧
    RegFix t u {1, 2} ∧ u.intMem = t.intMem ∧
    (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 34 → u.core.ptrs q = t.core.ptrs q) ∧
    u.core.regs 1 = (∑ i' ∈ Finset.range i, contrib S L1f L2f (Af i') (Bf i') (Vf i') (Wf i')).re ∧
    u.core.regs 2 = (∑ i' ∈ Finset.range i, contrib S L1f L2f (Af i') (Bf i') (Vf i') (Wf i')).im
  have hstep : ∀ i < M, ∀ u, Inv i u → ¬ u.core.ptrs 1 ≤ u.core.ptrs 34 ∧
      ∃ s1 m, Exec sampBody (tick u) s1 m ∧ m ≤ 70 * S + 30 ∧ Inv (i + 1) (tick s1) := by
    intro i hi u ⟨i34, i4, ireg, imem, iptr, ir1, ir2⟩
    have e : ∀ q, q ∉ scrS → q ≠ 4 → q ≠ 34 → u.core.ptrs q = t.core.ptrs q := iptr
    obtain ⟨t', m, ex, hm, tfix, tmem, tptr, t4, t34, tr1, tr2⟩ := sampBody_exec (tick u) k n S xs L1f L2f
      (Af i) (Bf i) (Vf i) (Wf i)
      (by simp only [tick_core]; rw [e 10 (by simp [scrS]) (by norm_num) (by norm_num), h10])
      (by simp only [tick_core]; rw [e 11 (by simp [scrS]) (by norm_num) (by norm_num), h11])
      (by simp only [tick_core]; rw [e 45 (by simp [scrS]) (by norm_num) (by norm_num), h45])
      (by simp only [tick_core]; rw [e 43 (by simp [scrS]) (by norm_num) (by norm_num), h43])
      (by simp only [tick_core]; rw [e 47 (by simp [scrS]) (by norm_num) (by norm_num), h47])
      (by simp only [tick_core]; rw [e 46 (by simp [scrS]) (by norm_num) (by norm_num), h46])
      (by simp only [tick_core]; rw [e 0 (by simp [scrS]) (by norm_num) (by norm_num), h0])
      (by simp only [tick_core]; rw [e 2 (by simp [scrS]) (by norm_num) (by norm_num), h2])
      (by simp only [tick_core]; rw [e 20 (by simp [scrS]) (by norm_num) (by norm_num), h20])
      (by simp only [tick_intMem, imem]; exact htab)
      (by
        intro r hr
        obtain ⟨a1, a2, a3⟩ := hrec r hr
        obtain ⟨b1, b2, b3, b4⟩ := hsm i hi r hr
        simp only [tick_intMem, tick_core, imem, i4, e 13 (by simp [scrS]) (by norm_num) (by norm_num)]
        exact ⟨a1, a2, a3, b1, b2, b3, b4⟩)
    have hreg3 : (tick u).core.regs 3 = 4 ^ S := by
      simp only [tick_core]; rw [ireg.2.2.2 3 (by simp), hr3]
    have hc : (if ∀ r < S, Bf i r = letterMul (letterMul (L2f r) (Af i r)) (L1f r) then
        ((tick u).core.regs 3 : ℂ) * Complex.I ^ (∑ r ∈ Finset.range S,
          siteExp (L1f r) (L2f r) (Af i r) (Bf i r) (Vf i r) (Wf i r)) else 0) =
        contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i) := by
      rw [hreg3]; unfold contrib; push_cast; rfl
    rw [hc] at tr1 tr2
    have su : RegFix u (tick u) {1, 2} := RegFix.refl u _
    refine ⟨by rw [e 1 (by simp [scrS]) (by norm_num) (by norm_num), h1, i34]; push_cast; omega,
      t', m, ex, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [tick_core]; rw [t34]; simp only [tick_core, i34]; push_cast; ring
    · simp only [tick_core]; rw [t4]; simp only [tick_core, i4]; push_cast; ring
    · exact (ireg.trans (su.trans tfix)).tick
    · simp only [tick_intMem]; rw [tmem]; simp only [tick_intMem]; exact imem
    · intro q hq h4 h34'; simp only [tick_core]; rw [tptr q hq h4 h34']; simp only [tick_core]
      exact e q hq h4 h34'
    · simp only [tick_core]; rw [tr1]; simp only [tick_core, ir1, Finset.sum_range_succ, Complex.add_re]
    · simp only [tick_core]; rw [tr2]; simp only [tick_core, ir2, Finset.sum_range_succ, Complex.add_im]
  have hend : ∀ u, Inv M u → u.core.ptrs 1 ≤ u.core.ptrs 34 := by
    rintro u ⟨i34, -, -, -, iptr, -⟩
    rw [iptr 1 (by simp [scrS]) (by norm_num) (by norm_num), h1, i34]
  obtain ⟨sT, m, ⟨i34, i4, ireg, imem, iptr, ir1, ir2⟩, hex, hm⟩ := loop_rule Inv M (70 * S + 30) hstep
    hend t ⟨h34, by rw [h4]; simp, RegFix.refl t _, rfl, fun q _ _ _ => rfl, by simp [hr1], by simp [hr2]⟩
  exact ⟨tick sT, m, hex, by linarith, ireg.tick, imem, iptr, ir1, ir2⟩

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma pow_loop (t : MState) (S : ℕ) (h19 : t.core.ptrs 19 = 0) (h20 : t.core.ptrs 20 = S)
    (hr3 : t.core.regs 3 = 1) (hr4 : t.core.regs 4 = 4) :
    ∃ t' m, Exec (.loop 20 19 (seqs [rmul 3 3 4, pinc 19])) t t' m ∧ m ≤ S * 4 + 1 ∧
      RegFix t t' {3} ∧ t'.intMem = t.intMem ∧ (∀ q, q ≠ 19 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.regs 3 = 4 ^ S := by
  let Inv : ℕ → MState → Prop := fun j u => u.core.ptrs 19 = j ∧ RegFix t u {3} ∧ u.intMem = t.intMem ∧
    (∀ q, q ≠ 19 → u.core.ptrs q = t.core.ptrs q) ∧ u.core.regs 3 = 4 ^ j
  have hstep : ∀ j < S, ∀ u, Inv j u → ¬ u.core.ptrs 20 ≤ u.core.ptrs 19 ∧
      ∃ s1 m, Exec (seqs [rmul 3 3 4, pinc 19]) (tick u) s1 m ∧ m ≤ 2 ∧ Inv (j + 1) (tick s1) := by
    intro j hj u ⟨i19, ifix, imem, iptr, i3⟩
    refine ⟨by rw [iptr 20 (by norm_num), h20, i19]; push_cast; omega, _, _,
      Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial), le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ains, i19]
    · refine ⟨ifix.1, ifix.2.1, ifix.2.2.1, fun q hq => ?_⟩
      have : q ≠ 3 := by simpa using hq
      simp [ains, Function.update_of_ne this, ifix.2.2.2 q hq]
    · simp [ains, imem]
    · intro q hq; simp [ains, Function.update_of_ne hq, iptr q hq]
    · have h4 : u.core.regs 4 = 4 := by rw [ifix.2.2.2 4 (by simp), hr4]
      simp [ains, i3, h4, pow_succ]
  have hend : ∀ u, Inv S u → u.core.ptrs 20 ≤ u.core.ptrs 19 := by
    rintro u ⟨i19, -, -, iptr, -⟩; rw [iptr 20 (by norm_num), h20, i19]
  obtain ⟨sT, m, ⟨i19, ifix, imem, iptr, i3⟩, hex, hm⟩ := loop_rule Inv S 2 hstep hend t
    ⟨h19, RegFix.refl t _, rfl, fun q _ => rfl, by simp [hr3]⟩
  exact ⟨tick sT, m, hex, by linarith, ifix.tick, imem, iptr, i3⟩

end LindbladStructLearn.Mach.A1

namespace LindbladStructLearn.Mach.A1
open LindbladTolerant.Testing LindbladStructLearn SmaleNinth Rec

lemma core3_exec (t : MState) (k n S M : ℕ) (xs : ℕ → ℕ) (L1f L2f : ℕ → Fin 4)
    (Af Bf : ℕ → ℕ → Fin 4) (Vf Wf : ℕ → ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h20 : t.core.ptrs 20 = S)
    (h1 : t.core.ptrs 1 = M) (hr4 : t.core.regs 4 = 4)
    (htab : Tab t.intMem)
    (hrec : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ))
    (hsm : ∀ i < M, ∀ r < S, t.intMem (cSAMP k + 4 * n * i + xs r) = (Af i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n) = (if Vf i r then 1 else 0) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n) = (Bf i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n + n) = (if Wf i r then 1 else 0)) :
    let tot := ∑ i ∈ Finset.range M, contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i)
    let b := t.core.ptrs 13
    ∃ t' m, Exec (core3 k) t t' m ∧ m ≤ M * (70 * S + 32) + 4 * S + 20 ∧
      t'.output = t.output ∧ t'.durations = t.durations ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → t'.core.regs q = t.core.regs q) ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 7 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.mem = Function.update (Function.update t.core.mem (b + (3 * k + 1))
        (tot.re * t.core.regs 6)) (b + (3 * k + 1) + 1) (tot.im * t.core.regs 6) := by
  intro tot b
  let t2 := ains (.core (.pset 19 0)) (ains (.core (.const 3 1)) t)
  obtain ⟨p, mp, ep, hmp, pfix, pmem, pptr, p3⟩ := pow_loop t2 S (by simp [t2, ains])
    (by simp [t2, ains, h20]) (by simp [t2, ains]) (by simp [t2, ains, hr4])
  have pp : ∀ q, q ≠ 19 → p.core.ptrs q = t.core.ptrs q := by
    intro q hq; rw [pptr q hq]; simp [t2, ains, Function.update_of_ne hq]
  have preg : ∀ q, q ≠ 3 → p.core.regs q = t.core.regs q := by
    intro q hq; rw [pfix.2.2.2 q (by simpa using hq)]; simp [t2, ains, Function.update_of_ne hq]
  let t7 := ains (.core (.pset 34 0)) (ains (.core (.pset 4 (cSAMP k))) (ains (.core (.const 2 0))
    (ains (.core (.const 1 0)) p)))
  have tp : ∀ q, q ≠ 4 → q ≠ 34 → t7.core.ptrs q = p.core.ptrs q := by
    intro q a b'; simp [t7, ains, Function.update_of_ne a, Function.update_of_ne b']
  have tq : ∀ q, q ∉ scrS → q ≠ 4 → q ≠ 34 → t7.core.ptrs q = t.core.ptrs q := by
    intro q hq a b'; rw [tp q a b', pp q (by intro h; subst h; simp [scrS] at hq)]
  have t7mem : t7.intMem = t.intMem := by simp only [t7, ains]; rw [pmem]; rfl
  have t7_13 : t7.core.ptrs 13 = t.core.ptrs 13 := tq 13 (by simp [scrS]) (by norm_num) (by norm_num)
  obtain ⟨u, mu, eu, hmu, ufix, umem, uptr, u1, u2⟩ := samp_loop t7 k n S M xs L1f L2f Af Bf Vf Wf
    (by rw [tq 10 (by simp [scrS]) (by norm_num) (by norm_num), h10])
    (by rw [tq 11 (by simp [scrS]) (by norm_num) (by norm_num), h11])
    (by rw [tq 45 (by simp [scrS]) (by norm_num) (by norm_num), h45])
    (by rw [tq 43 (by simp [scrS]) (by norm_num) (by norm_num), h43])
    (by rw [tq 47 (by simp [scrS]) (by norm_num) (by norm_num), h47])
    (by rw [tq 46 (by simp [scrS]) (by norm_num) (by norm_num), h46])
    (by rw [tq 0 (by simp [scrS]) (by norm_num) (by norm_num), h0])
    (by rw [tq 2 (by simp [scrS]) (by norm_num) (by norm_num), h2])
    (by rw [tp 20 (by norm_num) (by norm_num), pp 20 (by norm_num), h20])
    (by rw [tq 1 (by simp [scrS]) (by norm_num) (by norm_num), h1])
    (by simp [t7, ains]) (by simp [t7, ains])
    (by simp [t7, ains]) (by simp [t7, ains])
    (by simp only [t7, ains]; simp [Function.update_of_ne, p3])
    (by rw [t7mem]; exact htab)
    (by rw [t7mem, t7_13]; exact hrec)
    (by rw [t7mem]; exact hsm)
  have u13 : u.core.ptrs 13 = b := by
    rw [uptr 13 (by simp [scrS]) (by norm_num) (by norm_num), tq 13 (by simp [scrS]) (by norm_num) (by norm_num)]
  have ureg : ∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → u.core.regs q = t.core.regs q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    rw [ufix.2.2.2 q (by simp [hq.1, hq.2.1])]
    simp only [t7, ains, Function.update_of_ne hq.1, Function.update_of_ne hq.2.1]
    exact preg q hq.2.2
  have umem' : u.core.mem = t.core.mem := by
    rw [ufix.2.2.1]; simp only [t7, ains]; rw [pfix.2.2.1]; rfl
  have ex : Exec (core3 k) t (ains (.core (.store 6 2)) (ains (.core (.pinc 6)) (ains (.core (.store 6 1))
      (ains (.pointerAdd 6 13 7) (ains (.core (.pset 7 (3 * k + 1))) (ains (.core (.mul 2 2 6))
      (ains (.core (.mul 1 1 6)) u)))))))
      (1 + (1 + (mp + (1 + (1 + (1 + (1 + (mu + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))))))) := by
    unfold core3; simp only [seqs]
    exact (Exec.seq (Exec.ins _ t trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq ep (Exec.seq (Exec.ins _ p trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq eu (Exec.seq (Exec.ins _ u trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.seq (Exec.ins _ _ trivial) (Exec.ins _ _ trivial)))))))))))))))
  have u6 : u.core.regs 6 = t.core.regs 6 := ureg 6 (by simp)
  refine ⟨_, _, ex, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ains]; rw [ufix.1]; simp only [t7, ains]; rw [pfix.1]; rfl
  · simp only [ains]; rw [ufix.2.1]; simp only [t7, ains]; rw [pfix.2.1]; rfl
  · simp only [ains]; rw [umem]; simp only [t7, ains]; rw [pmem]; rfl
  · intro q hq
    have hq' := hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq'
    simp only [ains, Function.update_of_ne hq'.1, Function.update_of_ne hq'.2.1]
    exact ureg q hq
  · intro q hq h4 h7 h34
    have h6 : q ≠ 6 := by intro h; subst h; simp [scrS] at hq
    simp only [ains, Function.update_of_ne h6, Function.update_of_ne h7]
    rw [uptr q hq h4 h34, tq q hq h4 h34]
  · have e13 : u.core.ptrs 13 = b := u13
    simp only [ains]
    simp only [Function.update_apply, show (13 : ℕ) ≠ 7 by norm_num, show (6 : ℕ) ≠ 7 by norm_num,
      show (2 : ℕ) ≠ 1 by norm_num, show (1 : ℕ) ≠ 2 by norm_num, show (6 : ℕ) = 6 from rfl, if_true,
      if_false, e13, umem', u1, u2, u6]
    funext z
    simp only [tot]
    split_ifs <;> first | (exfalso; omega) | ring_nf | rfl

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
theorem solution : ∀ (t : MState) (k n S M : ℕ) (xs : ℕ → ℕ) (L1f L2f : ℕ → Fin 4)
    (Af Bf : ℕ → ℕ → Fin 4) (Vf Wf : ℕ → ℕ → Bool)
    (h10 : t.core.ptrs 10 = 0) (h11 : t.core.ptrs 11 = 1) (h45 : t.core.ptrs 45 = 2)
    (h43 : t.core.ptrs 43 = 3) (h47 : t.core.ptrs 47 = 4) (h46 : t.core.ptrs 46 = k)
    (h0 : t.core.ptrs 0 = n) (h2 : t.core.ptrs 2 = 4 * n) (h20 : t.core.ptrs 20 = S)
    (h1 : t.core.ptrs 1 = M) (hr4 : t.core.regs 4 = 4)
    (htab : Tab t.intMem)
    (hrec : ∀ r < S, t.intMem (t.core.ptrs 13 + r + 1) = xs r ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k) = (L1f r : ℕ) ∧
      t.intMem (t.core.ptrs 13 + r + 1 + k + k) = (L2f r : ℕ))
    (hsm : ∀ i < M, ∀ r < S, t.intMem (cSAMP k + 4 * n * i + xs r) = (Af i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n) = (if Vf i r then 1 else 0) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n) = (Bf i r : ℕ) ∧
      t.intMem (cSAMP k + 4 * n * i + xs r + n + n + n) = (if Wf i r then 1 else 0)),
    let tot := ∑ i ∈ Finset.range M, contrib S L1f L2f (Af i) (Bf i) (Vf i) (Wf i)
    let b := t.core.ptrs 13
    ∃ t' m, Exec (core3 k) t t' m ∧ m ≤ M * (70 * S + 32) + 4 * S + 20 ∧
      t'.output = t.output ∧ t'.durations = t.durations ∧ t'.intMem = t.intMem ∧
      (∀ q, q ∉ ({1, 2, 3} : Finset ℕ) → t'.core.regs q = t.core.regs q) ∧
      (∀ q, q ∉ scrS → q ≠ 4 → q ≠ 7 → q ≠ 34 → t'.core.ptrs q = t.core.ptrs q) ∧
      t'.core.mem = Function.update (Function.update t.core.mem (b + (3 * k + 1))
        (tot.re * t.core.regs 6)) (b + (3 * k + 1) + 1) (tot.im * t.core.regs 6) :=
  @LindbladStructLearn.Mach.A1.core3_exec
