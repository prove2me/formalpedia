-- Prove2me | solution 1 for IntermediateDisorder.PointToLine.partitionFunction_sub_modified_eLpNorm_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T17:17:04.37701+00:00
-- url     : https://prove2.me/submissions/a46daac6-1cc1-47fe-869c-303ce6a78ace

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment

set_option autoImplicit false

namespace IntermediateDisorder.PointToLine
open MeasureTheory ProbabilityTheory Filter Topology Finset

lemma sum_fun_snoc {n : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → Bool) → M) :
    ∑ s, f s = ∑ t : Fin n → Bool, ∑ b : Bool, f (Fin.snoc (α := fun _ => Bool) t b) := by
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma walkPos_snoc {n : ℕ} (t : Fin n → Bool) (b : Bool) (i : ℕ) :
    walkPos (Fin.snoc (α := fun _ => Bool) t b) i = walkPos t i + if n < i then stepZ b else 0 := by
  unfold walkPos
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma walkPos_of_le {n : ℕ} (t : Fin n → Bool) {i : ℕ} (hi : n ≤ i) :
    walkPos t i = walkPos t n := by
  unfold walkPos
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : (j : ℕ) < i := lt_of_lt_of_le j.isLt hi
  simp [h1, j.isLt]

lemma walkPos_snoc_le {n : ℕ} (t : Fin n → Bool) (b : Bool) {i : ℕ} (hi : i ≤ n) :
    walkPos (Fin.snoc (α := fun _ => Bool) t b) i = walkPos t i := by
  rw [walkPos_snoc]; simp [not_lt.mpr hi]

lemma walkPos_snoc_succ {n : ℕ} (t : Fin n → Bool) (b : Bool) :
    walkPos (Fin.snoc (α := fun _ => Bool) t b) (n + 1) = walkPos t n + stepZ b := by
  rw [walkPos_snoc, walkPos_of_le t (Nat.le_succ n)]; simp

/-- number of collisions at times `1..n`. -/
def ovl {n : ℕ} (s s' : Fin n → Bool) : ℕ :=
  (univ.filter fun m : Fin n => walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card

/-- number of collisions at times `0..n-1`. -/
def ovl0 {n : ℕ} (s s' : Fin n → Bool) : ℕ :=
  (univ.filter fun m : Fin n => walkPos s (m : ℕ) = walkPos s' (m : ℕ)).card

/-- difference of the two walks at time `n`. -/
def dif {n : ℕ} (s s' : Fin n → Bool) : ℤ := walkPos s n - walkPos s' n

lemma card_filter_castSucc {n : ℕ} (p : Fin (n + 1) → Prop) [DecidablePred p] :
    (univ.filter p).card =
      (univ.filter fun m : Fin n => p m.castSucc).card + if p (Fin.last n) then 1 else 0 := by
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]

lemma ovl_snoc {n : ℕ} (t t' : Fin n → Bool) (b b' : Bool) :
    ovl (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b') =
      ovl t t' + if walkPos t n + stepZ b = walkPos t' n + stepZ b' then 1 else 0 := by
  unfold ovl
  rw [card_filter_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, walkPos_snoc_succ]
  congr 1
  congr 1
  apply Finset.filter_congr
  intro m _
  rw [walkPos_snoc_le _ _ (show (m : ℕ) + 1 ≤ n from m.isLt),
    walkPos_snoc_le _ _ (show (m : ℕ) + 1 ≤ n from m.isLt)]

lemma ovl0_snoc {n : ℕ} (t t' : Fin n → Bool) (b b' : Bool) :
    ovl0 (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b') =
      ovl0 t t' + if walkPos t n = walkPos t' n then 1 else 0 := by
  unfold ovl0
  rw [card_filter_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, walkPos_snoc_le _ _ le_rfl]
  congr 1
  congr 1
  apply Finset.filter_congr
  intro m _
  rw [walkPos_snoc_le _ _ (show (m : ℕ) ≤ n from m.isLt.le),
    walkPos_snoc_le _ _ (show (m : ℕ) ≤ n from m.isLt.le)]

lemma dif_snoc {n : ℕ} (t t' : Fin n → Bool) (b b' : Bool) :
    dif (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b') =
      dif t t' + (stepZ b - stepZ b') := by
  unfold dif
  rw [walkPos_snoc_succ, walkPos_snoc_succ]
  ring

lemma ovl_add_one {n : ℕ} (s s' : Fin n → Bool) :
    ovl s s' + 1 = ovl0 s s' + if dif s s' = 0 then 1 else 0 := by
  induction n with
  | zero => simp [ovl, ovl0, dif, walkPos]
  | succ n ih =>
    rw [← Fin.snoc_init_self s, ← Fin.snoc_init_self s']
    rw [ovl_snoc, ovl0_snoc, dif_snoc]
    have key1 : (walkPos (Fin.init s) n = walkPos (Fin.init s') n) ↔
        dif (Fin.init s) (Fin.init s') = 0 := by unfold dif; omega
    have key2 : (walkPos (Fin.init s) n + stepZ (s (Fin.last n)) =
        walkPos (Fin.init s') n + stepZ (s' (Fin.last n))) ↔
        dif (Fin.init s) (Fin.init s') + (stepZ (s (Fin.last n)) - stepZ (s' (Fin.last n))) = 0 := by
      unfold dif; omega
    have := ih (Fin.init s) (Fin.init s')
    simp only [key1, key2]
    split_ifs at * <;> omega

lemma ovl_le_ovl0 {n : ℕ} (s s' : Fin n → Bool) : ovl s s' ≤ ovl0 s s' := by
  have := ovl_add_one s s'
  split_ifs at this <;> omega

lemma dif_even {n : ℕ} (s s' : Fin n → Bool) : Even (dif s s') := by
  induction n with
  | zero => simp [dif, walkPos]
  | succ n ih =>
    rw [← Fin.snoc_init_self s, ← Fin.snoc_init_self s', dif_snoc]
    refine (ih _ _).add ?_
    cases s (Fin.last n) <;> cases s' (Fin.last n) <;> simp [stepZ]

/-- generic product-bound induction over pairs of step sequences. -/
lemma sum_pairs_le (F : ∀ n : ℕ, (Fin n → Bool) → (Fin n → Bool) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h0 : ∑ s : Fin 0 → Bool, ∑ s' : Fin 0 → Bool, F 0 s s' ≤ 1)
    (hstep : ∀ (n : ℕ) (t t' : Fin n → Bool),
      ∑ b : Bool, ∑ b' : Bool,
        F (n + 1) (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b') ≤
        K * F n t t') :
    ∀ n : ℕ, ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool, F n s s' ≤ K ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 : ∀ s : Fin (n + 1) → Bool, ∑ s' : Fin (n + 1) → Bool, F (n + 1) s s' =
        ∑ t' : Fin n → Bool, ∑ b' : Bool, F (n + 1) s (Fin.snoc (α := fun _ => Bool) t' b') :=
      fun s => sum_fun_snoc _
    rw [Finset.sum_congr rfl (fun s _ => h1 s), sum_fun_snoc]
    calc ∑ t : Fin n → Bool, ∑ b : Bool, ∑ t' : Fin n → Bool, ∑ b' : Bool,
          F (n + 1) (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b')
        = ∑ t : Fin n → Bool, ∑ t' : Fin n → Bool, ∑ b : Bool, ∑ b' : Bool,
          F (n + 1) (Fin.snoc (α := fun _ => Bool) t b) (Fin.snoc (α := fun _ => Bool) t' b') := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          exact Finset.sum_comm
      _ ≤ ∑ t : Fin n → Bool, ∑ t' : Fin n → Bool, K * F n t t' := by
          gcongr with t _ t' _
          exact hstep n t t'
      _ = K * ∑ t : Fin n → Bool, ∑ t' : Fin n → Bool, F n t t' := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ K * K ^ n := by gcongr
      _ = K ^ (n + 1) := by ring

lemma cosh_le_exp_sq (u : ℝ) : Real.cosh u ≤ Real.exp (u ^ 2) := by
  refine (Real.cosh_le_exp_half_sq u).trans (Real.exp_le_exp.mpr ?_)
  nlinarith [sq_nonneg u]

lemma two_add_exp_le (u : ℝ) :
    2 + Real.exp (2 * u) + Real.exp (-(2 * u)) ≤ 4 * Real.exp (u ^ 2) := by
  have hc : 0 ≤ (Real.exp u + Real.exp (-u)) / 2 := by positivity
  have hh := Real.cosh_le_exp_half_sq u
  rw [Real.cosh_eq] at hh
  have h3 : ((Real.exp u + Real.exp (-u)) / 2) ^ 2 ≤ Real.exp (u ^ 2 / 2) ^ 2 :=
    pow_le_pow_left₀ hc hh 2
  have e1 : Real.exp (2 * u) = Real.exp u ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have e2 : Real.exp (-(2 * u)) = Real.exp (-u) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have e3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have e5 : Real.exp (u ^ 2 / 2) ^ 2 = Real.exp (u ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [e1, e2]
  nlinarith [e3, e5, h3]

lemma sum_bool_step (g : ℤ → ℝ) (d : ℤ) :
    ∑ b : Bool, ∑ b' : Bool, g (d + (stepZ b - stepZ b')) = 2 * g d + g (d + 2) + g (d - 2) := by
  simp only [Fintype.sum_bool, stepZ, if_true, Bool.false_eq_true, if_false]
  have h1 : d + (1 - 1) = d := by ring
  have h2 : d + (1 - -1) = d + 2 := by ring
  have h3 : d + (-1 - 1) = d - 2 := by ring
  have h4 : d + (-1 - -1) = d := by ring
  rw [h1, h2, h3, h4]
  ring

lemma step_pot_real (u : ℝ) (hu : 0 ≤ u) (ℓ : ℝ) (x : ℝ) (hx : x = 0 ∨ 2 ≤ |x|) :
    2 * Real.exp (u * (ℓ + if x = 0 then 1 else 0) - u * |x|) +
      Real.exp (u * (ℓ + if x = 0 then 1 else 0) - u * |x + 2|) +
      Real.exp (u * (ℓ + if x = 0 then 1 else 0) - u * |x - 2|) ≤
      4 * Real.exp (u ^ 2) * Real.exp (u * ℓ - u * |x|) := by
  have hE := two_add_exp_le u
  rcases hx with h0 | h2
  · subst h0
    simp only [if_true, abs_zero, zero_add, zero_sub, abs_neg, abs_two, mul_zero, sub_zero]
    have hcosh := cosh_le_exp_sq u
    rw [Real.cosh_eq] at hcosh
    have ea : Real.exp (u * (ℓ + 1)) = Real.exp (u * ℓ) * Real.exp u := by
      rw [← Real.exp_add]; ring_nf
    have eb : Real.exp (u * (ℓ + 1) - u * 2) = Real.exp (u * ℓ) * Real.exp (-u) := by
      rw [← Real.exp_add]; ring_nf
    rw [ea, eb]
    have hp : 0 < Real.exp (u * ℓ) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left hcosh hp.le]
  · have hne : x ≠ 0 := by
      intro h; rw [h, abs_zero] at h2; norm_num at h2
    simp only [hne, if_false, add_zero]
    have hab : |x + 2| = |x| + 2 ∧ |x - 2| = |x| - 2 ∨ |x + 2| = |x| - 2 ∧ |x - 2| = |x| + 2 := by
      rcases le_or_gt 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0] at h2 ⊢
        left
        exact ⟨abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)⟩
      · rw [abs_of_neg hx0] at h2 ⊢
        right
        exact ⟨by rw [abs_of_nonpos (by linarith)]; ring,
          by rw [abs_of_neg (by linarith)]; ring⟩
    set E := Real.exp (u * ℓ - u * |x|) with hEdef
    have ep : Real.exp (u * ℓ - u * (|x| + 2)) = E * Real.exp (-(2 * u)) := by
      rw [hEdef, ← Real.exp_add]; ring_nf
    have em : Real.exp (u * ℓ - u * (|x| - 2)) = E * Real.exp (2 * u) := by
      rw [hEdef, ← Real.exp_add]; ring_nf
    have hp : 0 < E := Real.exp_pos _
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb, ep, em]
      nlinarith [mul_le_mul_of_nonneg_left hE hp.le]
    · rw [ha, hb, ep, em]
      nlinarith [mul_le_mul_of_nonneg_left hE hp.le]

lemma pot_bound (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
      Real.exp (u * (ovl0 s s' : ℝ) - u * |((dif s s' : ℤ) : ℝ)|) ≤ (4 * Real.exp (u ^ 2)) ^ n := by
  refine sum_pairs_le (fun n s s' => Real.exp (u * (ovl0 s s' : ℝ) - u * |((dif s s' : ℤ) : ℝ)|))
    _ (by positivity) ?_ ?_ n
  · simp [ovl0, dif, walkPos]
  · intro n t t'
    simp only [ovl0_snoc, dif_snoc]
    have key : (walkPos t n = walkPos t' n) ↔ dif t t' = 0 := by unfold dif; omega
    simp only [key]
    have hg := sum_bool_step (fun e : ℤ => Real.exp (u * ((ovl0 t t' + if dif t t' = 0 then 1 else 0 : ℕ) : ℝ) - u * |(e : ℝ)|)) (dif t t')
    rw [hg]
    have hx : ((dif t t' : ℤ) : ℝ) = 0 ∨ 2 ≤ |((dif t t' : ℤ) : ℝ)| := by
      rcases eq_or_ne (dif t t') 0 with h | h
      · left; simp [h]
      · right
        obtain ⟨k, hk⟩ := dif_even t t'
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact h hk
        have : (2 : ℤ) ≤ |dif t t'| := by
          rw [hk]
          rcases lt_or_gt_of_ne hk0 with hk1 | hk1
          · rw [abs_of_neg (by omega)]; omega
          · rw [abs_of_pos (by omega)]; omega
        exact_mod_cast this
    have := step_pot_real u hu (ovl0 t t' : ℝ) _ hx
    have hc : ((if dif t t' = 0 then (1 : ℕ) else 0 : ℕ) : ℝ) =
        (if ((dif t t' : ℤ) : ℝ) = 0 then 1 else 0) := by
      split_ifs with h1 h2 h2 <;> simp_all
    push_cast [hc]
    convert this using 3 <;> push_cast <;> ring_nf

lemma dif_bound (v : ℝ) (n : ℕ) :
    ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool, Real.exp (v * ((dif s s' : ℤ) : ℝ)) ≤
      (4 * Real.exp (v ^ 2)) ^ n := by
  refine sum_pairs_le (fun n s s' => Real.exp (v * ((dif s s' : ℤ) : ℝ))) _ (by positivity) ?_ ?_ n
  · simp [dif, walkPos]
  · intro n t t'
    simp only [dif_snoc]
    rw [sum_bool_step (fun e : ℤ => Real.exp (v * (e : ℝ)))]
    have hE := two_add_exp_le v
    set E := Real.exp (v * ((dif t t' : ℤ) : ℝ)) with hEdef
    have ep : Real.exp (v * (((dif t t' + 2 : ℤ)) : ℝ)) = E * Real.exp (2 * v) := by
      rw [hEdef, ← Real.exp_add]; push_cast; ring_nf
    have em : Real.exp (v * (((dif t t' - 2 : ℤ)) : ℝ)) = E * Real.exp (-(2 * v)) := by
      rw [hEdef, ← Real.exp_add]; push_cast; ring_nf
    rw [ep, em]
    have hp : 0 < E := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left hE hp.le]

/-- D2: exponential moments of the overlap. -/
theorem overlap_exp_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool, Real.exp (t * (ovl s s' : ℝ)) ≤
      2 * (4 * Real.exp (4 * t ^ 2)) ^ n := by
  have h1 := pot_bound (2 * t) (by linarith) n
  have h2 := dif_bound (2 * t) n
  have h3 := dif_bound (-(2 * t)) n
  have hsq : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
  have hsq' : (-(2 * t)) ^ 2 = 4 * t ^ 2 := by ring
  rw [hsq] at h1 h2
  rw [hsq'] at h3
  have hpt : ∀ s s' : Fin n → Bool, Real.exp (t * (ovl s s' : ℝ)) ≤
      (Real.exp (2 * t * (ovl0 s s' : ℝ) - 2 * t * |((dif s s' : ℤ) : ℝ)|) +
        (Real.exp (2 * t * ((dif s s' : ℤ) : ℝ)) + Real.exp (-(2 * t) * ((dif s s' : ℤ) : ℝ)))) / 2 := by
    intro s s'
    set D : ℝ := ((dif s s' : ℤ) : ℝ)
    have hle : (ovl s s' : ℝ) ≤ ovl0 s s' := by exact_mod_cast ovl_le_ovl0 s s'
    have e1 : Real.exp (t * (ovl s s' : ℝ)) ≤ Real.exp (t * (ovl0 s s' : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle ht)
    set a := Real.exp (t * (ovl0 s s' : ℝ) - t * |D|)
    set b := Real.exp (t * |D|)
    have hab : Real.exp (t * (ovl0 s s' : ℝ)) = a * b := by
      rw [← Real.exp_add]; ring_nf
    have ha2 : Real.exp (2 * t * (ovl0 s s' : ℝ) - 2 * t * |D|) = a ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hb2 : b ^ 2 ≤ Real.exp (2 * t * D) + Real.exp (-(2 * t) * D) := by
      rw [← Real.exp_nat_mul]
      rcases le_or_gt 0 D with hD | hD
      · rw [abs_of_nonneg hD]
        have : Real.exp (((2 : ℕ) : ℝ) * (t * D)) = Real.exp (2 * t * D) := by ring_nf
        rw [this]; linarith [Real.exp_pos (-(2 * t) * D)]
      · rw [abs_of_neg hD]
        have : Real.exp (((2 : ℕ) : ℝ) * (t * -D)) = Real.exp (-(2 * t) * D) := by ring_nf
        rw [this]; linarith [Real.exp_pos (2 * t * D)]
    rw [ha2]
    nlinarith [two_mul_le_add_sq a b]
  calc ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool, Real.exp (t * (ovl s s' : ℝ))
      ≤ ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
          (Real.exp (2 * t * (ovl0 s s' : ℝ) - 2 * t * |((dif s s' : ℤ) : ℝ)|) +
            (Real.exp (2 * t * ((dif s s' : ℤ) : ℝ)) +
              Real.exp (-(2 * t) * ((dif s s' : ℤ) : ℝ)))) / 2 := by
        gcongr with s _ s' _
        exact hpt s s'
    _ = ((∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
          Real.exp (2 * t * (ovl0 s s' : ℝ) - 2 * t * |((dif s s' : ℤ) : ℝ)|)) +
        ((∑ s : Fin n → Bool, ∑ s' : Fin n → Bool, Real.exp (2 * t * ((dif s s' : ℤ) : ℝ))) +
          ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
            Real.exp (-(2 * t) * ((dif s s' : ℤ) : ℝ)))) / 2 := by
        simp only [Finset.sum_div, Finset.sum_add_distrib, add_div]
    _ ≤ ((4 * Real.exp (4 * t ^ 2)) ^ n + ((4 * Real.exp (4 * t ^ 2)) ^ n +
          (4 * Real.exp (4 * t ^ 2)) ^ n)) / 2 := by gcongr
    _ ≤ 2 * (4 * Real.exp (4 * t ^ 2)) ^ n := by
        have : 0 ≤ (4 * Real.exp (4 * t ^ 2)) ^ n := by positivity
        linarith


lemma integral_finset_prod_indep {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ι : Type*} (S : Finset ι) (X : ι → Ω → ℝ)
    (hX : iIndepFun X Q) (hm : ∀ i, Measurable (X i)) :
    ∫ a, ∏ i ∈ S, X i a ∂Q = ∏ i ∈ S, ∫ a, X i a ∂Q := by
  classical
  have := hX.isProbabilityMeasure
  induction S using Finset.cons_induction with
  | empty => simp
  | cons j S hj ih =>
    simp only [Finset.prod_cons]
    have hind : IndepFun (X j) (∏ i ∈ S, X i) Q := (hX.indepFun_finsetProd_of_notMem hm hj).symm
    have hmS : Measurable (∏ i ∈ S, X i) := by
      have := Finset.measurable_prod S (fun i _ => hm i)
      convert this using 1
      ext a; simp [Finset.prod_apply]
    have h2 := hind.integral_fun_mul_eq_mul_integral (hm j).aestronglyMeasurable
      hmS.aestronglyMeasurable
    simp only [Finset.prod_apply] at h2
    rw [h2, ih]

lemma integrable_finset_prod_indep {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ι : Type*} (S : Finset ι) (X : ι → Ω → ℝ)
    (hX : iIndepFun X Q) (hm : ∀ i, Measurable (X i)) (hi : ∀ i ∈ S, Integrable (X i) Q) :
    Integrable (fun a => ∏ i ∈ S, X i a) Q := by
  classical
  have := hX.isProbabilityMeasure
  induction S using Finset.cons_induction with
  | empty => simp
  | cons j S hj ih =>
    have hind : IndepFun (X j) (∏ i ∈ S, X i) Q := (hX.indepFun_finsetProd_of_notMem hm hj).symm
    have hS : Integrable (∏ i ∈ S, X i) Q := by
      have := ih (fun i hi' => hi i (Finset.mem_cons_of_mem hi'))
      convert this using 1
      ext a; simp [Finset.prod_apply]
    have := hind.integrable_mul (hi j (Finset.mem_cons_self j S)) hS
    convert this using 1
    ext a; simp only [Pi.mul_apply, Finset.prod_apply, Finset.prod_cons]

/-- sites visited by a path at times `1..n`. -/
def pathSites {n : ℕ} (s : Fin n → Bool) : Finset (ℕ × ℤ) :=
  univ.image fun m : Fin n => ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1))

lemma pathSites_inj {n : ℕ} (s : Fin n → Bool) :
    Function.Injective fun m : Fin n => ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) := by
  intro m m' h
  have := congrArg Prod.fst h
  simp only at this
  exact Fin.ext (by omega)

lemma prod_path {n : ℕ} (s : Fin n → Bool) (f : ℕ × ℤ → ℝ) :
    ∏ m : Fin n, f ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) = ∏ p ∈ pathSites s, f p := by
  classical
  rw [pathSites, Finset.prod_image (fun x _ y _ h => pathSites_inj s h)]

lemma card_inter_pathSites {n : ℕ} (s s' : Fin n → Bool) :
    (pathSites s ∩ pathSites s').card =
      (univ.filter fun m : Fin n => walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card := by
  classical
  have h : pathSites s ∩ pathSites s' =
      (univ.filter fun m : Fin n => walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).image
        (fun m : Fin n => ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1))) := by
    ext ⟨t, x⟩
    simp only [pathSites, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨m, hm1, hm2⟩, ⟨m', hm1', hm2'⟩⟩
      have hmm : m = m' := Fin.ext (by omega)
      subst hmm
      exact ⟨m, by rw [hm2, hm2'], hm1, hm2⟩
    · rintro ⟨m, hc, hm1, hm2⟩
      exact ⟨⟨m, hm1, hm2⟩, ⟨m, hm1, by rw [← hc]; exact hm2⟩⟩
  rw [h, Finset.card_image_of_injective _ (pathSites_inj s)]

/-- the site function used to factor a product over two paths. -/
noncomputable def twoPathFun {n : ℕ} (s s' : Fin n → Bool) (φ ψ : ℝ → ℝ) (p : ℕ × ℤ) (x : ℝ) : ℝ :=
  (if p ∈ pathSites s then φ x else 1) * (if p ∈ pathSites s' then ψ x else 1)

lemma twoPathFun_measurable {n : ℕ} (s s' : Fin n → Bool) (φ ψ : ℝ → ℝ) (hφ : Measurable φ)
    (hψ : Measurable ψ) (p : ℕ × ℤ) : Measurable (twoPathFun s s' φ ψ p) := by
  unfold twoPathFun
  by_cases h1 : p ∈ pathSites s <;> by_cases h2 : p ∈ pathSites s' <;>
    simp only [h1, h2, if_true, if_false, mul_one, one_mul]
  · exact hφ.mul hψ
  · exact hφ
  · exact hψ
  · exact measurable_const

lemma prod_two_paths {n : ℕ} (s s' : Fin n → Bool) (φ ψ : ℝ → ℝ) (g : ℕ × ℤ → ℝ) :
    (∏ m : Fin n, φ (g ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)))) *
      (∏ m : Fin n, ψ (g ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)))) =
      ∏ p ∈ pathSites s ∪ pathSites s', twoPathFun s s' φ ψ p (g p) := by
  classical
  rw [prod_path s (fun p => φ (g p)), prod_path s' (fun p => ψ (g p))]
  unfold twoPathFun
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
    Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]

/-- D1 core: the expectation of a product over two paths. -/
theorem integral_two_paths {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ1 : ∫ a, φ (ω (1, 0) a) ∂Q = 1) (hψ1 : ∫ a, ψ (ω (1, 0) a) ∂Q = 1)
    {n : ℕ} (s s' : Fin n → Bool) :
    ∫ a, (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) ∂Q =
      (∫ a, φ (ω (1, 0) a) * ψ (ω (1, 0) a) ∂Q) ^
        (univ.filter fun m : Fin n => walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card := by
  classical
  have hpt := fun a => prod_two_paths s s' φ ψ (fun p => ω p a)
  simp_rw [hpt]
  have hmeas := twoPathFun_measurable s s' φ ψ hφ hψ
  have hind : iIndepFun (fun p => fun a => twoPathFun s s' φ ψ p (ω p a)) Q :=
    hω.indep.comp (fun p => twoPathFun s s' φ ψ p) hmeas
  rw [integral_finset_prod_indep _ _ hind (fun p => (hmeas p).comp (hω.measurable p))]
  have hval : ∀ p ∈ pathSites s ∪ pathSites s', ∫ a, twoPathFun s s' φ ψ p (ω p a) ∂Q =
      if p ∈ pathSites s ∩ pathSites s' then ∫ a, φ (ω (1, 0) a) * ψ (ω (1, 0) a) ∂Q else 1 := by
    intro p _
    have hid := ((hω.identDistrib p).comp (hmeas p)).integral_eq
    simp only [Function.comp_apply] at hid
    rw [hid]
    unfold twoPathFun
    by_cases h1 : p ∈ pathSites s <;> by_cases h2 : p ∈ pathSites s' <;>
      simp [h1, h2, hφ1, hψ1]
  rw [Finset.prod_congr rfl hval, Finset.prod_ite_mem, Finset.prod_const,
    Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans Finset.subset_union_left),
    card_inter_pathSites]

lemma integrable_two_paths {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp (fun a => φ (ω (1, 0) a)) 2 Q) (hψ2 : MemLp (fun a => ψ (ω (1, 0) a)) 2 Q)
    {n : ℕ} (s s' : Fin n → Bool) :
    Integrable (fun a => (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a))) Q := by
  classical
  have hpt := fun a => prod_two_paths s s' φ ψ (fun p => ω p a)
  simp_rw [hpt]
  have hmeas := twoPathFun_measurable s s' φ ψ hφ hψ
  have hind : iIndepFun (fun p => fun a => twoPathFun s s' φ ψ p (ω p a)) Q :=
    hω.indep.comp (fun p => twoPathFun s s' φ ψ p) hmeas
  refine integrable_finset_prod_indep _ _ hind (fun p => (hmeas p).comp (hω.measurable p)) ?_
  intro p _
  have hid := ((hω.identDistrib p).comp (hmeas p)).integrable_iff
  simp only [Function.comp_def] at hid
  rw [hid]
  have hφ1 : Integrable (fun a => φ (ω (1, 0) a)) Q := hφ2.integrable one_le_two
  have hψ1 : Integrable (fun a => ψ (ω (1, 0) a)) Q := hψ2.integrable one_le_two
  have hφψ : Integrable (fun a => φ (ω (1, 0) a) * ψ (ω (1, 0) a)) Q := hφ2.integrable_mul hψ2
  unfold twoPathFun
  by_cases h1 : p ∈ pathSites s <;> by_cases h2 : p ∈ pathSites s' <;>
    simp only [h1, h2, if_true, if_false, mul_one, one_mul]
  · exact hφψ
  · exact hφ1
  · exact hψ1
  · exact integrable_const 1

/-- D1: second moment of the difference of two product-type partition functions. -/
theorem second_moment_diff {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (φ ψ : ℝ → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp (fun a => φ (ω (1, 0) a)) 2 Q) (hψ2 : MemLp (fun a => ψ (ω (1, 0) a)) 2 Q)
    (hφ1 : ∫ a, φ (ω (1, 0) a) ∂Q = 1) (hψ1 : ∫ a, ψ (ω (1, 0) a) ∂Q = 1) (n : ℕ) :
    ∫ a, (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
            ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) -
          ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
            ∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) ^ 2 ∂Q =
      ((4 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
        ((∫ a, φ (ω (1, 0) a) * φ (ω (1, 0) a) ∂Q) ^ (univ.filter fun m : Fin n =>
              walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card -
          (∫ a, φ (ω (1, 0) a) * ψ (ω (1, 0) a) ∂Q) ^ (univ.filter fun m : Fin n =>
              walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card -
          (∫ a, ψ (ω (1, 0) a) * φ (ω (1, 0) a) ∂Q) ^ (univ.filter fun m : Fin n =>
              walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card +
          (∫ a, ψ (ω (1, 0) a) * ψ (ω (1, 0) a) ∂Q) ^ (univ.filter fun m : Fin n =>
              walkPos s ((m : ℕ) + 1) = walkPos s' ((m : ℕ) + 1)).card) := by
  classical
  set Φ : (Fin n → Bool) → Ω → ℝ := fun s a =>
    ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) with hΦ
  set Ψ : (Fin n → Bool) → Ω → ℝ := fun s a =>
    ∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) with hΨ
  have hpt : ∀ a, (((2 : ℝ) ^ n)⁻¹ * ∑ s, Φ s a - ((2 : ℝ) ^ n)⁻¹ * ∑ s, Ψ s a) ^ 2 =
      ((4 : ℝ) ^ n)⁻¹ * ∑ s, ∑ s', (Φ s a * Φ s' a - Φ s a * Ψ s' a - Ψ s a * Φ s' a +
        Ψ s a * Ψ s' a) := by
    intro a
    have h4 : ((4 : ℝ) ^ n)⁻¹ = ((2 : ℝ) ^ n)⁻¹ ^ 2 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4, ← mul_sub, ← Finset.sum_sub_distrib, mul_pow, sq (∑ s, (Φ s a - Ψ s a)),
      Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => ?_))
    ring
  have hI : ∀ (f g : ℝ → ℝ), Measurable f → Measurable g →
      MemLp (fun a => f (ω (1, 0) a)) 2 Q → MemLp (fun a => g (ω (1, 0) a)) 2 Q →
      ∀ s s' : Fin n → Bool, Integrable (fun a =>
        (∏ m : Fin n, f (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, g (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a))) Q :=
    fun f g hf hg hf2 hg2 s s' => integrable_two_paths hω f g hf hg hf2 hg2 s s'
  have hφφ := hI φ φ hφ hφ hφ2 hφ2
  have hφψ := hI φ ψ hφ hψ hφ2 hψ2
  have hψφ := hI ψ φ hψ hφ hψ2 hφ2
  have hψψ := hI ψ ψ hψ hψ hψ2 hψ2
  simp only [hΦ, hΨ] at hpt
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  have H1 : ∀ s s' : Fin n → Bool, Integrable (fun a =>
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) -
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a))) Q :=
    fun s s' => (hφφ s s').sub (hφψ s s')
  have H2 : ∀ s s' : Fin n → Bool, Integrable (fun a =>
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) -
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) -
      (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a))) Q :=
    fun s s' => (H1 s s').sub (hψφ s s')
  have H3 : ∀ s s' : Fin n → Bool, Integrable (fun a =>
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) -
      (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) -
      (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a)) +
      (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) *
        (∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s' ((m : ℕ) + 1)) a))) Q :=
    fun s s' => (H2 s s').add (hψψ s s')
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun s' _ => H3 s s'))]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [integral_finsetSum _ (fun s' _ => H3 s s')]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [integral_add (H2 s s') (hψψ s s'), integral_sub (H1 s s') (hψφ s s'),
    integral_sub (hφφ s s') (hφψ s s'),
    integral_two_paths hω φ φ hφ hφ hφ1 hφ1, integral_two_paths hω φ ψ hφ hψ hφ1 hψ1,
    integral_two_paths hω ψ φ hψ hφ hψ1 hφ1, integral_two_paths hω ψ ψ hψ hψ hψ1 hψ1]


lemma abs_exp_sub_one_sub_le' (y : ℝ) : |Real.exp y - 1 - y| ≤ y ^ 2 * (1 + Real.exp y) := by
  have hpos : 0 ≤ Real.exp y - 1 - y := by linarith [Real.add_one_le_exp y]
  rcases le_or_gt (|y|) 1 with h | h
  · refine (Real.abs_exp_sub_one_sub_id_le h).trans ?_
    have : 0 ≤ y ^ 2 * Real.exp y := by positivity
    nlinarith
  · rw [abs_of_nonneg hpos]
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h
      have : 1 ≤ y ^ 2 := by nlinarith
      have he := Real.exp_pos y
      nlinarith
    · rw [abs_of_neg hy] at h
      have : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy.le
      have he := Real.exp_pos y
      nlinarith

lemma abs_exp_sub_one_le' (y : ℝ) : |Real.exp y - 1| ≤ |y| * (1 + Real.exp y) := by
  rcases le_or_gt 0 y with hy | hy
  · have h1 : 0 ≤ Real.exp y - 1 := by linarith [Real.add_one_le_exp y]
    rw [abs_of_nonneg h1, abs_of_nonneg hy]
    have h2 := Real.add_one_le_exp (-y)
    have h3 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    have he := Real.exp_pos y
    nlinarith
  · have h1 : Real.exp y - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr hy.le]
    rw [abs_of_nonpos h1, abs_of_neg hy]
    have h2 := Real.add_one_le_exp y
    have he := Real.exp_pos y
    nlinarith

lemma exp_mul_le_one_add {β β₁ x : ℝ} (hβ : 0 ≤ β) (h : β ≤ β₁) :
    Real.exp (β * x) ≤ 1 + Real.exp (β₁ * x) := by
  rcases le_or_gt 0 x with hx | hx
  · have : Real.exp (β * x) ≤ Real.exp (β₁ * x) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h hx)
    linarith
  · have : Real.exp (β * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith [Real.exp_pos (β₁ * x)]

lemma sq_mul_exp_le {δ β₁ x : ℝ} (hδ : 0 < δ) (hβ₁ : 0 ≤ β₁) :
    x ^ 2 * Real.exp (β₁ * x) ≤ x ^ 2 + 2 / δ ^ 2 * Real.exp ((β₁ + δ) * x) := by
  rcases le_or_gt x 0 with hx | hx
  · have : Real.exp (β₁ * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h0 : 0 ≤ 2 / δ ^ 2 * Real.exp ((β₁ + δ) * x) := by positivity
    have : x ^ 2 * Real.exp (β₁ * x) ≤ x ^ 2 := by
      have := sq_nonneg x
      nlinarith
    linarith
  · have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ δ * x by positivity)
    have hx2 : x ^ 2 ≤ 2 / δ ^ 2 * Real.exp (δ * x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [Real.exp_pos (δ * x), mul_pos hδ hx]
    have he : Real.exp ((β₁ + δ) * x) = Real.exp (δ * x) * Real.exp (β₁ * x) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have hp := Real.exp_pos (β₁ * x)
    nlinarith [mul_le_mul_of_nonneg_right hx2 hp.le, sq_nonneg x]

lemma eventually_small (x : ℝ) :
    ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < β ∧ |β * x| ≤ 1 := by
  have hpos : (0 : ℝ) < 1 / (|x| + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with β hβ
  refine ⟨hβ.1, ?_⟩
  rw [abs_mul, abs_of_pos hβ.1]
  have h1 : β * (|x| + 1) < 1 := by
    have := hβ.2
    rw [lt_div_iff₀ (by positivity)] at this
    exact this
  nlinarith [abs_nonneg x]

lemma tendsto_F (x : ℝ) :
    Tendsto (fun β : ℝ => (Real.exp (β * x) - 1 - β * x) / β ^ 2) (𝓝[>] 0) (𝓝 (x ^ 2 / 2)) := by
  have hlim : Tendsto (fun β : ℝ => β * |x| ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun β : ℝ => β * |x| ^ 3) (𝓝 0) (𝓝 (0 * |x| ^ 3)) :=
      (continuous_id.mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_small x] with β ⟨hβ, hy⟩
  have hb := Real.exp_bound hy (show 0 < 3 by norm_num)
  have hs : ∑ m ∈ Finset.range 3, (β * x) ^ m / (m.factorial : ℝ) = 1 + β * x + (β * x) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hb
  have hβ2 : 0 < β ^ 2 := by positivity
  have key : (Real.exp (β * x) - 1 - β * x) / β ^ 2 - x ^ 2 / 2 =
      (Real.exp (β * x) - (1 + β * x + (β * x) ^ 2 / 2)) / β ^ 2 := by
    field_simp
    ring
  rw [Real.norm_eq_abs, key, abs_div, abs_of_pos hβ2, div_le_iff₀ hβ2]
  have hb' : |Real.exp (β * x) - (1 + β * x + (β * x) ^ 2 / 2)| ≤ |β * x| ^ 3 := by
    refine hb.trans ?_
    apply mul_le_of_le_one_right (by positivity)
    norm_num [Nat.factorial]
  calc _ ≤ |β * x| ^ 3 := hb'
    _ = β * |x| ^ 3 * β ^ 2 := by rw [abs_mul, abs_of_pos hβ]; ring

lemma tendsto_G (x : ℝ) :
    Tendsto (fun β : ℝ => x * (Real.exp (β * x) - 1) / β) (𝓝[>] 0) (𝓝 (x ^ 2)) := by
  have hlim : Tendsto (fun β : ℝ => β * |x| ^ 3) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun β : ℝ => β * |x| ^ 3) (𝓝 0) (𝓝 (0 * |x| ^ 3)) :=
      (continuous_id.mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_small x] with β ⟨hβ, hy⟩
  have hb := Real.abs_exp_sub_one_sub_id_le hy
  have key : x * (Real.exp (β * x) - 1) / β - x ^ 2 = x * (Real.exp (β * x) - 1 - β * x) / β := by
    field_simp
  rw [Real.norm_eq_abs, key, abs_div, abs_mul, abs_of_pos hβ, div_le_iff₀ hβ]
  calc |x| * |Real.exp (β * x) - 1 - β * x| ≤ |x| * (β * x) ^ 2 :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg x)
    _ = β * |x| ^ 3 * β := by
        have : (β * x) ^ 2 = β ^ 2 * |x| ^ 2 := by rw [mul_pow, sq_abs]
        rw [this]; ring

/-- D3: small-β behaviour of the moment generating function under one-sided exponential
moments. -/
theorem mgf_small {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (hX : Measurable X) (h2 : MemLp X 2 Q) (hmean : ∫ a, X a ∂Q = 0)
    (hvar : ∫ a, X a ^ 2 ∂Q = 1) (β₀ : ℝ) (hβ₀ : 0 < β₀)
    (hexp : ∀ b : ℝ, 0 < b → b < β₀ → Integrable (fun a => Real.exp (b * X a)) Q) :
    Tendsto (fun β => (mgf X Q β - 1) / β ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) ∧
      Tendsto (fun β => (∫ a, X a * Real.exp (β * X a) ∂Q) / β) (𝓝[>] 0) (𝓝 1) := by
  set β₁ := β₀ / 2 with hβ₁
  set δ := β₀ / 4 with hδ
  have hδp : 0 < δ := by positivity
  have hβ₁p : 0 ≤ β₁ := by positivity
  have hint_sq : Integrable (fun a => X a ^ 2) Q := h2.integrable_sq
  have hintX : Integrable X Q := h2.integrable one_le_two
  have hintE : Integrable (fun a => Real.exp ((β₁ + δ) * X a)) Q :=
    hexp _ (by positivity) (by rw [hβ₁, hδ]; linarith)
  set bound : Ω → ℝ := fun a => 3 * X a ^ 2 + 2 / δ ^ 2 * Real.exp ((β₁ + δ) * X a) with hbd
  have hbound_int : Integrable bound Q :=
    (hint_sq.const_mul 3).add (hintE.const_mul _)
  -- pointwise domination
  have hdom : ∀ β : ℝ, 0 < β → β ≤ β₁ → ∀ x : ℝ,
      x ^ 2 * (1 + Real.exp (β * x)) ≤ 3 * x ^ 2 + 2 / δ ^ 2 * Real.exp ((β₁ + δ) * x) := by
    intro β hβ hββ x
    have h1 := exp_mul_le_one_add (x := x) hβ.le hββ
    have h2' := sq_mul_exp_le (x := x) hδp hβ₁p
    have := sq_nonneg x
    nlinarith
  have hsmall : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < β ∧ β ≤ β₁ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < β₁ by positivity)] with β hβ
    exact ⟨hβ.1, hβ.2.le⟩
  have hlt : ∀ β : ℝ, β ≤ β₁ → β < β₀ := fun β h => by rw [hβ₁] at h; linarith
  constructor
  · -- first limit
    have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := Q) (l := 𝓝[>] (0 : ℝ))
      (F := fun β a => (Real.exp (β * X a) - 1 - β * X a) / β ^ 2) (f := fun a => X a ^ 2 / 2)
      bound
      (Eventually.of_forall fun β => (by fun_prop : Measurable fun a =>
        (Real.exp (β * X a) - 1 - β * X a) / β ^ 2).aestronglyMeasurable)
      (by
        filter_upwards [hsmall] with β ⟨hβ, hββ⟩
        refine Eventually.of_forall fun a => ?_
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < β ^ 2),
          div_le_iff₀ (by positivity)]
        calc |Real.exp (β * X a) - 1 - β * X a| ≤ (β * X a) ^ 2 * (1 + Real.exp (β * X a)) :=
              abs_exp_sub_one_sub_le' _
          _ = β ^ 2 * (X a ^ 2 * (1 + Real.exp (β * X a))) := by ring
          _ ≤ β ^ 2 * bound a := by
              gcongr
              exact hdom β hβ hββ (X a)
          _ = bound a * β ^ 2 := by ring)
      hbound_int
      (Eventually.of_forall fun a => tendsto_F (X a))
    have hlim : ∫ a, X a ^ 2 / 2 ∂Q = 1 / 2 := by rw [integral_div, hvar]
    rw [hlim] at hDCT
    refine hDCT.congr' ?_
    filter_upwards [hsmall] with β ⟨hβ, hββ⟩
    have hiE := hexp β hβ (hlt β hββ)
    have hi1 : Integrable (fun a => Real.exp (β * X a) - 1) Q := hiE.sub (integrable_const 1)
    have hi2 : Integrable (fun a => β * X a) Q := hintX.const_mul β
    rw [integral_div, integral_sub hi1 hi2, integral_sub hiE (integrable_const 1),
      integral_const_mul, hmean]
    simp [mgf]
  · -- second limit
    have hGint : ∀ β : ℝ, 0 < β → β ≤ β₁ →
        Integrable (fun a => X a * (Real.exp (β * X a) - 1) / β) Q := by
      intro β hβ hββ
      refine Integrable.mono' hbound_int (by fun_prop) (Eventually.of_forall fun a => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hβ, div_le_iff₀ hβ]
      calc |X a| * |Real.exp (β * X a) - 1| ≤ |X a| * (|β * X a| * (1 + Real.exp (β * X a))) :=
            mul_le_mul_of_nonneg_left (abs_exp_sub_one_le' _) (abs_nonneg _)
        _ = β * (X a ^ 2 * (1 + Real.exp (β * X a))) := by
            rw [abs_mul, abs_of_pos hβ]
            have : |X a| * |X a| = X a ^ 2 := by rw [← sq, sq_abs]
            linear_combination (β * (1 + Real.exp (β * X a))) * this
        _ ≤ β * bound a := by
            gcongr
            exact hdom β hβ hββ (X a)
        _ = bound a * β := by ring
    have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := Q) (l := 𝓝[>] (0 : ℝ))
      (F := fun β a => X a * (Real.exp (β * X a) - 1) / β) (f := fun a => X a ^ 2)
      bound
      (Eventually.of_forall fun β => (by fun_prop : Measurable fun a =>
        X a * (Real.exp (β * X a) - 1) / β).aestronglyMeasurable)
      (by
        filter_upwards [hsmall] with β ⟨hβ, hββ⟩
        refine Eventually.of_forall fun a => ?_
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hβ, div_le_iff₀ hβ]
        calc |X a| * |Real.exp (β * X a) - 1| ≤ |X a| * (|β * X a| * (1 + Real.exp (β * X a))) :=
              mul_le_mul_of_nonneg_left (abs_exp_sub_one_le' _) (abs_nonneg _)
          _ = β * (X a ^ 2 * (1 + Real.exp (β * X a))) := by
              rw [abs_mul, abs_of_pos hβ]
              have : |X a| * |X a| = X a ^ 2 := by rw [← sq, sq_abs]
              linear_combination (β * (1 + Real.exp (β * X a))) * this
          _ ≤ β * bound a := by
              gcongr
              exact hdom β hβ hββ (X a)
          _ = bound a * β := by ring)
      hbound_int
      (Eventually.of_forall fun a => tendsto_G (X a))
    rw [hvar] at hDCT
    refine hDCT.congr' ?_
    filter_upwards [hsmall] with β ⟨hβ, hββ⟩
    have hG := hGint β hβ hββ
    have hXE : Integrable (fun a => X a * Real.exp (β * X a)) Q := by
      have := (hG.const_mul β).add hintX
      refine this.congr (Eventually.of_forall fun a => ?_)
      have hβ0 : β ≠ 0 := hβ.ne'
      simp only [Pi.add_apply]
      field_simp
      ring
    have : ∀ a, X a * (Real.exp (β * X a) - 1) / β = (X a * Real.exp (β * X a) - X a) / β := by
      intro a; ring
    simp_rw [this]
    rw [integral_div, integral_sub hXE hintX, hmean, sub_zero]


lemma integrable_X_mul_exp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (hX : Measurable X) (h2 : MemLp X 2 Q) (β₀ : ℝ) (hβ₀ : 0 < β₀)
    (hexp : ∀ b : ℝ, 0 < b → b < β₀ → Integrable (fun a => Real.exp (b * X a)) Q)
    (b : ℝ) (hb : 0 < b) (hb' : b ≤ β₀ / 2) :
    Integrable (fun a => X a * Real.exp (b * X a)) Q := by
  have hδ : (0 : ℝ) < β₀ / 4 := by positivity
  have hE := hexp b hb (by linarith)
  have hE2 := hexp (b + β₀ / 4) (by positivity) (by linarith)
  have hsq := h2.integrable_sq
  refine Integrable.mono' ((hE.add hsq).add (hE2.const_mul (2 / (β₀ / 4) ^ 2))) (by fun_prop)
    (Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := sq_mul_exp_le (x := X a) hδ hb.le
  have h3 : |X a| ≤ 1 + X a ^ 2 := by
    nlinarith [abs_nonneg (X a), sq_abs (X a), sq_nonneg (|X a| - 1)]
  have hp := Real.exp_pos (b * X a)
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]

lemma tendsto_sq_nhdsGT : Tendsto (fun b : ℝ => b ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun b : ℝ => b ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

lemma ratio_limits {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (hX : Measurable X) (h2 : MemLp X 2 Q) (hmean : ∫ a, X a ∂Q = 0)
    (hvar : ∫ a, X a ^ 2 ∂Q = 1) (β₀ : ℝ) (hβ₀ : 0 < β₀)
    (hexp : ∀ b : ℝ, 0 < b → b < β₀ → Integrable (fun a => Real.exp (b * X a)) Q) :
    Tendsto (fun b => (mgf X Q (2 * b) / mgf X Q b ^ 2 - 1) / b ^ 2) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun b => ((1 + b * (∫ a, X a * Real.exp (b * X a) ∂Q) / mgf X Q b) - 1) / b ^ 2)
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨T1, T2⟩ := mgf_small X hX h2 hmean hvar β₀ hβ₀ hexp
  have h2b : Tendsto (fun b : ℝ => 2 * b) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun b : ℝ => 2 * b) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with b hb
      exact mul_pos two_pos (Set.mem_Ioi.mp hb)
  have T1' := T1.comp h2b
  have hsq := tendsto_sq_nhdsGT
  have hM : Tendsto (fun b => 1 + b ^ 2 * ((mgf X Q b - 1) / b ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hsq.mul T1)
  have hsmall : ∀ᶠ b in 𝓝[>] (0 : ℝ), 0 < b ∧ b < β₀ / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < β₀ / 2 by positivity)] with b hb
    exact ⟨hb.1, hb.2⟩
  constructor
  · have hlim := ((((tendsto_const_nhds (x := (4 : ℝ))).mul T1').sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul T1)).sub (hsq.mul (T1.pow 2))).div (hM.pow 2)
      (by norm_num)
    have hval : (4 * (1 / 2) - 2 * (1 / 2) - 0 * (1 / 2) ^ 2) / (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [hsmall] with b ⟨hb, hbβ⟩
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hM0 : mgf X Q b ≠ 0 := (mgf_pos (hexp b hb (by linarith))).ne'
    have e1 : 1 + b ^ 2 * ((mgf X Q b - 1) / b ^ 2) = mgf X Q b := by field_simp; ring
    simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    rw [e1]
    field_simp
    ring
  · have hlim := T2.div hM (by norm_num)
    rw [div_one] at hlim
    refine hlim.congr' ?_
    filter_upwards [hsmall] with b ⟨hb, hbβ⟩
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hM0 : mgf X Q b ≠ 0 := (mgf_pos (hexp b hb (by linarith))).ne'
    have e1 : 1 + b ^ 2 * ((mgf X Q b - 1) / b ^ 2) = mgf X Q b := by field_simp; ring
    simp only [Pi.div_apply]
    rw [e1]
    field_simp
    ring

lemma pow_sub_pow_bound (c r : ℝ) (hc : 0 ≤ c) (hr : |r - 1| ≤ 1) (L : ℕ) :
    |(1 + c * r) ^ L - (1 + c) ^ L| ≤ |r - 1| * Real.exp (3 * c * L) := by
  have hr' := abs_le.mp hr
  have hr0 : 0 ≤ r := by linarith
  have hr2 : r ≤ 2 := by linarith
  have h := abs_pow_sub_pow_le (a := 1 + c * r) (b := 1 + c) (n := L)
  have hmax : max |1 + c * r| |1 + c| ≤ 1 + 2 * c := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact max_le (by nlinarith) (by linarith)
  have hdiff : |1 + c * r - (1 + c)| = c * |r - 1| := by
    rw [show 1 + c * r - (1 + c) = c * (r - 1) by ring, abs_mul, abs_of_nonneg hc]
  have hpow : max |1 + c * r| |1 + c| ^ (L - 1) ≤ Real.exp (2 * c * L) := by
    calc max |1 + c * r| |1 + c| ^ (L - 1) ≤ (1 + 2 * c) ^ (L - 1) :=
          pow_le_pow_left₀ (by positivity) hmax _
      _ ≤ (1 + 2 * c) ^ L := pow_le_pow_right₀ (by linarith) (Nat.sub_le L 1)
      _ ≤ Real.exp (2 * c) ^ L :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * c)]) _
      _ = Real.exp (2 * c * L) := by rw [← Real.exp_nat_mul]; ring_nf
  have hcL : c * L ≤ Real.exp (c * L) := by linarith [Real.add_one_le_exp (c * L)]
  calc |(1 + c * r) ^ L - (1 + c) ^ L|
      ≤ |1 + c * r - (1 + c)| * L * max |1 + c * r| |1 + c| ^ (L - 1) := h
    _ = |r - 1| * (c * L) * max |1 + c * r| |1 + c| ^ (L - 1) := by rw [hdiff]; ring
    _ ≤ |r - 1| * Real.exp (c * L) * Real.exp (2 * c * L) := by
        gcongr
    _ = |r - 1| * Real.exp (3 * c * L) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma rpow_quarter_pow_four (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 * n = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_mul_natCast hn0.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

/-- D4: the L² comparison between the normalised and the modified partition function. -/
theorem partitionFunction_sub_modified_sq_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => ∫ a,
        (Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a -
          modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a) ^ 2 ∂Q)
      atTop (𝓝 0) := by
  classical
  obtain ⟨β₀, hβ₀, hexp⟩ := hexp
  set X := ω (1, 0) with hXdef
  have hXm : Measurable X := hω.measurable _
  have h2 : MemLp X 2 Q := hω.memLp_two
  have hmean : ∫ a, X a ∂Q = 0 := hω.mean_zero
  have hvar : ∫ a, X a ^ 2 ∂Q = 1 := hω.second_moment
  obtain ⟨TA, TB⟩ := ratio_limits X hXm h2 hmean hvar β₀ hβ₀ hexp
  set rA : ℝ → ℝ := fun b => (mgf X Q (2 * b) / mgf X Q b ^ 2 - 1) / b ^ 2 with hrA
  set rB : ℝ → ℝ := fun b =>
    ((1 + b * (∫ a, X a * Real.exp (b * X a) ∂Q) / mgf X Q b) - 1) / b ^ 2 with hrB
  set bn : ℕ → ℝ := fun n => β * (n : ℝ) ^ (-(1 / 4 : ℝ)) with hbn
  have hbn0 : Tendsto bn atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have := (h1.comp tendsto_natCast_atTop_atTop).const_mul β
    simpa [hbn] using this
  have hbnpos : ∀ n : ℕ, 1 ≤ n → 0 < bn n := by
    intro n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos hβ (Real.rpow_pos_of_pos this _)
  have hbn_tend : Tendsto bn atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hbn0, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbnpos n hn
  set η : ℕ → ℝ := fun n => max |rA (bn n) - 1| |rB (bn n) - 1| with hη
  have hηt : Tendsto η atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => |rA (bn n) - 1|) atTop (𝓝 0) := by
      have := ((TA.comp hbn_tend).sub_const 1).abs
      simpa using this
    have h2' : Tendsto (fun n => |rB (bn n) - 1|) atTop (𝓝 0) := by
      have := ((TB.comp hbn_tend).sub_const 1).abs
      simpa using this
    simpa using h1.max h2'
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ bn n < β₀ / 2 ∧ η n ≤ 1 := by
    have e1 := eventually_ge_atTop 1
    have e2 := hbn0.eventually (gt_mem_nhds (show (0 : ℝ) < β₀ / 2 by positivity))
    have e3 := hηt.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [e1, e2, e3] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set K : ℝ := 6 * Real.exp (36 * β ^ 4) with hK
  refine squeeze_zero_norm' ?_ (by simpa using hηt.const_mul K)
  filter_upwards [hev] with n ⟨hn1, hbβ, hη1⟩
  -- fix n
  set b := bn n with hbdef
  have hb0 : 0 < b := hbnpos n hn1
  have hiE : Integrable (fun a => Real.exp (b * X a)) Q := hexp b hb0 (by linarith)
  have hiE2 : Integrable (fun a => Real.exp ((2 * b) * X a)) Q := hexp (2 * b) (by positivity)
    (by linarith)
  have hiXE := integrable_X_mul_exp X hXm h2 β₀ hβ₀ hexp b hb0 hbβ.le
  have hintX : Integrable X Q := h2.integrable one_le_two
  set M := mgf X Q b with hMdef
  have hM : 0 < M := mgf_pos hiE
  set lam := cgf X Q b with hlam
  have hexpl : Real.exp lam = M := by rw [hlam, cgf, Real.exp_log hM]
  set φ : ℝ → ℝ := fun x => Real.exp (b * x - lam) with hφdef
  set ψ : ℝ → ℝ := fun x => 1 + b * x with hψdef
  have hφm : Measurable φ := by fun_prop
  have hψm : Measurable ψ := by fun_prop
  have hφx : ∀ x, φ x = Real.exp (b * x) / M := by
    intro x; rw [hφdef]; simp only; rw [Real.exp_sub, hexpl]
  have hφ2 : MemLp (fun a => φ (X a)) 2 Q := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have : (fun a => φ (X a) ^ 2) = fun a => Real.exp ((2 * b) * X a) / M ^ 2 := by
      funext a; rw [hφx, div_pow, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact hiE2.div_const _
  have hψ2 : MemLp (fun a => ψ (X a)) 2 Q := by
    have := (memLp_const (1 : ℝ)).add (h2.const_mul b)
    exact this
  have hφ1 : ∫ a, φ (X a) ∂Q = 1 := by
    simp_rw [hφx]
    rw [integral_div]
    change mgf X Q b / M = 1
    exact div_self hM.ne'
  have hψ1 : ∫ a, ψ (X a) ∂Q = 1 := by
    simp only [hψdef]
    rw [integral_add (integrable_const 1) (hintX.const_mul b), integral_const_mul, hmean]
    simp
  -- rewrite the integrand
  have hY : ∀ a, Real.exp (-(n : ℝ) * lam) * partitionFunction ω n b a =
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) := by
    intro a
    unfold partitionFunction energy
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [← Real.exp_add]
    simp only [hφdef]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hZ : ∀ a, modifiedPartitionFunction ω n b a =
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) := fun a => rfl
  have hcongr : (fun a => (Real.exp (-(n : ℝ) * lam) * partitionFunction ω n b a -
      modifiedPartitionFunction ω n b a) ^ 2) = fun a =>
      (((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) -
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, ψ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) ^ 2 := by
    funext a; rw [hY, hZ]
  rw [hcongr, second_moment_diff hω φ ψ hφm hψm hφ2 hψ2 hφ1 hψ1 n]
  -- the four second moments
  have hAA : ∫ a, φ (X a) * φ (X a) ∂Q = 1 + b ^ 2 * rA b := by
    have : (fun a => φ (X a) * φ (X a)) = fun a => Real.exp ((2 * b) * X a) / M ^ 2 := by
      funext a; rw [hφx, div_mul_div_comm, ← Real.exp_add, sq]; ring_nf
    rw [this, integral_div]
    change mgf X Q (2 * b) / M ^ 2 = _
    simp only [hrA]
    rw [← hMdef]
    have hb0' : b ≠ 0 := hb0.ne'
    have hM0 : M ≠ 0 := hM.ne'
    field_simp
    ring
  have hAB : ∫ a, φ (X a) * ψ (X a) ∂Q = 1 + b ^ 2 * rB b := by
    have : (fun a => φ (X a) * ψ (X a)) =
        fun a => (Real.exp (b * X a) + b * (X a * Real.exp (b * X a))) / M := by
      funext a; rw [hφx]; simp only [hψdef]; ring
    rw [this, integral_div, integral_add hiE (hiXE.const_mul b), integral_const_mul]
    change (M + b * ∫ a, X a * Real.exp (b * X a) ∂Q) / M = _
    simp only [hrB]
    rw [← hMdef]
    have hb0' : b ≠ 0 := hb0.ne'
    have hM0 : M ≠ 0 := hM.ne'
    field_simp
    ring
  have hBA : ∫ a, ψ (X a) * φ (X a) ∂Q = 1 + b ^ 2 * rB b := by
    simp_rw [mul_comm (ψ _) (φ _)]
    exact hAB
  have hCC : ∫ a, ψ (X a) * ψ (X a) ∂Q = 1 + b ^ 2 := by
    have : (fun a => ψ (X a) * ψ (X a)) = fun a => 1 + (2 * b) * X a + b ^ 2 * X a ^ 2 := by
      funext a; simp only [hψdef]; ring
    have i1 : Integrable (fun a => (1 : ℝ) + 2 * b * X a) Q :=
      (integrable_const 1).add (hintX.const_mul _)
    have i2 : Integrable (fun a => b ^ 2 * X a ^ 2) Q := h2.integrable_sq.const_mul _
    rw [this, integral_add i1 i2, integral_add (integrable_const 1) (hintX.const_mul _),
      integral_const_mul, integral_const_mul, hmean, hvar]
    simp
  rw [hAA, hAB, hBA, hCC]
  -- bound each term
  set c : ℝ := b ^ 2 with hc
  have hc0 : 0 ≤ c := sq_nonneg b
  have hηA : |rA b - 1| ≤ η n := le_max_left _ _
  have hηB : |rB b - 1| ≤ η n := le_max_right _ _
  have hterm : ∀ L : ℕ, |(1 + c * rA b) ^ L - (1 + c * rB b) ^ L - (1 + c * rB b) ^ L +
      (1 + c) ^ L| ≤ 3 * η n * Real.exp ((3 * c) * L) := by
    intro L
    have h1 := abs_le.mp ((pow_sub_pow_bound c (rA b) hc0 (hηA.trans hη1) L).trans
      (mul_le_mul_of_nonneg_right hηA (Real.exp_pos _).le))
    have h2'' := abs_le.mp ((pow_sub_pow_bound c (rB b) hc0 (hηB.trans hη1) L).trans
      (mul_le_mul_of_nonneg_right hηB (Real.exp_pos _).le))
    have he : Real.exp (3 * c * L) = Real.exp ((3 * c) * L) := by ring_nf
    rw [he] at h1 h2''
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2''.1, h2''.2]
  have hsum := overlap_exp_le (3 * c) (by positivity) n
  have h4n : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hb4 : b ^ 4 * n = β ^ 4 := by
    rw [hbdef, hbn]
    simp only
    rw [mul_pow, mul_assoc, rpow_quarter_pow_four n hn1, mul_one]
  have hfin : ((4 : ℝ) ^ n)⁻¹ * (2 * (4 * Real.exp (4 * (3 * c) ^ 2)) ^ n) =
      2 * Real.exp (36 * β ^ 4) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (n : ℝ) * (4 * (3 * c) ^ 2) = 36 * β ^ 4 := by
      rw [← hb4, hc]; ring
    rw [this]
    field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr h4n)]
  calc _
      ≤ ((4 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
          3 * η n * Real.exp ((3 * c) * (ovl s s' : ℝ)) := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        gcongr with s _
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        gcongr with s' _
        exact hterm (ovl s s')
    _ = 3 * η n * (((4 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∑ s' : Fin n → Bool,
          Real.exp ((3 * c) * (ovl s s' : ℝ))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun s' _ => by ring))
    _ ≤ 3 * η n * (((4 : ℝ) ^ n)⁻¹ * (2 * (4 * Real.exp (4 * (3 * c) ^ 2)) ^ n)) := by
        have : 0 ≤ η n := le_trans (abs_nonneg _) hηA
        gcongr
    _ = K * η n := by rw [hfin, hK]; ring

lemma phi_facts {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (hXm : Measurable X) (b : ℝ)
    (hiE : Integrable (fun a => Real.exp (b * X a)) Q)
    (hiE2 : Integrable (fun a => Real.exp ((2 * b) * X a)) Q) :
    MemLp (fun a => Real.exp (b * X a - cgf X Q b)) 2 Q ∧
      ∫ a, Real.exp (b * X a - cgf X Q b) ∂Q = 1 := by
  have hM : 0 < mgf X Q b := mgf_pos hiE
  have hexpl : Real.exp (cgf X Q b) = mgf X Q b := by rw [cgf, Real.exp_log hM]
  have hφx : ∀ x, Real.exp (b * x - cgf X Q b) = Real.exp (b * x) / mgf X Q b := by
    intro x; rw [Real.exp_sub, hexpl]
  constructor
  · rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have : (fun a => Real.exp (b * X a - cgf X Q b) ^ 2) =
        fun a => Real.exp ((2 * b) * X a) / mgf X Q b ^ 2 := by
      funext a; rw [hφx, div_pow, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    exact hiE2.div_const _
  · simp_rw [hφx]
    rw [integral_div]
    change mgf X Q b / mgf X Q b = 1
    exact div_self hM.ne'

lemma partitionFunction_eq_prod {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) (n : ℕ) (b lam : ℝ) (a : Ω) :
    Real.exp (-(n : ℝ) * lam) * partitionFunction ω n b a =
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, Real.exp (b * ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a - lam) := by
  unfold partitionFunction energy
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma memLp_path {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφ2 : MemLp (fun a => φ (ω (1, 0) a)) 2 Q)
    {n : ℕ} (s : Fin n → Bool) :
    MemLp (fun a => ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) 2 Q := by
  have hm : Measurable (fun a => ∏ m : Fin n, φ (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a)) :=
    Finset.measurable_prod _ (fun m _ => hφ.comp (hω.measurable _))
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have := integrable_two_paths hω φ φ hφ hφ hφ2 hφ2 s s
  simpa [sq] using this

lemma eLpNorm_tendsto_of_integral_sq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (f : ℕ → Ω → ℝ) (hmem : ∀ᶠ n in atTop, MemLp (f n) 2 Q)
    (h : Tendsto (fun n => ∫ a, f n a ^ 2 ∂Q) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 Q) atTop (𝓝 0) := by
  have key : ∀ᶠ n in atTop, ENNReal.ofReal ((∫ a, f n a ^ 2 ∂Q) ^ (2 : ℝ)⁻¹) =
      eLpNorm (f n) 2 Q := by
    filter_upwards [hmem] with n hn
    rw [hn.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have h2 : Tendsto (fun n => (∫ a, f n a ^ 2 ∂Q) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
    have := h.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    simpa using this
  have h3 := (ENNReal.tendsto_ofReal h2)
  rw [ENNReal.ofReal_zero] at h3
  exact h3.congr' key

/-- D4 (L² form): the normalised partition function minus the modified one tends to `0` in
`L²(Q)`. -/
theorem partitionFunction_sub_modified_eLpNorm_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => eLpNorm (fun a =>
        Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a -
          modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a) 2 Q)
      atTop (𝓝 0) := by
  classical
  have hsq := partitionFunction_sub_modified_sq_tendsto_zero hω hexp β hβ
  refine eLpNorm_tendsto_of_integral_sq _ ?_ hsq
  obtain ⟨β₀, hβ₀, hexp⟩ := hexp
  have hbn0 : Tendsto (fun n : ℕ => β * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul β
  filter_upwards [eventually_ge_atTop 1,
    hbn0.eventually (gt_mem_nhds (show (0 : ℝ) < β₀ / 2 by positivity))] with n hn1 hbβ
  set b := β * (n : ℝ) ^ (-(1 / 4 : ℝ)) with hbdef
  have hb0 : 0 < b := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact mul_pos hβ (Real.rpow_pos_of_pos this _)
  set X := ω (1, 0) with hXdef
  have hiE : Integrable (fun a => Real.exp (b * X a)) Q := hexp b hb0 (by linarith)
  have hiE2 : Integrable (fun a => Real.exp ((2 * b) * X a)) Q :=
    hexp (2 * b) (by positivity) (by linarith)
  obtain ⟨hφ2, -⟩ := phi_facts X (hω.measurable _) b hiE hiE2
  have hψ2 : MemLp (fun a => 1 + b * X a) 2 Q := (memLp_const (1 : ℝ)).add (hω.memLp_two.const_mul b)
  have hφm : Measurable (fun x : ℝ => Real.exp (b * x - cgf X Q b)) := by fun_prop
  have hψm : Measurable (fun x : ℝ => 1 + b * x) := by fun_prop
  have hfun : (fun a => Real.exp (-(n : ℝ) * cgf X Q b) * partitionFunction ω n b a -
      modifiedPartitionFunction ω n b a) = fun a =>
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, (fun x : ℝ => Real.exp (b * x - cgf X Q b))
          (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) -
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool,
        ∏ m : Fin n, (fun x : ℝ => 1 + b * x) (ω ((m : ℕ) + 1, walkPos s ((m : ℕ) + 1)) a) := by
    funext a
    rw [partitionFunction_eq_prod]
    rfl
  rw [hfun]
  have h1 := (memLp_finsetSum (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun s _ => memLp_path hω _ hφm hφ2 s)).const_mul ((2 : ℝ) ^ n)⁻¹
  have h2 := (memLp_finsetSum (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun s _ => memLp_path hω _ hψm hψ2 s)).const_mul ((2 : ℝ) ^ n)⁻¹
  exact h1.sub h2

end IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter Topology IntermediateDisorder.PointToLine in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => eLpNorm (fun a =>
        Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a -
          modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a) 2 Q)
      atTop (𝓝 0) := by
  exact partitionFunction_sub_modified_eLpNorm_tendsto_zero hω hexp β hβ
