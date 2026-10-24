-- Prove2me | solution 1 for HiringLP.ProbeTopK.proposition_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:39:30.779826+00:00
-- url     : https://prove2.me/submissions/105ceae1-96dd-485d-9e50-5491534a9a04

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank
import Definitions.Def_HiringLP_SimLower_PoissonRatio
import Theorems.Thm_HiringLP_SimLower_proposition_EC_2
import Theorems.Thm_HiringLP_SimLower_expMinPois_div_antitone

set_option autoImplicit false
open Finset HiringLP.SimLower HiringLP.ProbeTopK

namespace PTKAux

/-! ### Poisson pmf -/

noncomputable def pp (x : ℝ) (j : ℕ) : ℝ := Real.exp (-x) * x ^ j / (j.factorial : ℝ)

theorem pp_hasSum (l : ℝ) : HasSum (pp l) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) l).mul_left (Real.exp (-l))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : pp l = fun j : ℕ => Real.exp (-l) * (l ^ j / (j.factorial : ℝ)) := by
    funext j; unfold pp; ring
  rw [e2]; exact h

theorem pp_rec (l : ℝ) (m : ℕ) : ((m + 1 : ℕ) : ℝ) * pp l (m + 1) = l * pp l m := by
  unfold pp
  rw [Nat.factorial_succ]
  push_cast
  have : ((m.factorial : ℝ)) ≠ 0 := by positivity
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pp_nonneg (l : ℝ) (hl : 0 ≤ l) (j : ℕ) : 0 ≤ pp l j := by
  unfold pp; positivity

theorem pp_mean (l : ℝ) : HasSum (fun j : ℕ => (j : ℝ) * pp l j) l := by
  have h := (pp_hasSum l).mul_left l
  rw [mul_one] at h
  have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * pp l (n + 1)) l := by
    have e : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * pp l (n + 1)) = fun n => l * pp l n := by
      funext n; exact pp_rec l n
    rw [e]; exact h
  refine (hasSum_nat_add_iff' (f := fun j : ℕ => (j : ℝ) * pp l j) 1).1 ?_
  simpa using h2

theorem pp_conv (a b : ℝ) (j : ℕ) :
    pp (a + b) j = ∑ i ∈ range (j + 1), pp a i * pp b (j - i) := by
  unfold pp
  rw [add_pow, neg_add, Real.exp_add, mul_sum, sum_div]
  apply sum_congr rfl
  intro m hm
  have hmj : m ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hm)
  have key : ((j.choose m : ℕ) : ℝ) * (m.factorial : ℝ) * ((j - m).factorial : ℝ) =
      (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmj
  have h1 : (m.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((j - m).factorial : ℝ) ≠ 0 := by positivity
  have h3 : ((j.choose m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmj).ne'
  rw [← key]
  field_simp

/-- `F r μ = Σ_{j<r} (r - j) π_μ(j) = E[(r - Pois μ)^+]`. -/
noncomputable def FF (r : ℕ) (μ : ℝ) : ℝ := ∑ j ∈ range r, ((r : ℝ) - j) * pp μ j

theorem FF_conv (r : ℕ) (a b : ℝ) :
    FF r (a + b) = ∑ i ∈ range r, pp a i * FF (r - i) b := by
  unfold FF
  have e1 : ∀ j ∈ range r, ((r : ℝ) - j) * pp (a + b) j =
      ∑ i ∈ range (j + 1), (fun i l => ((r : ℝ) - (i + l)) * (pp a i * pp b l)) i (j - i) := by
    intro j _
    rw [pp_conv, mul_sum]
    apply sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    simp only
    rw [Nat.cast_sub hij]; ring
  rw [sum_congr rfl e1, sum_range_diag_flip r
    (fun i l => ((r : ℝ) - (i + l)) * (pp a i * pp b l))]
  apply sum_congr rfl
  intro i hi
  have hir : i ≤ r := (mem_range.1 hi).le
  rw [mul_sum]
  apply sum_congr rfl
  intro l _
  rw [Nat.cast_sub hir]; ring

theorem hasSum_FF (r : ℕ) (μ : ℝ) :
    HasSum (fun l : ℕ => if l ∈ range r then ((r : ℝ) - l) * pp μ l else 0) (FF r μ) := by
  have h : HasSum (fun l : ℕ => if l ∈ range r then ((r : ℝ) - l) * pp μ l else 0)
      (∑ l ∈ range r, if l ∈ range r then ((r : ℝ) - l) * pp μ l else 0) :=
    hasSum_sum_of_ne_finset_zero (fun l hl => if_neg hl)
  have e : FF r μ = ∑ l ∈ range r, if l ∈ range r then ((r : ℝ) - l) * pp μ l else 0 := by
    unfold FF
    apply sum_congr rfl
    intro l hl; rw [if_pos hl]
  rw [e]; exact h

theorem FF_lower (r : ℕ) (q : ℝ) (hq : 0 ≤ q) : (r : ℝ) - q ≤ FF r q := by
  have hf : HasSum (fun l : ℕ => ((r : ℝ) - l) * pp q l) ((r : ℝ) * 1 - q) := by
    have h := ((pp_hasSum q).mul_left (r : ℝ)).sub (pp_mean q)
    have e : (fun l : ℕ => ((r : ℝ) - l) * pp q l) = fun l => (r : ℝ) * pp q l - l * pp q l := by
      funext l; ring
    rw [e]; exact h
  have hg := hasSum_FF r q
  have := hasSum_le (fun l => ?_) hf hg
  · linarith
  · by_cases hl : l ∈ range r
    · rw [if_pos hl]
    · rw [if_neg hl]
      have : (r : ℝ) ≤ l := by exact_mod_cast (not_lt.1 (fun h => hl (mem_range.2 h)))
      have := pp_nonneg q hq l
      nlinarith

theorem FF_nonneg (r : ℕ) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ FF r q := by
  unfold FF
  apply sum_nonneg
  intro j hj
  have : (j : ℝ) < r := by exact_mod_cast mem_range.1 hj
  have := pp_nonneg q hq j
  nlinarith

theorem FF_upper (r : ℕ) (q : ℝ) (hq : 0 ≤ q) : FF r q ≤ r := by
  unfold FF
  have h1 : ∑ j ∈ range r, ((r : ℝ) - j) * pp q j ≤ ∑ j ∈ range r, (r : ℝ) * pp q j := by
    apply sum_le_sum
    intro j _
    have := pp_nonneg q hq j
    have : (0 : ℝ) ≤ j := by positivity
    nlinarith
  have h2 : ∑ j ∈ range r, pp q j ≤ 1 :=
    sum_le_hasSum (range r) (fun i _ => pp_nonneg q hq i) (pp_hasSum q)
  rw [← mul_sum] at h1
  have : (0 : ℝ) ≤ r := by positivity
  nlinarith

/-- monotonicity of `F` in the mean (decreasing). -/
theorem FF_anti (r : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : FF r (a + b) ≤ FF r a := by
  rw [FF_conv]
  unfold FF
  apply sum_le_sum
  intro i hi
  have hir : i ≤ r := (mem_range.1 hi).le
  have hU := FF_upper (r - i) b hb
  unfold FF at hU
  rw [mul_comm ((r : ℝ) - i), ← Nat.cast_sub hir]
  exact mul_le_mul_of_nonneg_left hU (pp_nonneg a ha i)

theorem FF_pred (m : ℕ) (μ : ℝ) :
    FF m μ = ∑ i ∈ range (m + 1), (((m + 1 : ℕ) : ℝ) - 1 - i) * pp μ i := by
  unfold FF
  rw [sum_range_succ]
  push_cast
  simp

/-- key step: `F(r, μ+q) ≥ (1-q) F(r, μ) + q F(r-1, μ)`. -/
theorem FF_step (r : ℕ) (μ q : ℝ) (hμ : 0 ≤ μ) (hq : 0 ≤ q) :
    (1 - q) * FF r μ + q * FF (r - 1) μ ≤ FF r (μ + q) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [FF]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [FF_conv, show m + 1 - 1 = m by omega, FF_pred m μ]
  unfold FF
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  have hir : i ≤ m + 1 := (mem_range.1 hi).le
  have hL := FF_lower (m + 1 - i) q hq
  rw [Nat.cast_sub hir] at hL
  have := pp_nonneg μ hμ i
  have : pp μ i * (((m + 1 : ℕ) : ℝ) - i - q) ≤ pp μ i * FF (m + 1 - i) q :=
    mul_le_mul_of_nonneg_left hL (pp_nonneg μ hμ i)
  unfold FF at this
  linarith

theorem expMinPois_eq (μ : ℝ) (k : ℕ) : expMinPois μ k = k - FF k μ := by
  have hk : HasSum (fun j : ℕ => (k : ℝ) * pp μ j) ((k : ℝ) * 1) := (pp_hasSum μ).mul_left _
  have hg := hasSum_FF k μ
  have h := hk.sub hg
  have e : (fun j : ℕ => min (j : ℝ) k * (Real.exp (-μ) * μ ^ j / (j.factorial : ℝ))) =
      fun j : ℕ => (k : ℝ) * pp μ j -
        (if j ∈ range k then ((k : ℝ) - j) * pp μ j else 0) := by
    funext j
    unfold pp
    by_cases hj : j ∈ range k
    · rw [if_pos hj]
      have : (j : ℝ) ≤ k := by exact_mod_cast (mem_range.1 hj).le
      rw [min_eq_left this]; ring
    · rw [if_neg hj]
      have : (k : ℝ) ≤ j := by exact_mod_cast (not_lt.1 (fun h => hj (mem_range.2 h)))
      rw [min_eq_right this]; ring
  unfold expMinPois
  rw [e, h.tsum_eq, mul_one]

theorem expMinPois_le (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) : expMinPois μ k ≤ μ := by
  rw [expMinPois_eq]; have := FF_lower k μ hμ; linarith

theorem expMinPois_nonneg (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ expMinPois μ k := by
  rw [expMinPois_eq]; have := FF_upper k μ hμ; linarith

theorem expMinPois_mono (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    expMinPois a k ≤ expMinPois b k := by
  rw [expMinPois_eq, expMinPois_eq]
  have := FF_anti k a (b - a) ha (by linarith)
  rw [add_sub_cancel] at this
  linarith

theorem expMinPois_zero (k : ℕ) : expMinPois 0 k = 0 := by
  have h1 := expMinPois_le 0 le_rfl k
  have h2 := expMinPois_nonneg 0 le_rfl k
  linarith

/-! ### Independent Bernoulli sums -/

section Bern
variable {ι : Type*} [DecidableEq ι]

def WW (q : ι → ℝ) (S A : Finset ι) : ℝ := ∏ i ∈ S, if i ∈ A then q i else 1 - q i

theorem WW_insert (q : ι → ℝ) (a : ι) (S : Finset ι) (ha : a ∉ S) (Φ : Finset ι → ℝ) :
    ∑ A ∈ (insert a S).powerset, WW q (insert a S) A * Φ A =
      (1 - q a) * ∑ A ∈ S.powerset, WW q S A * Φ A +
        q a * ∑ A ∈ S.powerset, WW q S A * Φ (insert a A) := by
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
    unfold WW
    rw [prod_insert ha, if_neg haA]; ring
  · apply sum_congr rfl
    intro A _
    unfold WW
    rw [prod_insert ha, if_pos (mem_insert_self a A)]
    have : ∏ i ∈ S, (if i ∈ insert a A then q i else 1 - q i) =
        ∏ i ∈ S, (if i ∈ A then q i else 1 - q i) := by
      apply prod_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [mem_insert, hia]
    rw [this]; ring

theorem WW_one (q : ι → ℝ) (S : Finset ι) : ∑ A ∈ S.powerset, WW q S A = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [WW]
  | insert a S ha ih =>
    have := WW_insert q a S ha (fun _ => 1)
    simp only [mul_one] at this
    rw [this, ih]; ring

theorem WW_lin (q : ι → ℝ) (f : ι → ℝ) (S : Finset ι) :
    ∑ A ∈ S.powerset, WW q S A * ∑ i ∈ A, f i = ∑ i ∈ S, f i * q i := by
  induction S using Finset.induction_on with
  | empty => simp [WW]
  | insert a S ha ih =>
    rw [WW_insert q a S ha, sum_insert ha]
    have e : ∑ A ∈ S.powerset, WW q S A * ∑ i ∈ insert a A, f i =
        ∑ A ∈ S.powerset, (WW q S A * f a + WW q S A * ∑ i ∈ A, f i) := by
      apply sum_congr rfl
      intro A hA
      have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
      rw [sum_insert haA]; ring
    rw [e, sum_add_distrib, ← sum_mul, WW_one, ih]; ring

theorem WW_min (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) (S : Finset ι) :
    ∀ c : ℕ, (k : ℝ) - FF (k - c) (∑ i ∈ S, q i) ≤
      ∑ A ∈ S.powerset, WW q S A * min ((A.card : ℝ) + c) k := by
  induction S using Finset.induction_on with
  | empty =>
    intro c
    simp only [powerset_empty, sum_singleton, card_empty, sum_empty, WW, prod_empty, one_mul,
      Nat.cast_zero, zero_add]
    have := FF_lower (k - c) 0 le_rfl
    rcases le_total c k with h | h
    · rw [Nat.cast_sub h] at this
      rw [min_eq_left (by exact_mod_cast h)]; linarith
    · rw [Nat.sub_eq_zero_of_le h] at this ⊢
      rw [min_eq_right (by exact_mod_cast h)]
      simp [FF]
  | insert a S ha ih =>
    intro c
    rw [WW_insert q a S ha, sum_insert ha]
    have e : ∑ A ∈ S.powerset, WW q S A * min (((insert a A).card : ℝ) + c) k =
        ∑ A ∈ S.powerset, WW q S A * min ((A.card : ℝ) + ((c + 1 : ℕ) : ℝ)) k := by
      apply sum_congr rfl
      intro A hA
      have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
      rw [card_insert_of_notMem haA]; push_cast; ring_nf
    rw [e]
    have h0 := ih c
    have h1 := ih (c + 1)
    have hqa := hq a
    have hS : 0 ≤ ∑ i ∈ S, q i := sum_nonneg (fun i _ => (hq i).1)
    have hstep := FF_step (k - c) (∑ i ∈ S, q i) (q a) hS hqa.1
    rw [show k - c - 1 = k - (c + 1) by omega] at hstep
    rw [add_comm (q a)]
    have := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ 1 - q a)
    have := mul_le_mul_of_nonneg_left h1 hqa.1
    nlinarith

end Bern

/-! ### Masked Bernoulli bound and the product identity -/

section Mask
variable {ι : Type*} [DecidableEq ι]

theorem WW_min_mask (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) (B : Finset ι)
    (S : Finset ι) :
    ∀ c : ℕ, (k : ℝ) - FF (k - c) (∑ i ∈ S ∩ B, q i) ≤
      ∑ A ∈ S.powerset, WW q S A * min (((A ∩ B).card : ℝ) + c) k := by
  induction S using Finset.induction_on with
  | empty =>
    intro c
    simp only [powerset_empty, sum_singleton, empty_inter, card_empty, sum_empty, WW,
      prod_empty, one_mul, Nat.cast_zero, zero_add]
    have := FF_lower (k - c) 0 le_rfl
    rcases le_total c k with h | h
    · rw [Nat.cast_sub h] at this
      rw [min_eq_left (by exact_mod_cast h)]; linarith
    · rw [Nat.sub_eq_zero_of_le h] at this ⊢
      rw [min_eq_right (by exact_mod_cast h)]
      simp [FF]
  | insert a S ha ih =>
    intro c
    rw [WW_insert q a S ha]
    have hqa := hq a
    by_cases haB : a ∈ B
    · have hsum : ∑ i ∈ insert a S ∩ B, q i = ∑ i ∈ S ∩ B, q i + q a := by
        rw [insert_inter_of_mem haB, sum_insert (fun h => ha (mem_inter.1 h).1), add_comm]
      rw [hsum]
      have e : ∀ A ∈ S.powerset, WW q S A * min ((((insert a A) ∩ B).card : ℝ) + c) k =
          WW q S A * min (((A ∩ B).card : ℝ) + ((c + 1 : ℕ) : ℝ)) k := by
        intro A hA
        have haA : a ∉ A ∩ B := fun h => ha (mem_powerset.1 hA (mem_inter.1 h).1)
        rw [insert_inter_of_mem haB, card_insert_of_notMem haA]; push_cast; ring_nf
      rw [sum_congr rfl e]
      have h0 := ih c
      have h1 := ih (c + 1)
      have hS : 0 ≤ ∑ i ∈ S ∩ B, q i := sum_nonneg (fun i _ => (hq i).1)
      have hstep := FF_step (k - c) (∑ i ∈ S ∩ B, q i) (q a) hS hqa.1
      rw [show k - c - 1 = k - (c + 1) by omega] at hstep
      have := mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ 1 - q a)
      have := mul_le_mul_of_nonneg_left h1 hqa.1
      nlinarith
    · have hsum : ∑ i ∈ insert a S ∩ B, q i = ∑ i ∈ S ∩ B, q i := by
        rw [insert_inter_of_notMem haB]
      rw [hsum]
      have e : ∀ A ∈ S.powerset, WW q S A * min ((((insert a A) ∩ B).card : ℝ) + c) k =
          WW q S A * min (((A ∩ B).card : ℝ) + c) k := by
        intro A _
        rw [insert_inter_of_notMem haB]
      rw [sum_congr rfl e]
      have h0 := ih c
      linarith

theorem WW_double (y p : ι → ℝ) (S : Finset ι) :
    ∀ Φ : Finset ι → ℝ,
    ∑ A ∈ S.powerset, WW y S A * ∑ B ∈ S.powerset, WW p S B * Φ (A ∩ B) =
      ∑ C ∈ S.powerset, WW (fun i => y i * p i) S C * Φ C := by
  induction S using Finset.induction_on with
  | empty => intro Φ; simp [WW]
  | insert a S ha ih =>
    intro Φ
    rw [WW_insert y a S ha (fun A => ∑ B ∈ (insert a S).powerset, WW p (insert a S) B * Φ (A ∩ B)),
      WW_insert (fun i => y i * p i) a S ha]
    have h1 : ∀ A ∈ S.powerset, WW y S A * ∑ B ∈ (insert a S).powerset,
        WW p (insert a S) B * Φ (A ∩ B) = WW y S A * ∑ B ∈ S.powerset, WW p S B * Φ (A ∩ B) := by
      intro A hA
      have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
      rw [WW_insert p a S ha (fun B => Φ (A ∩ B))]
      have : ∀ B, A ∩ insert a B = A ∩ B := fun B => inter_insert_of_notMem haA
      simp only [this]; ring
    have h2 : ∀ A ∈ S.powerset, WW y S A * ∑ B ∈ (insert a S).powerset,
        WW p (insert a S) B * Φ (insert a A ∩ B) =
        (1 - p a) * (WW y S A * ∑ B ∈ S.powerset, WW p S B * Φ (A ∩ B)) +
          p a * (WW y S A * ∑ B ∈ S.powerset, WW p S B * Φ (insert a (A ∩ B))) := by
      intro A hA
      rw [WW_insert p a S ha (fun B => Φ (insert a A ∩ B))]
      have e1 : ∑ B ∈ S.powerset, WW p S B * Φ (insert a A ∩ B) =
          ∑ B ∈ S.powerset, WW p S B * Φ (A ∩ B) := by
        apply sum_congr rfl
        intro B hB
        have haB : a ∉ B := fun h => ha (mem_powerset.1 hB h)
        rw [insert_inter_of_notMem haB]
      have e2 : ∑ B ∈ S.powerset, WW p S B * Φ (insert a A ∩ insert a B) =
          ∑ B ∈ S.powerset, WW p S B * Φ (insert a (A ∩ B)) := by
        apply sum_congr rfl
        intro B _
        rw [← insert_inter_distrib]
      rw [e1, e2]; ring
    rw [sum_congr rfl h1, sum_congr rfl h2, sum_add_distrib, ← mul_sum, ← mul_sum, ih Φ,
      ih (fun C => Φ (insert a C))]
    ring

end Mask

/-! ### Prefixes, the greedy set and summation by parts -/

section Greedy
variable {n : ℕ} (ord : Equiv.Perm (Fin n))

def pre (t : ℕ) : Finset (Fin n) := univ.filter (fun i => ((ord.symm i : Fin n) : ℕ) < t)

def gset (k : ℕ) (D : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i => i ∈ D ∧ (univ.filter fun l => l ∈ D ∧ before ord l i).card < k)

theorem pre_zero : pre ord 0 = ∅ := by
  ext i; simp [pre]

theorem pre_succ (t : ℕ) (ht : t < n) :
    pre ord (t + 1) = insert (ord ⟨t, ht⟩) (pre ord t) ∧ ord ⟨t, ht⟩ ∉ pre ord t := by
  constructor
  · ext i
    simp only [pre, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · left
        have : ord.symm i = ⟨t, ht⟩ := Fin.ext h
        rw [← this, Equiv.apply_symm_apply]
    · rintro (h | h)
      · rw [h, Equiv.symm_apply_apply]; simp
      · omega
  · simp [pre]

theorem pre_of_le (t : ℕ) (ht : n ≤ t) : pre ord t = univ := by
  ext i; simp only [pre, mem_filter, mem_univ, true_and, iff_true]
  have := (ord.symm i).isLt; omega

theorem before_iff_pre (l : Fin n) (t : ℕ) (ht : t < n) :
    before ord l (ord ⟨t, ht⟩) ↔ l ∈ pre ord t := by
  simp only [before, Equiv.symm_apply_apply, pre, mem_filter, mem_univ, true_and, Fin.lt_def]

theorem gset_pre (k : ℕ) (D : Finset (Fin n)) (t : ℕ) :
    (gset ord k D ∩ pre ord t).card = min k (D ∩ pre ord t).card := by
  induction t with
  | zero => simp [pre_zero]
  | succ t ih =>
    by_cases ht : t < n
    · obtain ⟨hpre, hna⟩ := pre_succ ord t ht
      set a : Fin n := ord ⟨t, ht⟩ with ha_def
      have hcount : (univ.filter fun l => l ∈ D ∧ before ord l a) = D ∩ pre ord t := by
        ext l
        simp only [mem_filter, mem_univ, true_and, mem_inter]
        rw [ha_def, before_iff_pre ord l t ht]
      rw [hpre]
      by_cases haD : a ∈ D
      · rw [inter_insert_of_mem haD, card_insert_of_notMem (fun h => hna (mem_inter.1 h).2)]
        by_cases hk : (D ∩ pre ord t).card < k
        · have hag : a ∈ gset ord k D := by
            simp only [gset, mem_filter, mem_univ, true_and]
            exact ⟨haD, by rw [hcount]; exact hk⟩
          rw [inter_insert_of_mem hag, card_insert_of_notMem (fun h => hna (mem_inter.1 h).2), ih]
          omega
        · have hag : a ∉ gset ord k D := by
            simp only [gset, mem_filter, mem_univ, true_and, not_and]
            intro _; rw [hcount]; exact hk
          rw [inter_insert_of_notMem hag, ih]
          omega
      · have hag : a ∉ gset ord k D := by
          simp only [gset, mem_filter, mem_univ, true_and, not_and]
          intro h; exact absurd h haD
        rw [inter_insert_of_notMem hag, inter_insert_of_notMem haD, ih]
    · rw [pre_of_le ord (t + 1) (by omega), ← pre_of_le ord t (by omega), ih]

theorem gset_sub (k : ℕ) (D : Finset (Fin n)) : gset ord k D ⊆ D := by
  intro i hi; simp only [gset, mem_filter] at hi; exact hi.2.1

theorem gset_card (k : ℕ) (D : Finset (Fin n)) : (gset ord k D).card ≤ k := by
  have := gset_pre ord k D n
  rw [pre_of_le ord n le_rfl, inter_univ, inter_univ] at this
  omega

/-- partial sums of `g` along the order equal sums over prefixes -/
theorem range_sum_eq_pre (d : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ t ∈ range m, (if h : t < n then d (ord ⟨t, h⟩) else 0) = ∑ i ∈ pre ord m, d i := by
  induction m with
  | zero => simp [pre_zero]
  | succ m ih =>
    have hm' : m < n := by omega
    obtain ⟨hpre, hna⟩ := pre_succ ord m hm'
    rw [sum_range_succ, ih (by omega), hpre, sum_insert hna, dif_pos hm', add_comm]

theorem abel (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : SortedBy ord w) (α β : Fin n → ℝ)
    (h : ∀ t ≤ n, ∑ i ∈ pre ord t, α i ≤ ∑ i ∈ pre ord t, β i) :
    ∑ i, w i * α i ≤ ∑ i, w i * β i := by
  set d : Fin n → ℝ := fun i => β i - α i with hd
  suffices H : 0 ≤ ∑ i, w i * d i by
    have : ∑ i, w i * d i = ∑ i, w i * β i - ∑ i, w i * α i := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; simp [hd]; ring
    linarith
  set f : ℕ → ℝ := fun t => if h : t < n then w (ord ⟨t, h⟩) else 0 with hf
  set g : ℕ → ℝ := fun t => if h : t < n then d (ord ⟨t, h⟩) else 0 with hg
  have hsum : ∑ i, w i * d i = ∑ t ∈ range n, f t • g t := by
    rw [← Equiv.sum_comp ord, ← Fin.sum_univ_eq_sum_range (fun t => f t • g t)]
    apply sum_congr rfl
    intro t _
    simp [hf, hg, dif_pos t.isLt]
  have hG : ∀ m ≤ n, 0 ≤ ∑ j ∈ range m, g j := by
    intro m hm
    rw [hg, range_sum_eq_pre ord d m hm]
    have := h m hm
    have e : ∑ i ∈ pre ord m, d i = ∑ i ∈ pre ord m, β i - ∑ i ∈ pre ord m, α i := by
      rw [← sum_sub_distrib]
    rw [e]; linarith
  have hf0 : ∀ t, 0 ≤ f t := by
    intro t; simp only [hf]; split_ifs
    · exact hw _
    · exact le_rfl
  have hfanti : ∀ i, i + 1 < n → f (i + 1) ≤ f i := by
    intro i hi
    simp only [hf, dif_pos hi, dif_pos (show i < n by omega)]
    apply hs
    simp [before, Fin.lt_def]
  rw [hsum, sum_range_by_parts]
  have h1 : 0 ≤ f (n - 1) • ∑ j ∈ range n, g j := mul_nonneg (hf0 _) (hG n le_rfl)
  have h2 : ∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j ≤ 0 := by
    apply sum_nonpos
    intro i hi
    have hi' : i + 1 < n := by have := mem_range.1 hi; omega
    have := hfanti i hi'
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hG (i + 1) (by omega))
  linarith

theorem wrank_eq_gset (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : SortedBy ord w) (k : ℕ)
    (D : Finset (Fin n)) : HiringLP.ProbeTopK.wrank w k D = ∑ i ∈ gset ord k D, w i := by
  apply le_antisymm
  · unfold HiringLP.ProbeTopK.wrank
    apply sup'_le
    intro R hR
    simp only [mem_filter, mem_powerset] at hR
    have key := abel ord w hw hs (fun i => if i ∈ R then 1 else 0)
      (fun i => if i ∈ gset ord k D then 1 else 0) (by
        intro t _
        simp only [sum_boole, Nat.cast_le]
        have e1 : (filter (fun i => i ∈ R) (pre ord t)) = R ∩ pre ord t := by
          ext i; simp [and_comm]
        have e2 : (filter (fun i => i ∈ gset ord k D) (pre ord t)) = gset ord k D ∩ pre ord t := by
          ext i; simp [and_comm]
        rw [e1, e2, gset_pre]
        apply le_min
        · exact (card_le_card inter_subset_left).trans hR.2
        · exact card_le_card (inter_subset_inter_right hR.1))
    simp only [mul_ite, mul_one, mul_zero, ← sum_filter] at key
    have e1 : (univ.filter fun i => i ∈ R) = R := by ext; simp
    have e2 : (univ.filter fun i => i ∈ gset ord k D) = gset ord k D := by ext; simp
    rw [e1, e2] at key
    exact key
  · unfold HiringLP.ProbeTopK.wrank
    apply le_sup' (fun R => ∑ i ∈ R, w i)
    simp only [mem_filter, mem_powerset]
    exact ⟨gset_sub ord k D, gset_card ord k D⟩

end Greedy

/-! ### The Poisson bound -/

theorem pois_bound (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 ≤ s) :
    (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) * min s k ≤
      expMinPois s k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hEC := HiringLP.SimLower.proposition_EC_2 k
  set c := 1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ) with hc
  have hck : expMinPois k k / k = c := by rw [hEC]; field_simp
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, expMinPois_zero]; simp
  rcases le_total s k with hsk | hsk
  · rw [min_eq_left hsk]
    have hanti := HiringLP.SimLower.expMinPois_div_antitone k (show s ∈ Set.Ioi (0:ℝ) from hpos)
      (show (k : ℝ) ∈ Set.Ioi (0:ℝ) from hk0) hsk
    simp only at hanti
    rw [hck, le_div_iff₀ hpos] at hanti
    linarith
  · rw [min_eq_right hsk]
    have := expMinPois_mono k k s hk0.le hsk
    have e : c * k = expMinPois k k := by rw [hEC]; ring
    linarith

theorem one_sub_c_nonneg (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ 1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := expMinPois_nonneg k hk0.le k
  rw [HiringLP.SimLower.proposition_EC_2 k] at h
  by_contra hneg
  have := mul_neg_of_pos_of_neg hk0 (lt_of_not_ge hneg)
  linarith

/-- `E_{indep q}[min(k, |S ∩ B|)] ≥ (1 - c_k) min(k, Σ_{B} q)` over all subsets of `Fin n`. -/
theorem indep_min_bound {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) (hk : 1 ≤ k)
    (B : Finset (Fin n)) :
    (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) * min (∑ i ∈ B, q i) k ≤
      ∑ S : Finset (Fin n), HiringLP.ProbeTopK.indepProb q S * min ((S ∩ B).card : ℝ) k := by
  have h := WW_min_mask q hq k B univ 0
  simp only [Nat.sub_zero, univ_inter, Nat.cast_zero, add_zero] at h
  have e : ∑ S : Finset (Fin n), HiringLP.ProbeTopK.indepProb q S * min ((S ∩ B).card : ℝ) k =
      ∑ A ∈ (univ : Finset (Fin n)).powerset, WW q univ A * min ((A ∩ B).card : ℝ) k := by
    rw [powerset_univ]; rfl
  rw [e]
  have hB : 0 ≤ ∑ i ∈ B, q i := sum_nonneg (fun i _ => (hq i).1)
  have := pois_bound k hk _ hB
  rw [expMinPois_eq] at this
  linarith

end PTKAux

namespace PTKAux

theorem gset_swap {n : ℕ} (ord : Equiv.Perm (Fin n)) (k : ℕ) (w : Fin n → ℝ)
    (ν : Finset (Fin n) → ℝ) :
    ∑ S, ν S * ∑ i ∈ gset ord k S, w i =
      ∑ i, w i * ∑ S, ν S * (if i ∈ gset ord k S then 1 else 0) := by
  have e : ∀ S, ν S * ∑ i ∈ gset ord k S, w i =
      ∑ i, w i * (ν S * if i ∈ gset ord k S then 1 else 0) := by
    intro S
    rw [mul_sum]
    rw [← sum_subset (subset_univ (gset ord k S))]
    · apply sum_congr rfl; intro i hi; rw [if_pos hi]; ring
    · intro i _ hi; rw [if_neg hi]; ring
  rw [sum_congr rfl (fun S _ => e S), sum_comm]
  apply sum_congr rfl; intro i _; rw [mul_sum]

theorem prefix_mass {n : ℕ} (ord : Equiv.Perm (Fin n)) (k : ℕ) (ν : Finset (Fin n) → ℝ) (t : ℕ) :
    ∑ i ∈ pre ord t, (∑ S, ν S * (if i ∈ gset ord k S then 1 else 0)) =
      ∑ S, ν S * min ((S ∩ pre ord t).card : ℝ) k := by
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [← mul_sum, sum_boole]
  have e : (filter (fun i => i ∈ gset ord k S) (pre ord t)) = gset ord k S ∩ pre ord t := by
    ext i; simp [and_comm]
  rw [e, gset_pre, Nat.cast_min, min_comm]

end PTKAux

open PTKAux in
theorem solution {n : ℕ} (k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (μ : Finset (Fin n) → ℝ) (hμ0 : ∀ S, 0 ≤ μ S) (hμ1 : ∑ S, μ S = 1) :
    (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) * ∑ S, μ S * wrank w k S ≤
      ∑ S, indepProb (marg μ) S * wrank w k S := by
  set c := 1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ) with hc
  have hc0 : 0 ≤ c := one_sub_c_nonneg k hk
  obtain ⟨ord, hord⟩ : ∃ o : Equiv.Perm (Fin n), o = Tuple.sort (fun i => -w i) := ⟨_, rfl⟩
  have hs : SortedBy ord w := by
    intro l i hli
    have hm := Tuple.monotone_sort (fun i => -w i) hli.le
    rw [← hord] at hm
    simp only [Function.comp, Equiv.apply_symm_apply] at hm
    linarith
  set q := marg μ with hq_def
  have hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := by
    intro i
    constructor
    · exact sum_nonneg (fun S _ => mul_nonneg (hμ0 S) (by split_ifs <;> norm_num))
    · rw [← hμ1]
      exact sum_le_sum (fun S _ => by
        have := hμ0 S
        split_ifs <;> nlinarith)
  simp only [wrank_eq_gset ord w hw hs k]
  rw [gset_swap, gset_swap, mul_sum]
  simp only [mul_comm c, mul_assoc]
  apply abel ord w hw hs
  intro t _
  rw [← sum_mul, prefix_mass, prefix_mass, mul_comm]
  set P := pre ord t
  have hup : ∑ S, μ S * min ((S ∩ P).card : ℝ) k ≤ min (∑ i ∈ P, q i) k := by
    apply le_min
    · have e : ∑ i ∈ P, q i = ∑ S, μ S * ((S ∩ P).card : ℝ) := by
        simp only [hq_def, marg]
        rw [sum_comm]
        apply sum_congr rfl
        intro S _
        rw [← mul_sum, sum_boole]
        have e : filter (fun i => i ∈ S) P = S ∩ P := by ext i; simp [and_comm]
        rw [e]
      rw [e]
      exact sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hμ0 S))
    · calc ∑ S, μ S * min ((S ∩ P).card : ℝ) k ≤ ∑ S, μ S * (k : ℝ) :=
            sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hμ0 S))
        _ = k := by rw [← sum_mul, hμ1, one_mul]
  have hlow := indep_min_bound q hq k hk P
  calc c * ∑ S, μ S * min ((S ∩ P).card : ℝ) k ≤ c * min (∑ i ∈ P, q i) k :=
        mul_le_mul_of_nonneg_left hup hc0
    _ ≤ _ := hlow
