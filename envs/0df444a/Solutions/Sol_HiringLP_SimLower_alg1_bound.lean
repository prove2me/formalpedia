-- Prove2me | solution 1 for HiringLP.SimLower.alg1_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:28:27.465299+00:00
-- url     : https://prove2.me/submissions/143fc870-0b50-4bf4-a906-e1963488dbd7

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP
import Definitions.Def_HiringLP_SimLower_Algorithm
import Definitions.Def_HiringLP_SimLower_PoissonRatio
import Theorems.Thm_HiringLP_SimLower_expMinPois_div_antitone
import Theorems.Thm_HiringLP_SimLower_proposition_EC_2

set_option autoImplicit false
open Finset HiringLP.SimLower

namespace T3Aux

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

/-! ### Truncation -/

section Trunc
variable {n : ℕ} (I : SimInstance n)

noncomputable def Pl (i : Fin n) : ℝ := ∑ l ∈ univ.filter (fun l => l < i), I.p l

theorem trunc_mul (κ : ℝ) (i : Fin n) (hp : 0 ≤ I.p i) :
    truncate I κ i * I.p i = min κ (Pl I i + I.p i) - min κ (Pl I i) := by
  unfold truncate
  change (if I.p i = 0 then 0 else min 1 (max 0 ((κ - Pl I i) / I.p i))) * I.p i = _
  split_ifs with h0
  · rw [h0]; simp
  have hp' : 0 < I.p i := lt_of_le_of_ne hp (Ne.symm h0)
  rcases le_total κ (Pl I i) with h1 | h1
  · have : (κ - Pl I i) / I.p i ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hp
    rw [max_eq_left this, min_eq_right zero_le_one, min_eq_left (by linarith), min_eq_left h1]
    ring
  rcases le_total κ (Pl I i + I.p i) with h2 | h2
  · have e1 : 0 ≤ (κ - Pl I i) / I.p i := div_nonneg (by linarith) hp
    have e2 : (κ - Pl I i) / I.p i ≤ 1 := by rw [div_le_one hp']; linarith
    rw [max_eq_right e1, min_eq_right e2, min_eq_left h2, min_eq_right h1]
    field_simp
  · have e2 : 1 ≤ (κ - Pl I i) / I.p i := by rw [le_div_iff₀ hp']; linarith
    rw [max_eq_right (by linarith), min_eq_left e2, min_eq_right h2, min_eq_right h1]
    ring

theorem trunc_bounds (κ : ℝ) (i : Fin n) : 0 ≤ truncate I κ i ∧ truncate I κ i ≤ 1 := by
  unfold truncate
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

noncomputable def ee (l : ℕ) : ℝ := if h : l < n then I.p ⟨l, h⟩ else 0

theorem Pl_eq (i : Fin n) : Pl I i = ∑ l ∈ range i, ee I l := by
  unfold Pl
  rw [sum_filter]
  have h := Fin.sum_univ_eq_sum_range (fun l => if l < (i : ℕ) then ee I l else 0) n
  have e : ∀ l : Fin n, (if l < i then I.p l else 0) =
      (fun l => if l < (i : ℕ) then ee I l else 0) (l : ℕ) := by
    intro l
    simp only [Fin.lt_def, ee, dif_pos l.isLt]
  rw [sum_congr rfl (fun l _ => e l), h, ← sum_filter]
  congr 1
  ext l
  simp only [mem_filter, mem_range]
  have := i.isLt
  omega

theorem Ptot_eq : ∑ i, I.p i = ∑ l ∈ range n, ee I l := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro l _
  simp [ee]

theorem trunc_sum (κ : ℝ) (hκ0 : 0 ≤ κ) (hκP : κ ≤ ∑ i, I.p i) (hp : ∀ i, 0 ≤ I.p i) :
    ∑ i, truncate I κ i * I.p i = κ := by
  rw [sum_congr rfl (fun i _ => trunc_mul I κ i (hp i))]
  have e : ∀ i : Fin n, min κ (Pl I i + I.p i) - min κ (Pl I i) =
      (fun l : ℕ => min κ (∑ m ∈ range (l + 1), ee I m) - min κ (∑ m ∈ range l, ee I m)) i := by
    intro i
    simp only
    rw [Pl_eq, sum_range_succ]
    simp [ee]
  rw [sum_congr rfl (fun i _ => e i), Fin.sum_univ_eq_sum_range
    (fun l : ℕ => min κ (∑ m ∈ range (l + 1), ee I m) - min κ (∑ m ∈ range l, ee I m)) n,
    sum_range_sub (fun l => min κ (∑ m ∈ range l, ee I m)), ← Ptot_eq]
  simp [min_eq_left hκP, min_eq_right hκ0]

theorem Pl_nonneg (hp : ∀ i, 0 ≤ I.p i) (i : Fin n) : 0 ≤ Pl I i :=
  sum_nonneg (fun l _ => hp l)

theorem Pl_mono (hp : ∀ i, 0 ≤ I.p i) (i i' : Fin n) (h : i < i') :
    Pl I i + I.p i ≤ Pl I i' := by
  unfold Pl
  have hni : i ∉ univ.filter (fun l => l < i) := by simp
  rw [add_comm, ← sum_insert hni]
  apply sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [mem_insert, mem_filter, mem_univ, true_and] at hl ⊢
    rcases hl with rfl | hl
    · exact h
    · exact lt_trans hl h
  · intro l _ _; exact hp l

theorem greedy (hp : ∀ i, 0 ≤ I.p i) (hv0 : ∀ i, 0 ≤ I.v i) (hanti : Antitone I.v)
    (κ : ℝ) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ I.p i)
    (hsum : ∑ i, b i ≤ ∑ i, (min κ (Pl I i + I.p i) - min κ (Pl I i))) :
    ∑ i, I.v i * b i ≤ ∑ i, I.v i * (min κ (Pl I i + I.p i) - min κ (Pl I i)) := by
  by_cases hJ : ∃ j, κ < Pl I j + I.p j
  · set J := univ.filter (fun j => κ < Pl I j + I.p j) with hJdef
    have hJne : J.Nonempty := by
      obtain ⟨j, hj⟩ := hJ; exact ⟨j, by simp [hJdef, hj]⟩
    set j := J.min' hJne
    have hjJ : κ < Pl I j + I.p j := by
      have := J.min'_mem hJne; simpa [hJdef] using this
    have key : ∀ i, 0 ≤ (I.v i - I.v j) *
        ((min κ (Pl I i + I.p i) - min κ (Pl I i)) - b i) := by
      intro i
      rcases lt_trichotomy i j with h | h | h
      · have hiJ : i ∉ J := fun hi => absurd (J.min'_le i hi) (not_le.2 h)
        have hle : Pl I i + I.p i ≤ κ := by
          by_contra hc; exact hiJ (by simp [hJdef]; linarith)
        have := hp i
        rw [min_eq_right hle, min_eq_right (by linarith)]
        have hv := hanti h.le
        have := hb i
        nlinarith
      · rw [h]; simp
      · have h1 := Pl_mono I hp j i h
        rw [min_eq_left (by linarith [hp i]), min_eq_left (by linarith)]
        have hv := hanti h.le
        have := hb i
        nlinarith
    have e : ∑ i, I.v i * (min κ (Pl I i + I.p i) - min κ (Pl I i)) - ∑ i, I.v i * b i =
        ∑ i, (I.v i - I.v j) * ((min κ (Pl I i + I.p i) - min κ (Pl I i)) - b i) +
          I.v j * (∑ i, (min κ (Pl I i + I.p i) - min κ (Pl I i)) - ∑ i, b i) := by
      rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    have h1 : 0 ≤ ∑ i, (I.v i - I.v j) * ((min κ (Pl I i + I.p i) - min κ (Pl I i)) - b i) :=
      sum_nonneg (fun i _ => key i)
    have h2 := mul_nonneg (hv0 j) (sub_nonneg.2 hsum)
    linarith
  · push Not at hJ
    apply sum_le_sum
    intro i _
    have hle := hJ i
    have := hp i
    rw [min_eq_right hle, min_eq_right (by linarith)]
    have := hb i
    have := hv0 i
    nlinarith

end Trunc

end T3Aux

set_option maxHeartbeats 1000000 in
open T3Aux in
theorem T3Aux.core {n : ℕ} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (I : SimInstance n) (hI : I.Valid)
    (hτ : I.TauBounded τ) (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ratioObj I.k τ s * LPsim I ≤ algReward I y s := by
  obtain ⟨hk1, -, hp01, hv0, hanti⟩ := hI
  have hp : ∀ i, 0 ≤ I.p i := fun i => (hp01 i).1
  have hkpos : (0 : ℝ) < I.k := by exact_mod_cast hk1
  obtain ⟨hs0, hs1⟩ := hs
  -- the LP optimum
  obtain ⟨⟨hy, hz0, hzk⟩, hmax⟩ := hopt
  have hLP : LPsim I = LPobj I y z := by
    unfold LPsim
    apply IsGreatest.csSup_eq
    exact ⟨⟨y, z, ⟨hy, hz0, hzk⟩, rfl⟩, by rintro _ ⟨y', z', hf, rfl⟩; exact hmax y' z' hf⟩
  set M := ∑ i, y i * I.p i with hMdef
  have hMeq : ∑ i, I.p i * y i = M := sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hMeq] at hzk
  have hzmin : min 0 ((I.k : ℝ) - M) ≤ z := by
    have := hmax y (min 0 ((I.k : ℝ) - M)) ⟨hy, min_le_left _ _, by rw [hMeq]; exact min_le_right _ _⟩
    unfold LPobj at this; linarith
  set V := ∑ i, I.v i * I.p i * y i with hVdef
  have hLPV : LPsim I = V + z := hLP
  have hM0 : 0 ≤ M := sum_nonneg (fun i _ => mul_nonneg (hy i).1 (hp i))
  have hMP : M ≤ ∑ i, I.p i := sum_le_sum (fun i _ => by
    have := hy i; have := hp i; nlinarith)
  have hVτ : τ * M ≤ V := by
    rw [hMdef, mul_sum]
    apply sum_le_sum
    intro i _
    have := hτ i; have := hy i; have := hp i
    have : 0 ≤ I.p i * y i := mul_nonneg (hp i) (hy i).1
    nlinarith
  set κ := s * M with hκdef
  have hκ0 : 0 ≤ κ := mul_nonneg hs0 hM0
  have hκM : κ ≤ M := by nlinarith
  -- the truncated solution
  have hsuma : ∑ i, truncate I κ i * I.p i = κ := trunc_sum I κ hκ0 (by linarith) hp
  have hgreedy : s * V ≤ ∑ i, I.v i * (truncate I κ i * I.p i) := by
    have hg := greedy I hp hv0 hanti κ (fun i => s * (y i * I.p i))
      (fun i => ⟨mul_nonneg hs0 (mul_nonneg (hy i).1 (hp i)), by
        have := hy i; have := hp i
        have : y i * I.p i ≤ I.p i := by nlinarith
        have : 0 ≤ y i * I.p i := mul_nonneg (hy i).1 (hp i)
        nlinarith⟩)
      (by
        rw [← sum_congr rfl (fun i _ => trunc_mul I κ i (hp i)), hsuma, ← mul_sum])
    have e2 : ∑ i, I.v i * (min κ (Pl I i + I.p i) - min κ (Pl I i)) =
        ∑ i, I.v i * (truncate I κ i * I.p i) :=
      sum_congr rfl (fun i _ => by rw [trunc_mul I κ i (hp i)])
    rw [e2] at hg
    have e : s * V = ∑ i, I.v i * (s * (y i * I.p i)) := by
      rw [hVdef, mul_sum]; apply sum_congr rfl; intro i _; ring
    rw [e]; exact hg
  -- the reward
  have hq : ∀ i, 0 ≤ truncate I κ i * I.p i ∧ truncate I κ i * I.p i ≤ 1 := by
    intro i
    have ht := trunc_bounds I κ i; have hpi := hp01 i
    constructor
    · exact mul_nonneg ht.1 (hp i)
    · nlinarith
  have hR : ∑ i, I.v i * (truncate I κ i * I.p i) - κ + expMinPois κ I.k ≤ algReward I y s := by
    unfold algReward rewardIndep
    rw [← hMdef]
    change _ ≤ ∑ A ∈ univ, WW (fun i => truncate I κ i * I.p i) univ A * _
    rw [← powerset_univ]
    have e : ∀ A ∈ (univ : Finset (Fin n)).powerset,
        WW (fun i => truncate I κ i * I.p i) univ A *
          ((∑ i ∈ A, I.v i) - max ((A.card : ℝ) - I.k) 0) =
        WW (fun i => truncate I κ i * I.p i) univ A * (∑ i ∈ A, I.v i) -
          WW (fun i => truncate I κ i * I.p i) univ A * (∑ i ∈ A, (1 : ℝ)) +
          WW (fun i => truncate I κ i * I.p i) univ A * min ((A.card : ℝ) + ((0 : ℕ) : ℝ)) I.k := by
      intro A _
      rw [sum_const, nsmul_eq_mul, mul_one, Nat.cast_zero, add_zero]
      have : max ((A.card : ℝ) - I.k) 0 = (A.card : ℝ) - min (A.card : ℝ) I.k := by
        rcases le_total (A.card : ℝ) I.k with h | h
        · rw [max_eq_right (by linarith), min_eq_left h]; ring
        · rw [max_eq_left (by linarith), min_eq_right h]
      rw [this]; ring
    rw [sum_congr rfl e, sum_add_distrib, sum_sub_distrib, WW_lin, WW_lin]
    have hmin := WW_min (fun i => truncate I κ i * I.p i) hq I.k univ 0
    rw [Nat.sub_zero, hsuma] at hmin
    have e2 : ∑ i, (1 : ℝ) * (truncate I κ i * I.p i) = κ := by
      simp only [one_mul]; exact hsuma
    rw [e2, expMinPois_eq]
    linarith
  -- Poisson facts
  have hgle : expMinPois (s * I.k) I.k ≤ s * I.k := expMinPois_le _ (by positivity) _
  set D := s * I.k - expMinPois (s * I.k) I.k with hD
  have hD0 : 0 ≤ D := by linarith
  have hρ : ratioObj I.k τ s = s - D / (τ * I.k) := by
    unfold ratioObj; rw [hD]; field_simp; ring
  have hcD : 0 ≤ D / (τ * I.k) := by positivity
  rw [hρ, hLPV]
  rcases le_or_gt M I.k with hMk | hMk
  · -- no overage in the LP
    have hz : z = 0 := by
      have : min 0 ((I.k : ℝ) - M) = 0 := min_eq_left (by linarith)
      linarith
    rw [hz, add_zero]
    have hant : M * expMinPois (s * I.k) I.k ≤ expMinPois κ I.k * I.k := by
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · rw [hκdef, ← h0]; simp [expMinPois_zero]
      rcases eq_or_lt_of_le hM0 with h1 | h1
      · rw [← h1]; simp only [zero_mul]
        exact mul_nonneg (expMinPois_nonneg _ hκ0 _) hkpos.le
      have hκpos : 0 < κ := mul_pos h0 h1
      have := expMinPois_div_antitone I.k (show κ ∈ Set.Ioi (0 : ℝ) from hκpos)
        (show s * (I.k : ℝ) ∈ Set.Ioi (0 : ℝ) from mul_pos h0 hkpos)
        (mul_le_mul_of_nonneg_left hMk hs0)
      simp only at this
      rw [div_le_div_iff₀ (mul_pos h0 hkpos) hκpos, hκdef] at this
      have : s * (M * expMinPois (s * I.k) I.k) ≤ s * (expMinPois κ I.k * I.k) := by
        rw [hκdef]; linarith
      exact le_of_mul_le_mul_left this h0
    have h1 : D / (τ * I.k) * (τ * M) = D * M / I.k := by field_simp
    have h2 : D / (τ * I.k) * (τ * M) ≤ D / (τ * I.k) * V := mul_le_mul_of_nonneg_left hVτ hcD
    have h3 : D * M / I.k ≥ s * M - expMinPois κ I.k := by
      rw [ge_iff_le, le_div_iff₀ hkpos, hD]
      nlinarith
    nlinarith
  · -- overage in the LP
    have hz : z = (I.k : ℝ) - M := by
      have : min 0 ((I.k : ℝ) - M) = (I.k : ℝ) - M := min_eq_right (by linarith)
      linarith
    -- `LP_sim(I) ≥ τ k`
    have hLPk : τ * I.k ≤ V + z := by
      have hkP : (I.k : ℝ) ≤ ∑ i, I.p i := by linarith
      have hsk := trunc_sum I (I.k : ℝ) hkpos.le hkP hp
      have hf : LPFeasible I (truncate I (I.k : ℝ)) 0 := by
        refine ⟨fun i => trunc_bounds I _ i, le_rfl, ?_⟩
        have : ∑ i, I.p i * truncate I (I.k : ℝ) i = I.k := by
          calc ∑ i, I.p i * truncate I (I.k : ℝ) i = ∑ i, truncate I (I.k : ℝ) i * I.p i :=
                sum_congr rfl (fun i _ => mul_comm _ _)
            _ = I.k := hsk
        rw [this]; simp
      have h := hmax _ _ hf
      unfold LPobj at h
      have : τ * I.k ≤ ∑ i, I.v i * I.p i * truncate I (I.k : ℝ) i := by
        calc τ * (I.k : ℝ) = τ * ∑ i, truncate I (I.k : ℝ) i * I.p i := by rw [hsk]
          _ = ∑ i, τ * (truncate I (I.k : ℝ) i * I.p i) := mul_sum _ _ _
          _ ≤ _ := ?_
        apply sum_le_sum
        intro i _
        have := hτ i
        have : 0 ≤ truncate I (I.k : ℝ) i * I.p i :=
          mul_nonneg (trunc_bounds I _ i).1 (hp i)
        nlinarith
      linarith
    have hmono : expMinPois (s * I.k) I.k ≤ expMinPois κ I.k :=
      expMinPois_mono _ _ _ (by positivity) (mul_le_mul_of_nonneg_left hMk.le hs0)
    clear_value D κ V M
    have h2 : D / (τ * I.k) * (τ * I.k) ≤ D / (τ * I.k) * (V + z) :=
      mul_le_mul_of_nonneg_left hLPk hcD
    have h1 : D / (τ * I.k) * (τ * I.k) = D := div_mul_cancel₀ D (ne_of_gt (mul_pos hτ0 hkpos))
    rw [hz] at h2 ⊢
    have hexp : (s - D / (τ * I.k)) * (V + ((I.k : ℝ) - M)) =
        s * V + s * I.k - s * M - D / (τ * I.k) * (V + ((I.k : ℝ) - M)) := by ring
    rw [hexp]
    generalize algReward I y s = R at hR ⊢
    generalize (∑ i, I.v i * (truncate I κ i * I.p i)) = A at hgreedy hR
    generalize expMinPois κ I.k = gk at hR hmono
    generalize expMinPois (s * I.k) I.k = gs at hD hmono
    generalize D / (τ * I.k) = c at h1 h2 ⊢
    linarith only [h2, h1, hD, hmono, hgreedy, hR, hκdef]

open T3Aux in
theorem solution {n : ℕ} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (I : SimInstance n) (hI : I.Valid) (hτ : I.TauBounded τ)
    (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z) :
    (1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / ((I.k.factorial : ℝ) * τ)) * LPsim I ≤
      algReward I y 1 := by
  have h := T3Aux.core τ hτ0 hτ1 I hI hτ y z hopt 1 ⟨zero_le_one, le_rfl⟩
  have hk : (0 : ℝ) < I.k := by exact_mod_cast hI.1
  have e : ratioObj I.k τ 1 =
      1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / ((I.k.factorial : ℝ) * τ) := by
    unfold ratioObj
    rw [one_mul, proposition_EC_2]
    have : (I.k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← e]; exact h
