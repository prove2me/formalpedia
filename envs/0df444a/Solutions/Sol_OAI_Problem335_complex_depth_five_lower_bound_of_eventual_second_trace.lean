-- Prove2me | solution 1 for OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:14.216986+00:00
-- url     : https://prove2.me/submissions/1e418e9b-7871-42cc-a308-8c774963f417

import Mathlib
import Definitions.Def_DepthFive
import Definitions.Def_OAIQWDF000

section
-- module Solutions.OAIQW_Problem335.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer parameters for the lower-bound rank measure. -/
namespace Problem335.LowerParameters

noncomputable section

theorem s_le_sqrt (n : ℕ) : (s n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h : (s n : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast s_le_nat_sqrt n
  exact h.trans Real.nat_sqrt_le_real_sqrt

theorem sqrt_sub_two_lt_s (n : ℕ) : Real.sqrt (n : ℝ) - 2 < (s n : ℝ) := by
  have h₁ := Real.real_sqrt_lt_nat_sqrt_succ (a := n)
  have h₂ : (Nat.sqrt n : ℝ) ≤ (s n : ℝ) + 1 := by
    exact_mod_cast nat_sqrt_le_s_add_one n
  linarith

theorem sqrt_half_le_s {n : ℕ} (hn : 16 ≤ n) :
    Real.sqrt (n : ℝ) / 2 ≤ (s n : ℝ) := by
  have h₁ := sqrt_sub_two_lt_s n
  have h₂ : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  linarith

theorem s_le_quarter {n : ℕ} (hn : 16 ≤ n) : (s n : ℝ) ≤ (n : ℝ) / 4 := by
  have hs := s_le_sqrt n
  have hroot : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  nlinarith

theorem three_mul_n_le_eight_mul_k {n : ℕ} (hn : 16 ≤ n) :
    3 * n ≤ 8 * k n := by
  have hs := s_le_quarter hn
  have hk : 2 * (k n : ℝ) + (s n : ℝ) = (n : ℝ) := by
    exact_mod_cast two_mul_k_add_s n
  have h : 3 * (n : ℝ) ≤ 8 * (k n : ℝ) := by linarith
  exact_mod_cast h

theorem lambda_ge_three_eighths {n : ℕ} (hn : 16 ≤ n) :
    (3 : ℝ) / 8 ≤ lambda n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lambda, le_div_iff₀ hpos]
  have h : 3 * (n : ℝ) ≤ 8 * (k n : ℝ) := by
    exact_mod_cast three_mul_n_le_eight_mul_k hn
  linarith

theorem rho_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rho n := by
  unfold rho
  apply div_pos <;> exact_mod_cast (by first | exact k_pos hn | exact m_pos hn)

theorem lambda_eq_half_sub {n : ℕ} (hn : 0 < n) :
    lambda n = 1 / 2 - (s n : ℝ) / (2 * (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hk : 2 * (k n : ℝ) + (s n : ℝ) = (n : ℝ) := by
    exact_mod_cast two_mul_k_add_s n
  unfold lambda
  field_simp
  linarith

theorem lambda_eq_rho_div {n : ℕ} (hn : 4 ≤ n) :
    lambda n = rho n / (1 + rho n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (m_pos hn))
  have hsum : (k n : ℝ) + (m n : ℝ) = (n : ℝ) := by
    exact_mod_cast k_add_m n
  unfold lambda rho
  field_simp
  nlinarith

theorem lambda_mul_n (n : ℕ) : lambda n * (n : ℝ) = (k n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num [lambda, k, s]
  · exact div_mul_cancel₀ _ (by exact_mod_cast hn)

theorem k_le_n (n : ℕ) : k n ≤ n := by
  have := k_add_m n
  omega

theorem m_le_n (n : ℕ) : m n ≤ n := by
  have := k_add_m n
  omega

theorem n_le_two_mul_m (n : ℕ) : n ≤ 2 * m n := by
  have := two_mul_m n
  omega

theorem one_sub_rho {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n = (s n : ℝ) / (m n : ℝ) := by
  have hm : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (m_pos hn))
  have h : (m n : ℝ) = (k n : ℝ) + (s n : ℝ) := by
    exact_mod_cast m_eq_k_add_s n
  unfold rho
  field_simp
  linarith

theorem u_pos {n : ℕ} (hn : 4 ≤ n) : 0 < u n := by
  unfold u
  exact Nat.mul_pos (m_pos hn) (Nat.pow_pos (by omega))

theorem three_mul_cube_le_eight_mul_v {n : ℕ} (hn : 16 ≤ n) :
    3 * n ^ 3 ≤ 8 * v n := by
  have h := Nat.mul_le_mul_right (n ^ 2) (three_mul_n_le_eight_mul_k hn)
  dsimp [v]
  nlinarith [h]

theorem cube_le_two_mul_u (n : ℕ) : n ^ 3 ≤ 2 * u n := by
  have h := Nat.mul_le_mul_right (n ^ 2) (n_le_two_mul_m n)
  dsimp [u]
  nlinarith [h]

end
end Problem335.LowerParameters

end OAI
end

section
-- module Solutions.OAIQW_Problem335.AnalyticParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounded analytic parameters used by the lower-bound rank measure. -/
noncomputable section
namespace Problem335.LowerParameters

theorem sqrt_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

theorem a0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a0 n := by
  unfold a0
  apply div_pos
  · exact_mod_cast v_pos hn
  · have := sqrt_ge_two hn
    linarith

theorem a_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a n := by
  exact Nat.ceil_pos.mpr (a0_pos hn)

theorem a0_le_a (n : ℕ) : a0 n ≤ (a n : ℝ) := Nat.le_ceil _

theorem alpha_pos {n : ℕ} (hn : 4 ≤ n) : 0 < alpha n := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  unfold alpha
  positivity

theorem inv_sqrt_le_alpha {n : ℕ} (hn : 4 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ alpha n := by
  have hr := sqrt_ge_two hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hround := a0_le_a n
  have hmul : (v n : ℝ) ≤ (a n : ℝ) * (Real.sqrt (n : ℝ) - 1) :=
    (div_le_iff₀ (by linarith)).mp hround
  rw [inv_eq_one_div, alpha]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  nlinarith

theorem inv_alpha_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ) := by
  have ha := alpha_pos hn
  have hs := sqrt_ge_two hn
  have h := inv_sqrt_le_alpha hn
  calc
    (alpha n)⁻¹ ≤ ((Real.sqrt (n : ℝ))⁻¹)⁻¹ :=
      (inv_le_inv₀ ha (inv_pos.mpr (by linarith))).mpr h
    _ = _ := inv_inv _

theorem k_mul_n_le_a0 {n : ℕ} (hn : 4 ≤ n) :
    (k n : ℝ) * (n : ℝ) ≤ a0 n := by
  have hr := sqrt_ge_two hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hbound : Real.sqrt (n : ℝ) - 1 ≤ (n : ℝ) := by nlinarith
  unfold a0
  apply (le_div_iff₀ (by linarith)).mpr
  have h := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (k n : ℝ) * (n : ℝ) by positivity)
  simpa [v, Nat.cast_mul, Nat.cast_pow, pow_two, mul_assoc] using h

theorem k_mul_n_le_a {n : ℕ} (hn : 4 ≤ n) : k n * n ≤ a n := by
  have h := (k_mul_n_le_a0 hn).trans (a0_le_a n)
  exact_mod_cast h

theorem k_le_a {n : ℕ} (hn : 4 ≤ n) : k n ≤ a n := by
  exact (Nat.le_mul_of_pos_right _ (by omega)).trans (k_mul_n_le_a hn)

theorem four_mul_n_le_a {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ a n := by
  have hk := three_mul_n_le_eight_mul_k hn
  have hka := k_mul_n_le_a (show 4 ≤ n by omega)
  have hk4 : 4 ≤ k n := by omega
  exact (Nat.mul_le_mul_right n hk4).trans hka

theorem alpha_rpow_rho_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < (alpha n) ^ (rho n) := Real.rpow_pos_of_pos (alpha_pos hn) _

theorem alpha_rpow_rho_lt_one {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (rho n) < 1 :=
  Real.rpow_lt_one (alpha_pos hn).le (alpha_lt_one hn) (rho_pos hn)

theorem alpha_le_alpha_rpow_rho {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (alpha n) ^ (rho n) :=
  Real.self_le_rpow_of_le_one (alpha_pos hn).le (alpha_lt_one hn).le (rho_lt_one hn).le

theorem b0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b0 n := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  unfold b0
  positivity

theorem b_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b n :=
  Nat.ceil_pos.mpr (b0_pos hn)

theorem b0_le_b (n : ℕ) : b0 n ≤ (b n : ℝ) := Nat.le_ceil _

theorem alpha_rpow_rho_le_beta {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (rho n) ≤ beta n := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hp := alpha_rpow_rho_lt_one hn
  have hround := b0_le_b n
  have hmul : (u n : ℝ) * (alpha n) ^ (rho n) ≤
      (b n : ℝ) * (1 - (alpha n) ^ (rho n)) :=
    (div_le_iff₀ (by linarith)).mp hround
  rw [beta]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem a_le_b0 {n : ℕ} (hn : 4 ≤ n) : (a n : ℝ) ≤ b0 n := by
  have hap := alpha_pos hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hu : (v n : ℝ) ≤ u n := by
    have hkm : k n ≤ m n := (k_lt_m hn).le
    exact_mod_cast Nat.mul_le_mul_right (n ^ 2) hkm
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  have hal := alpha_le_alpha_rpow_rho hn
  have heq : (a n : ℝ) * (1 - alpha n) = (v n : ℝ) * alpha n := by
    unfold alpha
    field_simp
    ring
  unfold b0
  apply (le_div_iff₀ (by linarith)).mpr
  calc
    (a n : ℝ) * (1 - (alpha n) ^ (rho n)) ≤ (a n : ℝ) * (1 - alpha n) := by
      gcongr
    _ = (v n : ℝ) * alpha n := heq
    _ ≤ (u n : ℝ) * (alpha n) ^ (rho n) :=
      mul_le_mul hu hal hap.le (by positivity)

theorem a_le_b {n : ℕ} (hn : 4 ≤ n) : a n ≤ b n := by
  exact_mod_cast (a_le_b0 hn).trans (b0_le_b n)

theorem four_mul_n_le_b {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ b n :=
  (four_mul_n_le_a hn).trans (a_le_b (by omega))

theorem q_pos {n : ℕ} (hn : 4 ≤ n) : 0 < q n :=
  Real.rpow_pos_of_pos (alpha_pos hn) _

theorem alpha_le_q {n : ℕ} (hn : 4 ≤ n) : alpha n ≤ q n := by
  have hr := rho_lt_one hn
  exact Real.self_le_rpow_of_le_one (alpha_pos hn).le (alpha_lt_one hn).le (by linarith)

theorem inv_sqrt_le_q {n : ℕ} (hn : 4 ≤ n) : (Real.sqrt (n : ℝ))⁻¹ ≤ q n :=
  (inv_sqrt_le_alpha hn).trans (alpha_le_q hn)

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitDegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335
universe u
variable {K : Type u} [CommSemiring K] {n : ℕ}

omit [CommSemiring K] in
/-- Every input leaf has formal degree at most one. -/
theorem d5LeafDegree_le_one (x : D5Leaf K n) : d5LeafDegree x ≤ 1 := by
  cases x <;> simp [d5LeafDegree]

/-- Bottom sums have degree zero or one, including empty bottom sums. -/
theorem bottomDegree_le_one (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    c.bottomDegree i ≤ 1 := by
  by_cases h : c.bottomInputs i = []
  · rw [c.bottomEmpty i h]
    omega
  · obtain ⟨entry, hentry⟩ := List.exists_mem_of_ne_nil _ h
    rw [← c.bottomHomogeneous i entry hentry]
    exact d5LeafDegree_le_one _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Homogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- Homogeneity is preserved by a list sum, including the empty sum. -/
theorem isHomogeneous_list_sum {K : Type u} [CommSemiring K]
    {σ : Type v} {ι : Type w} (l : List ι) (f : ι → MvPolynomial σ K) (d : ℕ)
    (h : ∀ i ∈ l, (f i).IsHomogeneous d) :
    (l.map f).sum.IsHomogeneous d := by
  induction l with
  | nil => simpa using MvPolynomial.isHomogeneous_zero σ K d
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

/-- A product's formal degree is the sum of its factors' formal degrees. -/
theorem isHomogeneous_list_prod {K : Type u} [CommSemiring K]
    {σ : Type v} {ι : Type w} (l : List ι) (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (h : ∀ i ∈ l, (f i).IsHomogeneous (d i)) :
    (l.map f).prod.IsHomogeneous (l.map d).sum := by
  induction l with
  | nil => simpa using MvPolynomial.isHomogeneous_one (σ := σ) K
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

theorem d5LeafValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (x : D5Leaf K n) : (d5LeafValue x).IsHomogeneous (d5LeafDegree x) := by
  cases x with
  | scalar a => exact MvPolynomial.isHomogeneous_C _ a
  | «variable» i => exact MvPolynomial.isHomogeneous_X K i

theorem bottomValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    (bottomValue c i).IsHomogeneous (c.bottomDegree i) := by
  unfold bottomValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.bottomHomogeneous i entry hentry]
  exact (d5LeafValue_isHomogeneous (c.leaves entry.2)).C_mul entry.1

theorem lowerValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    (lowerValue c i).IsHomogeneous ((c.lowerInputs i).map c.bottomDegree).sum := by
  unfold lowerValue
  apply isHomogeneous_list_prod
  intro j _
  exact bottomValue_isHomogeneous c j

theorem middleValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    (middleValue c i).IsHomogeneous (c.middleDegree i) := by
  unfold middleValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.middleHomogeneous i entry hentry]
  exact (lowerValue_isHomogeneous c entry.2).C_mul entry.1

theorem upperValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    (upperValue c i).IsHomogeneous ((c.upperInputs i).map c.middleDegree).sum := by
  unfold upperValue
  apply isHomogeneous_list_prod
  intro j _
  exact middleValue_isHomogeneous c j

theorem circuitValue_isHomogeneous {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) :
    (circuitValue c).IsHomogeneous c.outputDegree := by
  unfold circuitValue
  apply isHomogeneous_list_sum
  intro entry hentry
  rw [← c.outputHomogeneous entry hentry]
  exact (upperValue_isHomogeneous c entry.2).C_mul entry.1

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ProductNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

universe u v

variable {K : Type u} [CommSemiring K] {σ : Type v}

/-- A homogeneous polynomial of formal degree zero is a scalar, including
the zero polynomial. -/
theorem homogeneous_zero_eq_C {p : MvPolynomial σ K}
    (hp : p.IsHomogeneous 0) : p = C (constantCoeff p) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr hp

/-- Remove formal-degree-zero factors from a homogeneous product and absorb
them into a single scalar. Positive-degree occurrences, including repeated
occurrences and zero polynomials, are retained. -/
theorem homogeneous_product_positive_factors
    (l : List (MvPolynomial σ K × ℕ))
    (hl : ∀ q ∈ l, q.1.IsHomogeneous q.2) :
    ∃ a : K, ∃ factors : List (MvPolynomial σ K × ℕ),
      (∀ q ∈ factors, 0 < q.2 ∧ q.1.IsHomogeneous q.2) ∧
      (factors.map Prod.snd).sum = (l.map Prod.snd).sum ∧
      (l.map Prod.fst).prod = C a * (factors.map Prod.fst).prod ∧
      factors.Sublist l ∧
      factors.length ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil =>
      exact ⟨1, [], by simp⟩
  | cons q l ih =>
      have hq := hl q (by simp)
      have ht : ∀ r ∈ l, r.1.IsHomogeneous r.2 := by
        intro r hr
        exact hl r (by simp [hr])
      obtain ⟨a, factors, hf, hd, hv, hs, hn⟩ := ih ht
      by_cases hzero : q.2 = 0
      · have hscalar : q.1 = C (constantCoeff q.1) :=
          homogeneous_zero_eq_C (hzero ▸ hq)
        refine ⟨constantCoeff q.1 * a, factors, hf, ?_, ?_, hs.cons q, ?_⟩
        · simpa [hzero] using hd
        · simp only [List.map_cons, List.prod_cons, hv, map_mul]
          conv_lhs => lhs; rw [hscalar]
          simp only [mul_assoc]
        · simpa [hzero] using hn
      · have hpos : 0 < q.2 := Nat.pos_of_ne_zero hzero
        refine ⟨a, q :: factors, ?_, ?_, ?_, hs.cons_cons q, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact ⟨hpos, hq⟩
          · exact hf r hr
        · simpa using congrArg (q.2 + ·) hd
        · simp only [List.map_cons, List.prod_cons, hv]
          ac_rfl
        · simp only [List.length_cons, List.map_cons, List.sum_cons]
          omega

/-- When the original formal degrees are at most one, removing the scalar
factors leaves exactly the total formal degree many homogeneous linear
forms. No assumption on variable support is required. -/
theorem homogeneous_product_linear_factors
    (l : List (MvPolynomial σ K × ℕ))
    (hl : ∀ q ∈ l, q.1.IsHomogeneous q.2)
    (hle : ∀ q ∈ l, q.2 ≤ 1) :
    ∃ a : K, ∃ factors : List (MvPolynomial σ K),
      factors.length = (l.map Prod.snd).sum ∧
      (∀ p ∈ factors, p.IsHomogeneous 1) ∧
      (l.map Prod.fst).prod = C a * factors.prod := by
  obtain ⟨a, factors, hf, hd, hv, hs, _⟩ :=
    homogeneous_product_positive_factors l hl
  have hone : ∀ q ∈ factors, q.2 = 1 := by
    intro q hq
    have hpos := (hf q hq).1
    have hbound := hle q (hs.subset hq)
    omega
  have hsum : (factors.map Prod.snd).sum = factors.length := by
    have heq : factors.map Prod.snd = factors.map (fun _ => 1) := by
      apply List.map_eq_map_iff.mpr
      exact hone
    rw [heq]
    simp
  refine ⟨a, factors.map Prod.fst, ?_, ?_, hv⟩
  · simpa only [List.length_map] using hsum.symm.trans hd
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [hone q hq] using (hf q hq).2

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitFactorForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335
universe u
variable {K : Type u} [CommSemiring K] {n : ℕ}

/-- A lower product computes a scalar times exactly its formal degree many
homogeneous linear forms, with repeated inputs retained as repeated factors. -/
theorem lowerValue_normal_form (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    ∃ a : K, ∃ factors : List (MvPolynomial (Fin n × Fin n × Fin n) K),
      factors.length = ((c.lowerInputs i).map c.bottomDegree).sum ∧
      (∀ p ∈ factors, p.IsHomogeneous 1) ∧
      lowerValue c i = MvPolynomial.C a * factors.prod := by
  let l := (c.lowerInputs i).map fun j => (bottomValue c j, c.bottomDegree j)
  have hl : ∀ q ∈ l, q.1.IsHomogeneous q.2 := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    exact bottomValue_isHomogeneous c j
  have hle : ∀ q ∈ l, q.2 ≤ 1 := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    exact bottomDegree_le_one c j
  obtain ⟨a, factors, hlen, hhom, hval⟩ := homogeneous_product_linear_factors l hl hle
  exact ⟨a, factors, by simpa [l, Function.comp_def] using hlen, hhom,
    by simpa [l, lowerValue, Function.comp_def] using hval⟩

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.GateSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

/-- Any finite list of weighted inputs can be regrouped over its finite gate type. -/
theorem list_weighted_sum_eq_sum {K R ι : Type*} [Semiring K] [Semiring R]
    [Fintype ι] [DecidableEq ι] (f : K →+* R) (value : ι → R)
    (inputs : List (K × ι)) :
    (inputs.map (fun entry => f entry.1 * value entry.2)).sum =
      ∑ i, f (gateCoefficient inputs i) * value i := by
  induction inputs with
  | nil => simp
  | cons entry inputs ih =>
    simp only [List.map_cons, List.sum_cons, gateCoefficient_cons,
      map_add, add_mul, Finset.sum_add_distrib]
    rw [← ih]
    congr 1
    simp [apply_ite, ite_mul]

/-- A combined coefficient vanishes if its predecessor does not occur. -/
theorem gateCoefficient_eq_zero_of_not_mem {K ι : Type*}
    [AddCommMonoid K] [DecidableEq ι] (inputs : List (K × ι)) (i : ι)
    (h : ∀ entry ∈ inputs, entry.2 ≠ i) : gateCoefficient inputs i = 0 := by
  unfold gateCoefficient
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hx
  simp [h entry hentry]

/-- A nonzero combined coefficient must come from an actual wire. -/
theorem exists_mem_of_gateCoefficient_ne_zero {K ι : Type*}
    [AddCommMonoid K] [DecidableEq ι] (inputs : List (K × ι)) (i : ι)
    (h : gateCoefficient inputs i ≠ 0) : ∃ entry ∈ inputs, entry.2 = i := by
  by_contra hn
  apply h
  apply gateCoefficient_eq_zero_of_not_mem
  intro entry hentry heq
  exact hn ⟨entry, hentry, heq⟩

theorem middleValue_eq_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    middleValue c i = ∑ j : Fin c.lowerCount,
      MvPolynomial.C (gateCoefficient (c.middleInputs i) j) * lowerValue c j := by
  exact list_weighted_sum_eq_sum MvPolynomial.C (lowerValue c) _

theorem circuitValue_eq_sum {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) :
    circuitValue c = ∑ j : Fin c.upperCount,
      MvPolynomial.C (gateCoefficient c.outputInputs j) * upperValue c j := by
  exact list_weighted_sum_eq_sum MvPolynomial.C (upperValue c) _

/-- Aggregating wires preserves the middle homogeneous-degree constraint. -/
theorem middleDegree_of_gateCoefficient_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) (j : Fin c.lowerCount)
    (h : gateCoefficient (c.middleInputs i) j ≠ 0) :
    ((c.lowerInputs j).map c.bottomDegree).sum = c.middleDegree i := by
  obtain ⟨entry, hentry, heq⟩ := exists_mem_of_gateCoefficient_ne_zero _ _ h
  simpa [heq] using c.middleHomogeneous i entry hentry

/-- Aggregating wires preserves the output homogeneous-degree constraint. -/
theorem outputDegree_of_gateCoefficient_ne_zero {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (j : Fin c.upperCount)
    (h : gateCoefficient c.outputInputs j ≠ 0) :
    ((c.upperInputs j).map c.middleDegree).sum = c.outputDegree := by
  obtain ⟨entry, hentry, heq⟩ := exists_mem_of_gateCoefficient_ne_zero _ _ h
  simpa [heq] using c.outputHomogeneous entry hentry

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitRankAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace Problem335

/-- Finite subadditivity, with no assumptions on the individual summands. -/
theorem measure_finset_sum_le {A ι : Type*} [AddCommMonoid A]
    (R : A → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (s : Finset ι) (f : ι → A) :
    R (∑ j ∈ s, f j) ≤ ∑ j ∈ s, R (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hzero]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact (hadd _ _).trans (add_le_add le_rfl ih)

/-- Only predecessors with nonzero aggregate coefficient need a bound.
This matters for homogeneous circuits, since inactive gates can have arbitrary
formal degree. -/
theorem measure_weighted_sum_le_card_mul {K σ ι : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s : Finset ι) (a : ι → K) (p : ι → MvPolynomial σ K)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j ∈ s, a j ≠ 0 → R (p j) ≤ B) :
    R (∑ j ∈ s, MvPolynomial.C (a j) * p j) ≤ (s.card : ℝ) * B := by
  calc
    R (∑ j ∈ s, MvPolynomial.C (a j) * p j) ≤
        ∑ j ∈ s, R (MvPolynomial.C (a j) * p j) :=
      measure_finset_sum_le R hzero hadd s _
    _ ≤ ∑ j ∈ s, B := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases ha : a j = 0
      · simpa [ha, hzero] using hB
      · exact (hscale _ _).trans (hbound j hj ha)
    _ = (s.card : ℝ) * B := by simp

/-- A uniform bound on active output predecessors costs the number of upper
product gates, never the number of output wires. -/
theorem circuit_measure_le_upperCount_mul {K : Type*} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ) (hzero : R 0 = 0)
    (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ j, gateCoefficient c.outputInputs j ≠ 0 → R (upperValue c j) ≤ B) :
    R (circuitValue c) ≤ (c.upperCount : ℝ) * B := by
  rw [circuitValue_eq_sum]
  simpa using measure_weighted_sum_le_card_mul R hzero hadd hscale
    Finset.univ (gateCoefficient c.outputInputs) (upperValue c) B hB
    (fun j _ => hbound j)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

universe u v w

/-- An indexed version of positive-factor normalization. The resulting list
is a sublist of the original gate occurrences, so sharing and multiplicity
are preserved. -/
theorem homogeneous_indexed_product_positive_factors
    {K : Type u} [CommSemiring K] {σ : Type v} {ι : Type w}
    (l : List ι) (p : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hl : ∀ i ∈ l, (p i).IsHomogeneous (d i)) :
    ∃ a : K, ∃ factors : List ι,
      factors.Sublist l ∧
      (∀ i ∈ factors, 0 < d i) ∧
      (factors.map d).sum = (l.map d).sum ∧
      (l.map p).prod = C a * (factors.map p).prod ∧
      factors.length ≤ (l.map d).sum := by
  obtain ⟨a, fs, hf, hd, hv, hs, hn⟩ :=
    homogeneous_product_positive_factors (l.map (fun i => (p i, d i))) (by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact hl i hi)
  obtain ⟨factors, hsub, rfl⟩ := List.sublist_map_iff.mp hs
  refine ⟨a, factors, hsub, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hf (p i, d i) (List.mem_map.mpr ⟨i, hi, rfl⟩)).1
  · simpa only [List.map_map, Function.comp_def] using hd
  · simpa only [List.map_map, Function.comp_def] using hv
  · simpa only [List.length_map, List.map_map, Function.comp_def] using hn

/-- Every upper product is a scalar multiple of positive-formal-degree
middle-gate occurrences whose degrees add to the original formal degree. -/
theorem upperValue_positive_factors
    {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    ∃ a : K, ∃ factors : List (Fin c.middleCount),
      factors.Sublist (c.upperInputs i) ∧
      (∀ j ∈ factors, 0 < c.middleDegree j) ∧
      (factors.map c.middleDegree).sum =
        ((c.upperInputs i).map c.middleDegree).sum ∧
      upperValue c i = C a * (factors.map (middleValue c)).prod ∧
      factors.length ≤ ((c.upperInputs i).map c.middleDegree).sum := by
  exact homogeneous_indexed_product_positive_factors
    (c.upperInputs i) (middleValue c) c.middleDegree
    (fun j _ => middleValue_isHomogeneous c j)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section

namespace Problem335
universe u v

/-- Opening one high middle factor, or applying the all-low estimate, bounds
an actual list of positive-degree middle-gate occurrences. -/
theorem positive_middle_product_measure_le
    {K : Type u} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (d : ℕ) (t B : ℝ) (hB : 0 ≤ B)
    (hlow : LowProductBound R d t B) (hhigh : HighProductBound R d t B)
    (l : List (Fin c.middleCount))
    (hpos : ∀ j ∈ l, 0 < c.middleDegree j)
    (hdegree : (l.map c.middleDegree).sum = d) :
    R (l.map (middleValue c)).prod ≤ (circuitSize c : ℝ) * B := by
  classical
  have honeNat : 1 ≤ circuitSize c := by unfold circuitSize; omega
  have hone : (1 : ℝ) ≤ circuitSize c := by exact_mod_cast honeNat
  by_cases hsmall : ∀ j ∈ l, (c.middleDegree j : ℝ) < t
  · have hb := hlow (l.map fun j => (middleValue c j, c.middleDegree j)) (by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact ⟨hpos j hj, middleValue_isHomogeneous c j, hsmall j hj⟩) (by
      simpa only [List.map_map, Function.comp_def] using hdegree)
    have hb' : R (l.map (middleValue c)).prod ≤ B := by
      simpa only [List.map_map, Function.comp_def] using hb
    exact hb'.trans (by nlinarith)
  · push Not at hsmall
    obtain ⟨j, hj, hjhigh⟩ := hsmall
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp hj
    let others := (before ++ after).map fun k => (middleValue c k, c.middleDegree k)
    have hothers : ∀ q ∈ others, 0 < q.2 ∧ q.1.IsHomogeneous q.2 := by
      intro q hq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
      refine ⟨hpos k ?_, middleValue_isHomogeneous c k⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact List.mem_append_left _ hk
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hk)
    have htotal : c.middleDegree j + (others.map Prod.snd).sum = d := by
      simpa [others, List.map_append, List.sum_append, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Function.comp_def] using hdegree
    have hexpand :
        ((before ++ j :: after).map (middleValue c)).prod =
          ∑ k : Fin c.lowerCount,
            MvPolynomial.C (gateCoefficient (c.middleInputs j) k) *
              (lowerValue c k * (others.map Prod.fst).prod) := by
      simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
      rw [middleValue_eq_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [others, List.map_map, Function.comp_def, List.map_append, List.prod_append]
      ring
    have hbranches : ∀ k : Fin c.lowerCount,
        gateCoefficient (c.middleInputs j) k ≠ 0 →
        R (lowerValue c k * (others.map Prod.fst).prod) ≤ B := by
      intro k hk
      have hkdegree := middleDegree_of_gateCoefficient_ne_zero c j k hk
      obtain ⟨a, linears, hlen, hlin, hval⟩ := lowerValue_normal_form c k
      have hlen' : linears.length = c.middleDegree j := hlen.trans hkdegree
      have heq : lowerValue c k * (others.map Prod.fst).prod =
          MvPolynomial.C a * (linears.prod * (others.map Prod.fst).prod) := by
        rw [hval]
        ring
      rw [heq]
      apply (hscale a _).trans
      exact hhigh linears others hlin hothers (by simpa [hlen'] using hjhigh)
        (by simpa [hlen'] using htotal)
    have hb : R (((before ++ j :: after).map (middleValue c)).prod) ≤
        (c.lowerCount : ℝ) * B := by
      rw [hexpand]
      simpa using measure_weighted_sum_le_card_mul R hzero hadd hscale Finset.univ
        (gateCoefficient (c.middleInputs j))
        (fun k => lowerValue c k * (others.map Prod.fst).prod) B hB
        (fun k _ => hbranches k)
    have hcountNat : c.lowerCount ≤ circuitSize c := by unfold circuitSize; omega
    have hcount : (c.lowerCount : ℝ) ≤ circuitSize c := by exact_mod_cast hcountNat
    exact hb.trans (mul_le_mul_of_nonneg_right hcount hB)

/-- The manuscript's gate-count reduction instantiated with the actual circuit
normal forms. All remaining hypotheses are bounds on homogeneous products,
not circuit-specific summands or wire counts. -/
theorem circuit_measure_le_of_product_estimates
    {K : Type u} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (d : ℕ) (houtput : c.outputDegree = d) (t B : ℝ) (hB : 0 ≤ B)
    (hlow : LowProductBound R d t B) (hhigh : HighProductBound R d t B) :
    R (circuitValue c) ≤ (circuitSize c : ℝ) ^ 2 * B := by
  have hSB : 0 ≤ (circuitSize c : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hgates : ∀ u, gateCoefficient c.outputInputs u ≠ 0 →
      R (upperValue c u) ≤ (circuitSize c : ℝ) * B := by
    intro u hu
    obtain ⟨a, factors, _, hpos, hdegree, hval, _⟩ := upperValue_positive_factors c u
    have hdegree' : (factors.map c.middleDegree).sum = d :=
      hdegree.trans ((outputDegree_of_gateCoefficient_ne_zero c u hu).trans houtput)
    rw [hval]
    exact (hscale a _).trans
      (positive_middle_product_measure_le c R hzero hadd hscale d t B hB
        hlow hhigh factors hpos hdegree')
  have hcountNat : c.upperCount ≤ circuitSize c := by unfold circuitSize; omega
  have hcount : (c.upperCount : ℝ) ≤ circuitSize c := by exact_mod_cast hcountNat
  calc
    R (circuitValue c) ≤ (c.upperCount : ℝ) * ((circuitSize c : ℝ) * B) :=
      circuit_measure_le_upperCount_mul c R hzero hadd hscale _ hSB hgates
    _ ≤ (circuitSize c : ℝ) * ((circuitSize c : ℝ) * B) :=
      mul_le_mul_of_nonneg_right hcount hSB
    _ = (circuitSize c : ℝ) ^ 2 * B := by ring

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

lemma nearestIntegerDistance_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x :=
  abs_nonneg _

lemma nearestIntegerDistance_le_half (x : ℝ) : nearestIntegerDistance x ≤ 1 / 2 :=
  abs_sub_round x

lemma nearestIntegerDistance_even {e : ℕ} (he : Even e) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    nearestIntegerDistance ((e : ℝ) / 2 - δ) = δ := by
  rcases he with ⟨k, rfl⟩
  have hr : round (((k + k : ℕ) : ℝ) / 2 - δ) = (k : ℤ) := by
    apply round_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  rw [nearestIntegerDistance, hr]
  push_cast
  rw [show ((k : ℝ) + k) / 2 - δ - k = -δ by ring]
  simpa using abs_of_nonpos (neg_nonpos.mpr hδ)

lemma nearestIntegerDistance_odd {e : ℕ} (he : Odd e) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    nearestIntegerDistance ((e : ℝ) / 2 - δ) = 1 / 2 - δ := by
  rcases he with ⟨k, rfl⟩
  have hr : round (((2 * k + 1 : ℕ) : ℝ) / 2 - δ) = (k : ℤ) := by
    apply round_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  rw [nearestIntegerDistance, hr]
  push_cast
  rw [show ((2 * (k : ℝ) + 1) / 2 - δ - k) = 1 / 2 - δ by ring]
  exact abs_of_nonneg (sub_nonneg.mpr hδ')

lemma nearestIntegerDistance_half_sub_ge {e : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    δ ≤ nearestIntegerDistance ((e : ℝ) / 2 - δ) := by
  rcases Nat.even_or_odd e with he | he
  · rw [nearestIntegerDistance_even he hδ.le (by linarith)]
  · rw [nearestIntegerDistance_odd he hδ (by linarith)]
    linarith

lemma degreeDistance_eq_half_sub (n s : ℝ) (e : ℕ) :
    degreeDistance n s e = nearestIntegerDistance ((e : ℝ) / 2 - s * e / (2 * n)) := by
  unfold degreeDistance
  congr 1
  ring

lemma low_degree_offset {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) :
    0 < s * e / (2 * n) ∧ s * e / (2 * n) < 1 / 8 := by
  constructor
  · positivity
  · have hmul : (e : ℝ) * (4 * s) < n :=
      (lt_div_iff₀ (by positivity : 0 < 4 * s)).mp he'
    apply (div_lt_iff₀ (by positivity : 0 < 2 * n)).mpr
    nlinarith

lemma degreeDistance_even {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (heven : Even e) :
    degreeDistance n s e = s * e / (2 * n) := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_even heven hδ.le (by linarith)

lemma degreeDistance_odd {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    degreeDistance n s e = 1 / 2 - s * e / (2 * n) := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_odd hodd hδ (by linarith)

lemma degreeDistance_ge {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) :
    s * e / (2 * n) ≤ degreeDistance n s e := by
  rw [degreeDistance_eq_half_sub]
  obtain ⟨hδ, hδ'⟩ := low_degree_offset hn hs he he'
  exact nearestIntegerDistance_half_sub_ge hδ (by linarith)

lemma degreeDistance_odd_ge {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    {e : ℕ} (he : 0 < e) (he' : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    3 / 8 ≤ degreeDistance n s e := by
  rw [degreeDistance_odd hn hs he he' hodd]
  obtain ⟨_, hδ'⟩ := low_degree_offset hn hs he he'
  linarith

open scoped BigOperators

lemma sum_degreeDistance_ge {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s)) :
    s / (2 * n) * (∑ i ∈ I, (e i : ℝ)) ≤ ∑ i ∈ I, degreeDistance n s (e i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    s / (2 * n) * (e i : ℝ) = s * e i / (2 * n) := by ring
    _ ≤ degreeDistance n s (e i) := degreeDistance_ge hn hs (he i hi) (he' i hi)

lemma sum_degreeDistance_ge_half {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s : ℝ} (hn : 0 < n) (hs : 0 < s)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    s / 2 ≤ ∑ i ∈ I, degreeDistance n s (e i) := by
  have h := sum_degreeDistance_ge I e hn hs he he'
  rw [hsum] at h
  convert h using 1
  field_simp

lemma prod_degreeDistance_rpow_le {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s q : ℝ} (hn : 0 < n) (hs : 0 < s) (hq : 0 < q) (hq' : q ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    (∏ i ∈ I, q ^ (degreeDistance n s (e i) / 2)) ≤ q ^ (s / 4) := by
  rw [← Real.rpow_sum_of_pos hq]
  apply Real.rpow_le_rpow_of_exponent_ge hq hq'
  rw [← Finset.sum_div]
  have h := sum_degreeDistance_ge_half I e hn hs he he' hsum
  linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

lemma low_degree_power_saving {n s q : ℝ} (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hq' : q ≤ n ^ (-(2 / 5 : ℝ))) (hs : Real.sqrt n / 2 ≤ s) :
    q ^ (s / 4) ≤ n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  calc
    q ^ (s / 4) ≤ (n ^ (-(2 / 5 : ℝ))) ^ (s / 4) :=
      Real.rpow_le_rpow hq hq' (by positivity)
    _ = n ^ (-(s / 10)) := by rw [← Real.rpow_mul hn0]; congr 1; ring
    _ ≤ n ^ (-Real.sqrt n / 20) := by
      apply Real.rpow_le_rpow_of_exponent_le hn
      linarith

lemma prod_exp_corrections {ι : Type*} (I : Finset ι) (H d E : ι → ℝ)
    {q B : ℝ} (hq : 0 ≤ q) (hH : ∀ i ∈ I, 0 ≤ H i)
    (hbound : ∀ i ∈ I, H i ≤ q ^ d i * Real.exp (E i))
    (hE : ∑ i ∈ I, E i ≤ B) :
    (∏ i ∈ I, H i) ≤ (∏ i ∈ I, q ^ d i) * Real.exp B := by
  calc
    (∏ i ∈ I, H i) ≤ ∏ i ∈ I, q ^ d i * Real.exp (E i) :=
      Finset.prod_le_prod hH hbound
    _ = (∏ i ∈ I, q ^ d i) * Real.exp (∑ i ∈ I, E i) := by
      rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ i ∈ I, q ^ d i) * Real.exp B := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE)
      exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg hq (d i))

lemma all_low_degree_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    (H E : ι → ℝ) {n s q C : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hs' : Real.sqrt n / 2 ≤ s) (hq : 0 < q) (hq1 : q ≤ 1)
    (hq' : q ≤ n ^ (-(2 / 5 : ℝ)))
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) (hH : ∀ i ∈ I, 0 ≤ H i)
    (hbound : ∀ i ∈ I, H i ≤ q ^ (degreeDistance n s (e i) / 2) * Real.exp (E i))
    (hE : ∑ i ∈ I, E i ≤ C * Real.sqrt n) :
    (∏ i ∈ I, H i) ≤ Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 < n := by linarith
  calc
    (∏ i ∈ I, H i) ≤ (∏ i ∈ I, q ^ (degreeDistance n s (e i) / 2)) *
        Real.exp (C * Real.sqrt n) :=
      prod_exp_corrections I H _ E hq.le hH hbound hE
    _ ≤ q ^ (s / 4) * Real.exp (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right
        (prod_degreeDistance_rpow_le I e hn0 hs hq hq1 he he' hsum) (Real.exp_pos _).le
    _ ≤ n ^ (-Real.sqrt n / 20) * Real.exp (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right (low_degree_power_saving hn hq.le hq' hs') (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- For a zero-sum finite family, its total positive discrepancy is half of
its total absolute discrepancy.  This is the algebraic identity used when
ordering the factors in the product-rank argument. -/
theorem sum_positive_eq_half_sum_abs {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (hδ : ∑ j ∈ s, δ j = 0) :
    ∑ j ∈ s.filter (fun j => 0 < δ j), δ j =
      (∑ j ∈ s, |δ j|) / 2 := by
  classical
  have habs : ∀ j, |δ j| = 2 * (if 0 < δ j then δ j else 0) - δ j := by
    intro j
    by_cases h : 0 < δ j
    · rw [ite_eq_left h, abs_of_pos h]
      ring
    · rw [ite_eq_right h, abs_of_nonpos (le_of_not_gt h)]
      ring
  have hs : (∑ j ∈ s, |δ j|) =
      2 * (∑ j ∈ s.filter (fun j => 0 < δ j), δ j) := by
    simp_rw [habs]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hδ, sub_zero,
      Finset.sum_filter]
  linarith

/-- Collecting factors with positive proportional discrepancy expresses
precisely the dimension-saving exponent in terms of absolute discrepancies. -/
theorem positive_bidegree_identity {ι : Type*} (s : Finset ι)
    (e i : ι → ℝ) (ρ lam : ℝ)
    (hlam : (1 + ρ) * lam = ρ)
    (hδ : ∑ j ∈ s, (i j - lam * e j) = 0) :
    (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), i j) -
      ρ * (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), (e j - i j)) =
      (1 + ρ) / 2 * (∑ j ∈ s, |i j - lam * e j|) := by
  classical
  have hpoint : ∀ j, i j - ρ * (e j - i j) =
      (1 + ρ) * (i j - lam * e j) := by
    intro j
    nlinarith [congrArg (fun x : ℝ => x * e j) hlam]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [← Finset.mul_sum, sum_positive_eq_half_sum_abs s (fun j => i j - lam * e j) hδ]
  ring

/-- Conversion of the intermediate-dimension exponent to a product of
individual discrepancy weights. -/
theorem positive_bidegree_rpow {ι : Type*} (s : Finset ι)
    (e i : ι → ℝ) (ρ lam α : ℝ) (hα : 0 < α)
    (hlam : (1 + ρ) * lam = ρ)
    (hδ : ∑ j ∈ s, (i j - lam * e j) = 0) :
    α ^ ((∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), i j) -
      ρ * (∑ j ∈ s.filter (fun j => 0 < i j - lam * e j), (e j - i j))) =
      ∏ j ∈ s, (α ^ ((1 + ρ) / 2)) ^ |i j - lam * e j| := by
  rw [positive_bidegree_identity s e i ρ lam hlam hδ,
    Real.rpow_mul hα.le,
    Real.rpow_sum_of_pos (Real.rpow_pos_of_pos hα _) _ s]

/-- Dropping a constraint on independent choices and then distributing the
finite sums is valid for nonnegative weights. -/
theorem constrained_sum_prod_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} (t : (j : ι) → Finset (κ j))
    (w : (j : ι) → κ j → ℝ)
    (hw : ∀ j x, x ∈ t j → 0 ≤ w j x)
    (P : ((j : ι) → κ j) → Prop) [DecidablePred P] :
    (∑ x ∈ (Fintype.piFinset t).filter P, ∏ j, w j (x j)) ≤
      ∏ j, ∑ x ∈ t j, w j x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro x hx _
  apply Finset.prod_nonneg
  intro j _
  exact hw j (x j) ((Fintype.mem_piFinset.mp hx) j)

/-- The bidegree-constrained sum in the product-rank bound is at most the
product of the individual degree weights. -/
theorem bidegree_weight_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (k : ℕ) (q lam : ℝ) (hq : 0 ≤ q) :
    (∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k),
      ∏ j, q ^ |(i j : ℝ) - lam * e j|) ≤
      ∏ j, degreeWeight q lam (e j) := by
  classical
  exact constrained_sum_prod_le_prod_sum
    (fun j => Finset.range (e j + 1))
    (fun j i => q ^ |(i : ℝ) - lam * e j|)
    (fun _ _ _ => Real.rpow_nonneg hq _) _

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DegreeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

lemma latticeMajorant_nonneg {q : ℝ} (hq : 0 ≤ q) (d : ℝ) (z : ℤ) :
    0 ≤ latticeMajorant q d z := by
  unfold latticeMajorant
  split_ifs
  · exact Real.rpow_nonneg hq _
  · exact mul_nonneg (Real.rpow_nonneg hq _) (pow_nonneg hq _)

lemma hasSum_latticeMajorant {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (d : ℝ) :
    HasSum (latticeMajorant q d)
      (q ^ d + 2 * (q ^ (1 - d) / (1 - q))) := by
  have hgeom : HasSum (fun n : ℕ => q ^ (1 - d) * q ^ n)
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq hq1).mul_left (q ^ (1 - d))
  have hpval (n : ℕ) : latticeMajorant q d ((n : ℤ) + 1) =
      q ^ (1 - d) * q ^ n := by
    have hne : (n : ℤ) + 1 ≠ 0 := by omega
    have habs : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [latticeMajorant, ite_eq_right hne, habs, Nat.add_sub_cancel]
  have hnval (n : ℕ) : latticeMajorant q d (-((n : ℤ) + 1)) =
      q ^ (1 - d) * q ^ n := by
    have hne : -((n : ℤ) + 1) ≠ 0 := by omega
    have habs : ((n : ℤ) + 1).natAbs = n + 1 := by omega
    simp only [latticeMajorant, ite_eq_right hne, Int.natAbs_neg, habs, Nat.add_sub_cancel]
  have hp : HasSum (fun n : ℕ => latticeMajorant q d ((n : ℤ) + 1))
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [hpval] using hgeom
  have hn : HasSum (fun n : ℕ => latticeMajorant q d (-((n : ℤ) + 1)))
      (q ^ (1 - d) / (1 - q)) := by
    simpa only [hnval] using hgeom
  have h := hp.of_add_one_of_neg_add_one hn
  have hzero : latticeMajorant q d 0 = q ^ d := by simp [latticeMajorant]
  rw [hzero] at h
  convert h using 1
  ring

lemma rpow_abs_sub_le_latticeMajorant {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (y : ℝ) (z : ℤ) :
    q ^ |(z : ℝ) - y| ≤ latticeMajorant q |y| z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeMajorant]
  have hzpos : 1 ≤ z.natAbs := by
    have := Int.natAbs_pos.mpr hz
    omega
  have htriangle : (z.natAbs : ℝ) - |y| ≤ |(z : ℝ) - y| := by
    have h := abs_sub_abs_le_abs_sub (z : ℝ) y
    have heq : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      simp
    rw [heq] at h
    exact h
  calc
    q ^ |(z : ℝ) - y| ≤ q ^ ((z.natAbs : ℝ) - |y|) :=
      Real.rpow_le_rpow_of_exponent_ge hq hq1 htriangle
    _ = latticeMajorant q |y| z := by
      rw [latticeMajorant, ite_eq_right hz]
      have he : (z.natAbs : ℝ) - |y| = (1 - |y|) + ((z.natAbs - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hzpos]
        norm_num
      rw [he, Real.rpow_add hq, Real.rpow_natCast]

lemma sum_lattice_rpow_le {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (y : ℝ) (s : Finset ℤ) :
    ∑ z ∈ s, q ^ |(z : ℝ) - y| ≤
      q ^ |y| + 2 * (q ^ (1 - |y|) / (1 - q)) := by
  have hs := hasSum_latticeMajorant hq.le hq1 |y|
  calc
    ∑ z ∈ s, q ^ |(z : ℝ) - y| ≤ ∑ z ∈ s, latticeMajorant q |y| z :=
      Finset.sum_le_sum (fun z _ => rpow_abs_sub_le_latticeMajorant hq hq1.le y z)
    _ ≤ ∑' z : ℤ, latticeMajorant q |y| z :=
      hs.summable.sum_le_tsum s (fun z _ => latticeMajorant_nonneg hq.le |y| z)
    _ = _ := hs.tsum_eq

lemma sum_nat_rpow_le {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤
      q ^ nearestIntegerDistance x +
        2 * (q ^ (1 - nearestIntegerDistance x) / (1 - q)) := by
  unfold nearestIntegerDistance
  have h := sum_lattice_rpow_le hq hq1 (x - (round x : ℝ))
    (s.image (fun i : ℕ => (i : ℤ) - round x))
  rw [Finset.sum_image] at h
  · convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Int.cast_sub, Int.cast_natCast]
    congr 2
    ring
  · intro a ha b hb hab
    exact_mod_cast sub_left_injective hab

lemma rpow_geometric_bound {q d : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2) :
    q ^ d + 2 * (q ^ (1 - d) / (1 - q)) ≤
      q ^ d * (1 + 4 * q ^ (1 - 2 * d)) := by
  have hden : 0 < 1 - q := by linarith
  have hnum : 0 ≤ q ^ (1 - d) := Real.rpow_nonneg hq.le _
  have hdiv : q ^ (1 - d) / (1 - q) ≤ 2 * q ^ (1 - d) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hmul : q ^ d * q ^ (1 - 2 * d) = q ^ (1 - d) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  nlinarith

lemma rpow_geometric_bound_le_five {q d : ℝ} (hq : 0 < q)
    (hqhalf : q ≤ 1 / 2) (hd : 0 ≤ d) (hdhalf : d ≤ 1 / 2) :
    q ^ d * (1 + 4 * q ^ (1 - 2 * d)) ≤ 5 := by
  have hq1 : q ≤ 1 := by linarith
  have ha := Real.rpow_le_one hq.le hq1 hd
  have hb := Real.rpow_le_one hq.le hq1 (show 0 ≤ 1 - 2 * d by linarith)
  have hapos := Real.rpow_nonneg hq.le d
  have hbpos := Real.rpow_nonneg hq.le (1 - 2 * d)
  nlinarith

lemma sum_nat_rpow_le_nearest {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤
      q ^ nearestIntegerDistance x * (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance x)) :=
  (sum_nat_rpow_le hq (by linarith) x s).trans (rpow_geometric_bound hq hqhalf)

lemma sum_nat_rpow_le_five {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (x : ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, q ^ |(i : ℝ) - x| ≤ 5 :=
  (sum_nat_rpow_le_nearest hq hqhalf x s).trans
    (rpow_geometric_bound_le_five hq hqhalf
      (nearestIntegerDistance_nonneg x) (nearestIntegerDistance_le_half x))

/-- The nearest-integer geometric estimate for the manuscript's factor weight. -/
theorem degreeWeight_le_nearest {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) :
    degreeWeight q lam e ≤
      q ^ nearestIntegerDistance (lam * e) *
        (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance (lam * e))) :=
  sum_nat_rpow_le_nearest hq hqhalf (lam * e) (Finset.range (e + 1))

/-- Uniform upper bound for each factor weight, including arbitrarily high degrees. -/
theorem degreeWeight_le_five {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) : degreeWeight q lam e ≤ 5 :=
  sum_nat_rpow_le_five hq hqhalf (lam * e) (Finset.range (e + 1))

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.SmallDegreeCorrections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

/-- A convex chord controls the small-degree correction, without differentiating
its logarithm. -/
theorem rpow_one_sub_le_chord (q z : ℝ) (hq : 0 < q)
    (hz : 0 ≤ z) (hz' : z ≤ 1 / 4) :
    q ^ (1 - z) ≤ q + 4 * z * q ^ ((3 : ℝ) / 4) := by
  have hconv : q ^ ((1 - 4 * z) * 1 + 4 * z * (3 / 4)) ≤
      (1 - 4 * z) * q ^ (1 : ℝ) + 4 * z * q ^ ((3 : ℝ) / 4) :=
    (convexOn_rpow_left hq).2
      (Set.mem_univ (1 : ℝ)) (Set.mem_univ ((3 : ℝ) / 4))
      (by linarith) (by positivity) (by ring)
  simp only [Real.rpow_one] at hconv
  have heq : (1 - 4 * z) * 1 + 4 * z * (3 / 4) = 1 - z := by ring
  rw [heq] at hconv
  have hnonneg : 0 ≤ 4 * z * q := by positivity
  nlinarith

/-- Sum version of the chord estimate. -/
theorem sum_rpow_one_sub_le_chord {ι : Type*} (I : Finset ι)
    (q : ℝ) (z : ι → ℝ) (hq : 0 < q)
    (hz : ∀ i ∈ I, 0 ≤ z i) (hz' : ∀ i ∈ I, z i ≤ 1 / 4) :
    ∑ i ∈ I, q ^ (1 - z i) ≤
      (I.card : ℝ) * q + 4 * (∑ i ∈ I, z i) * q ^ ((3 : ℝ) / 4) := by
  calc
    _ ≤ ∑ i ∈ I, (q + 4 * z i * q ^ ((3 : ℝ) / 4)) :=
      Finset.sum_le_sum (fun i hi => rpow_one_sub_le_chord q (z i) hq (hz i hi) (hz' i hi))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum]

/-- The total low-degree correction is `O(sqrt n)`, uniformly in the number
and sizes of factors. The degree variables may be real; natural degrees are a
special case. -/
theorem sum_small_degree_corrections_le {ι : Type*} (I : Finset ι)
    (n s q : ℝ) (e : ι → ℝ)
    (hn : 0 < n) (hs : 0 ≤ s) (hs' : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqone : q ≤ 1) (hqsmall : q ≤ 2 / Real.sqrt n)
    (he : ∀ i ∈ I, 1 ≤ e i)
    (helow : ∀ i ∈ I, s * e i / n ≤ 1 / 4)
    (hesum : ∑ i ∈ I, e i ≤ n) :
    ∑ i ∈ I, q ^ (1 - s * e i / n) ≤ 6 * Real.sqrt n := by
  have hpos : ∀ i ∈ I, 0 ≤ s * e i / n := by
    intro i hi
    exact div_nonneg (mul_nonneg hs (le_trans zero_le_one (he i hi))) hn.le
  have hchord := sum_rpow_one_sub_le_chord I q
    (fun i => s * e i / n) hq hpos helow
  have hcard : (I.card : ℝ) ≤ n := by
    calc
      (I.card : ℝ) = ∑ i ∈ I, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ I, e i := Finset.sum_le_sum he
      _ ≤ n := hesum
  have hsum : (∑ i ∈ I, s * e i / n) ≤ s := by
    calc
      (∑ i ∈ I, s * e i / n) = s / n * ∑ i ∈ I, e i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ s / n * n := mul_le_mul_of_nonneg_left hesum (div_nonneg hs hn.le)
      _ = s := div_mul_cancel₀ s hn.ne'
  have hsumpos : 0 ≤ ∑ i ∈ I, s * e i / n := Finset.sum_nonneg hpos
  have hqpow : q ^ ((3 : ℝ) / 4) ≤ 1 := Real.rpow_le_one hq.le hqone (by norm_num)
  have hproduct : (∑ i ∈ I, s * e i / n) * q ^ ((3 : ℝ) / 4) ≤ s := by
    calc
      _ ≤ (∑ i ∈ I, s * e i / n) * 1 :=
        mul_le_mul_of_nonneg_left hqpow hsumpos
      _ ≤ s := by simpa using hsum
  have hcardq := mul_le_mul_of_nonneg_right hcard hq.le
  have hsqrtpos := Real.sqrt_pos.mpr hn
  have hqsqrt : q * Real.sqrt n ≤ 2 := (le_div_iff₀ hsqrtpos).mp hqsmall
  have hnq : n * q ≤ 2 * Real.sqrt n := by
    calc
      n * q = Real.sqrt n * (q * Real.sqrt n) := by
        nlinarith [Real.sq_sqrt hn.le]
      _ ≤ Real.sqrt n * 2 := mul_le_mul_of_nonneg_left hqsqrt hsqrtpos.le
      _ = 2 * Real.sqrt n := mul_comm _ _
  nlinarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowDegreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

lemma degreeWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (lam : ℝ) (e : ℕ) :
    0 ≤ degreeWeight q lam e :=
  Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg hq _)

lemma degreeWeight_le_five_mul_distance {q : ℝ} (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (lam : ℝ) (e : ℕ) :
    degreeWeight q lam e ≤ 5 * q ^ nearestIntegerDistance (lam * e) := by
  have hq1 : q ≤ 1 := by linarith
  have hd := nearestIntegerDistance_le_half (lam * e)
  have htail := Real.rpow_le_one hq.le hq1
    (show 0 ≤ 1 - 2 * nearestIntegerDistance (lam * e) by linarith)
  calc
    degreeWeight q lam e ≤ q ^ nearestIntegerDistance (lam * e) *
        (1 + 4 * q ^ (1 - 2 * nearestIntegerDistance (lam * e))) :=
      degreeWeight_le_nearest hq hqhalf lam e
    _ ≤ q ^ nearestIntegerDistance (lam * e) * 5 :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hq.le _)
    _ = _ := mul_comm _ _

lemma low_odd_degreeWeight_le {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) (hodd : Odd e) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤ q ^ (degreeDistance n s e / 2) := by
  have hq1 : q ≤ 1 := by linarith
  have hd := degreeDistance_odd_ge hn hs he helow hodd
  have hp : q ^ (degreeDistance n s e / 2) ≤ q ^ ((3 : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith)
  have hp5 : 5 * q ^ (degreeDistance n s e / 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (by norm_num)).trans hqsmall
  have hbound := degreeWeight_le_five_mul_distance hq hqhalf (1 / 2 - s / (2 * n)) e
  change degreeWeight q (1 / 2 - s / (2 * n)) e ≤ 5 * q ^ degreeDistance n s e at hbound
  calc
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤ 5 * q ^ degreeDistance n s e := hbound
    _ = (5 * q ^ (degreeDistance n s e / 2)) * q ^ (degreeDistance n s e / 2) := by
      rw [mul_assoc, ← Real.rpow_add hq]
      congr 2
      ring
    _ ≤ 1 * q ^ (degreeDistance n s e / 2) :=
      mul_le_mul_of_nonneg_right hp5 (Real.rpow_nonneg hq.le _)
    _ = _ := one_mul _

lemma low_even_degreeWeight_le {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) (heven : Even e) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤
      q ^ degreeDistance n s e * Real.exp (4 * q ^ (1 - s * e / n)) := by
  have hbound := degreeWeight_le_nearest hq hqhalf (1 / 2 - s / (2 * n)) e
  change degreeWeight q (1 / 2 - s / (2 * n)) e ≤ q ^ degreeDistance n s e *
    (1 + 4 * q ^ (1 - 2 * degreeDistance n s e)) at hbound
  have hexponent : 1 - 2 * degreeDistance n s e = 1 - s * e / n := by
    rw [degreeDistance_even hn hs he helow heven]
    ring
  rw [hexponent] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (by linarith [Real.add_one_le_exp (4 * q ^ (1 - s * e / n))])
    (Real.rpow_nonneg hq.le _))

lemma low_degreeWeight_le_with_correction {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    {e : ℕ} (he : 0 < e) (helow : (e : ℝ) < n / (4 * s)) :
    degreeWeight q (1 / 2 - s / (2 * n)) e ≤
      q ^ (degreeDistance n s e / 2) * Real.exp (4 * q ^ (1 - s * e / n)) := by
  have hq1 : q ≤ 1 := by linarith
  rcases Nat.even_or_odd e with heven | hodd
  · refine (low_even_degreeWeight_le hn hs hq hqhalf he helow heven).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hd : 0 ≤ degreeDistance n s e := nearestIntegerDistance_nonneg _
    linarith
  · refine (low_odd_degreeWeight_le hn hs hq hqhalf hqsmall he helow hodd).trans ?_
    have hexp : 1 ≤ Real.exp (4 * q ^ (1 - s * e / n)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
      (Real.rpow_nonneg hq.le (degreeDistance n s e / 2))

/-- The actual factor weights, rather than hypothetical costs, give the
all-low product saving in the circuit argument. -/
theorem low_degreeWeight_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    {n s q : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hslo : Real.sqrt n / 2 ≤ s) (hshi : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqpow : q ≤ n ^ (-(2 / 5 : ℝ))) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (helow : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) :
    (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      Real.exp (24 * Real.sqrt n) * n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 < n := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hcorr : (∑ i ∈ I, q ^ (1 - s * e i / n)) ≤ 6 * Real.sqrt n := by
    apply sum_small_degree_corrections_le I n s q (fun i => (e i : ℝ))
      hn0 hs.le hshi hq hq1 hqsqrt
    · intro i hi
      exact_mod_cast he i hi
    · intro i hi
      obtain ⟨_, h⟩ := low_degree_offset hn0 hs (he i hi) (helow i hi)
      have hid : s * e i / n = 2 * (s * e i / (2 * n)) := by ring
      rw [hid]
      linarith
    · exact hsum.le
  apply all_low_degree_product_bound I e
    (fun i => degreeWeight q (1 / 2 - s / (2 * n)) (e i))
    (fun i => 4 * q ^ (1 - s * e i / n)) hn hs hslo hq hq1 hqpow he helow hsum
  · exact fun i _ => degreeWeight_nonneg hq.le _ _
  · exact fun i hi => low_degreeWeight_le_with_correction hn0 hs hq hqhalf hqsmall
      (he i hi) (helow i hi)
  · rw [← Finset.mul_sum]
    linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ProductCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Numerical assembly of the product-rank estimates

These lemmas isolate the finite-product and real-power calculations in the
all-low and one-high cases of the circuit rank estimate.  All hypotheses on
individual factor costs and parameters remain explicit.
-/

open scoped BigOperators

namespace Problem335

/-- The favorable power from expanding one high-degree factor saves the exact
manuscript exponent `3*sqrt(n)/160`. -/
theorem one_high_power_saving (n q lam t : ℝ) (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hqbound : q ≤ n ^ (-(2 : ℝ) / 5)) (hlam : (3 : ℝ) / 8 ≤ lam)
    (ht : Real.sqrt n / 4 ≤ t) :
    q ^ (lam * t / 2) ≤ n ^ (-(3 * Real.sqrt n) / 160) := by
  have hlam0 : 0 ≤ lam := by linarith
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hlt : (3 / 8 : ℝ) * (Real.sqrt n / 4) ≤ lam * t :=
    mul_le_mul hlam ht (by positivity) hlam0
  calc
    q ^ (lam * t / 2) ≤ (n ^ (-(2 : ℝ) / 5)) ^ (lam * t / 2) :=
      Real.rpow_le_rpow hq hqbound (by positivity)
    _ = n ^ (-(lam * t) / 5) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ n)]
      congr 1
      ring
    _ ≤ n ^ (-(3 * Real.sqrt n) / 160) :=
      Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)

/-- The bounded loss per remaining large factor is exponential in `sqrt n`. -/
theorem high_factor_exponential_bound (n s : ℝ) (hs : s ≤ Real.sqrt n) :
    (5 : ℝ) ^ (4 * s) ≤ Real.exp (4 * Real.log 5 * Real.sqrt n) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The number of large positive-degree factor occurrences is charged to their
total degree, rather than to the number of distinct circuit gates. -/
theorem large_degree_count_mul_le_sum {ι : Type*} (s : Finset ι)
    (e : ι → ℝ) (t : ℝ) (he : ∀ j ∈ s, 0 ≤ e j) :
    ((s.filter (fun j => t ≤ e j)).card : ℝ) * t ≤ ∑ j ∈ s, e j := by
  classical
  calc
    ((s.filter (fun j => t ≤ e j)).card : ℝ) * t =
        ∑ j ∈ s.filter (fun j => t ≤ e j), t := by simp
    _ ≤ ∑ j ∈ s.filter (fun j => t ≤ e j), e j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    _ ≤ ∑ j ∈ s, e j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j hj _ => he j hj)

/-- Division form of the large-degree occurrence count. -/
theorem large_degree_count_le {ι : Type*} (s : Finset ι)
    (e : ι → ℝ) (t : ℝ) (ht : 0 < t) (he : ∀ j ∈ s, 0 ≤ e j) :
    ((s.filter (fun j => t ≤ e j)).card : ℝ) ≤ (∑ j ∈ s, e j) / t := by
  exact (le_div_iff₀ ht).mpr (large_degree_count_mul_le_sum s e t he)

/-- The all-low branch fits the common circuit-rank envelope.  No sign
assumption on the error constant `C` is required. -/
theorem all_low_common_rank_bound (n S D C : ℝ) (hn : 1 ≤ n)
    (hS : 1 ≤ S) (hD : 0 ≤ D) :
    2 * D * Real.exp (4 * C * Real.sqrt n) * n ^ (-Real.sqrt n / 20) ≤
      2 * S * D * Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) *
        n ^ (-Real.sqrt n / 100) := by
  have hc : 2 * D ≤ 2 * S * D := by nlinarith
  have he : Real.exp (4 * C * Real.sqrt n) ≤
      Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) := by
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ Real.log 5 * Real.sqrt n :=
      mul_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
    nlinarith
  have hp : n ^ (-Real.sqrt n / 20) ≤ n ^ (-Real.sqrt n / 100) :=
    Real.rpow_le_rpow_of_exponent_le hn (by nlinarith [Real.sqrt_nonneg n])
  exact mul_le_mul
    (mul_le_mul hc he (le_of_lt (Real.exp_pos _)) (by positivity)) hp
    (Real.rpow_nonneg (by linarith) _) (by positivity)

/-- The one-high branch fits the same envelope, absorbing the bounded cost of
all remaining high-degree factors. -/
theorem one_high_common_rank_bound (n s S D C : ℝ) (hn : 1 ≤ n)
    (hs : s ≤ Real.sqrt n) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    2 * S * D * (5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n) / 160) ≤
      2 * S * D * Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) *
        n ^ (-Real.sqrt n / 100) := by
  have he : (5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n) ≤
      Real.exp ((4 * C + 4 * Real.log 5) * Real.sqrt n) := by
    calc
      _ ≤ Real.exp (4 * Real.log 5 * Real.sqrt n) *
          Real.exp (4 * C * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right (high_factor_exponential_bound n s hs)
          (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : n ^ (-(3 * Real.sqrt n) / 160) ≤ n ^ (-Real.sqrt n / 100) :=
    Real.rpow_le_rpow_of_exponent_le hn (by nlinarith [Real.sqrt_nonneg n])
  calc
    _ = (2 * S * D) * ((5 : ℝ) ^ (4 * s) * Real.exp (4 * C * Real.sqrt n)) *
        n ^ (-(3 * Real.sqrt n) / 160) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hp
      (Real.rpow_nonneg (by linarith) _) (by positivity)

/-- Splitting large and small degrees multiplies their two distinct types of
cost, with the large-factor multiplicity retained exactly. -/
theorem prod_high_low_cost_le {ι : Type*} (s : Finset ι)
    (H err e : ι → ℝ) (t B E : ℝ)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hB : 0 ≤ B)
    (hhigh : ∀ j ∈ s, t ≤ e j → H j ≤ B)
    (hlow : ∀ j ∈ s, e j < t → H j ≤ Real.exp (err j))
    (herr : (∑ j ∈ s with e j < t, err j) ≤ E) :
    (∏ j ∈ s, H j) ≤
      B ^ (s.filter (fun j => t ≤ e j)).card * Real.exp E := by
  classical
  calc
    _ ≤ ∏ j ∈ s, if t ≤ e j then B else Real.exp (err j) := by
      apply Finset.prod_le_prod hH
      intro j hj
      split_ifs with h
      · exact hhigh j hj h
      · exact hlow j hj (lt_of_not_ge h)
    _ = B ^ (s.filter (fun j => t ≤ e j)).card *
        Real.exp (∑ j ∈ s with e j < t, err j) := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const, not_le, ← Real.exp_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
      (pow_nonneg hB _)

/-- A degree budget replaces the number of high factors by `N/t`. -/
theorem prod_high_low_cost_le_rpow {ι : Type*} (s : Finset ι)
    (H err e : ι → ℝ) (t B E N : ℝ) (ht : 0 < t)
    (hH : ∀ j ∈ s, 0 ≤ H j) (hB : 1 ≤ B)
    (he : ∀ j ∈ s, 0 ≤ e j) (hbudget : (∑ j ∈ s, e j) ≤ N)
    (hhigh : ∀ j ∈ s, t ≤ e j → H j ≤ B)
    (hlow : ∀ j ∈ s, e j < t → H j ≤ Real.exp (err j))
    (herr : (∑ j ∈ s with e j < t, err j) ≤ E) :
    (∏ j ∈ s, H j) ≤ B ^ (N / t) * Real.exp E := by
  have hcount : ((s.filter (fun j => t ≤ e j)).card : ℝ) ≤ N / t :=
    (large_degree_count_le s e t ht he).trans
      ((div_le_div_iff_of_pos_right ht).mpr hbudget)
  calc
    _ ≤ B ^ (s.filter (fun j => t ≤ e j)).card * Real.exp E :=
      prod_high_low_cost_le s H err e t B E hH (by linarith) hhigh hlow herr
    _ = B ^ ((s.filter (fun j => t ≤ e j)).card : ℝ) * Real.exp E := by
      rw [Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hB hcount) (le_of_lt (Real.exp_pos _))

/-- Expanding one factor of degree at least `t` supplies enough linear-factor
cost to obtain the favorable power `q^(lam*t/2)`. -/
theorem linear_factor_cost_power_le (H q lam t : ℝ) (e : ℕ)
    (hH : 0 ≤ H) (hq : 0 < q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam)
    (hcost : H ≤ q ^ (lam / 2)) (he : t ≤ (e : ℝ)) :
    H ^ e ≤ q ^ (lam * t / 2) := by
  calc
    H ^ e ≤ (q ^ (lam / 2)) ^ e := pow_le_pow_left₀ hH hcost e
    _ = q ^ (lam * (e : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hq)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hq hq1
      (by nlinarith [mul_le_mul_of_nonneg_left he hlam])

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.HighDegreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Remaining unexpanded factors cost at most one factor of five per large
occurrence, and a total exponential error for the low occurrences. -/
theorem remaining_degreeWeight_product_bound {ι : Type*} (I : Finset ι)
    (e : ι → ℕ) {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hshi : s ≤ Real.sqrt n) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (hsum : (∑ i ∈ I, (e i : ℝ)) ≤ n) :
    (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) := by
  classical
  have hq1 : q ≤ 1 := by linarith
  have ht : 0 < n / (4 * s) := by positivity
  have hcorr : (∑ i ∈ I with (e i : ℝ) < n / (4 * s),
      q ^ (1 - s * e i / n)) ≤ 6 * Real.sqrt n := by
    apply sum_small_degree_corrections_le
      (I.filter (fun i => (e i : ℝ) < n / (4 * s))) n s q
      (fun i => (e i : ℝ)) hn hs.le hshi hq hq1 hqsqrt
    · intro i hi
      exact_mod_cast he i (Finset.mem_filter.mp hi).1
    · intro i hi
      obtain ⟨hI, hlow⟩ := Finset.mem_filter.mp hi
      obtain ⟨_, h⟩ := low_degree_offset hn hs (he i hI) hlow
      have hid : s * e i / n = 2 * (s * e i / (2 * n)) := by ring
      rw [hid]
      linarith
    · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg (e i))).trans hsum
  have herr : (∑ i ∈ I with (e i : ℝ) < n / (4 * s),
      4 * q ^ (1 - s * e i / n)) ≤ 24 * Real.sqrt n := by
    rw [← Finset.mul_sum]
    linarith
  have hlow : ∀ i ∈ I, (e i : ℝ) < n / (4 * s) →
      degreeWeight q (1 / 2 - s / (2 * n)) (e i) ≤
        Real.exp (4 * q ^ (1 - s * e i / n)) := by
    intro i hi hlow
    have hw := low_degreeWeight_le_with_correction hn hs hq hqhalf hqsmall
      (he i hi) hlow
    have hd : 0 ≤ degreeDistance n s (e i) := nearestIntegerDistance_nonneg _
    have hp : q ^ (degreeDistance n s (e i) / 2) ≤ 1 :=
      Real.rpow_le_one hq.le hq1 (by positivity)
    exact hw.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
        (Real.exp_pos (4 * q ^ (1 - s * e i / n))).le)
  have h := prod_high_low_cost_le_rpow I
    (fun i => degreeWeight q (1 / 2 - s / (2 * n)) (e i))
    (fun i => 4 * q ^ (1 - s * e i / n)) (fun i => (e i : ℝ))
    (n / (4 * s)) 5 (24 * Real.sqrt n) n ht
    (fun i _ => degreeWeight_nonneg hq.le _ _) (by norm_num)
    (fun i _ => Nat.cast_nonneg (e i)) hsum
    (fun i _ _ => degreeWeight_le_five hq hqhalf _ _) hlow herr
  have hdiv : n / (n / (4 * s)) = 4 * s := by
    field_simp
  simpa only [hdiv] using h

/-- The actual factor weights in the one-high case obey the strong power
saving required by the homogeneous depth-five circuit rank argument. -/
theorem high_degreeWeight_product_bound {ι : Type*} (I : Finset ι)
    (e : ι → ℕ) (d : ℕ) {n s q : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hshi : s ≤ Real.sqrt n) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hqsqrt : q ≤ 2 / Real.sqrt n) (hqpow : q ≤ n ^ (-(2 : ℝ) / 5))
    (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (hlam : (3 : ℝ) / 8 ≤ 1 / 2 - s / (2 * n))
    (htone : 1 < n / (4 * s)) (hd : n / (4 * s) ≤ (d : ℝ))
    (he : ∀ i ∈ I, 0 < e i) (hsum : (∑ i ∈ I, (e i : ℝ)) ≤ n) :
    degreeWeight q (1 / 2 - s / (2 * n)) 1 ^ d *
        (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n) / 160) := by
  have hn0 : 0 < n := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hdist : degreeDistance n s 1 = 1 / 2 - s / (2 * n) := by
    simpa using degreeDistance_odd hn0 hs (by decide : 0 < (1 : ℕ))
      (by simpa using htone) (by decide : Odd (1 : ℕ))
  have hlinear : degreeWeight q (1 / 2 - s / (2 * n)) 1 ≤
      q ^ ((1 / 2 - s / (2 * n)) / 2) := by
    simpa only [hdist] using low_odd_degreeWeight_le hn0 hs hq hqhalf hqsmall
      (by decide : 0 < (1 : ℕ)) (by simpa using htone) (by decide : Odd (1 : ℕ))
  have hlinpow := linear_factor_cost_power_le
    (degreeWeight q (1 / 2 - s / (2 * n)) 1) q
    (1 / 2 - s / (2 * n)) (n / (4 * s)) d
    (degreeWeight_nonneg hq.le _ _) hq hq1 (by linarith) hlinear hd
  have hprod := remaining_degreeWeight_product_bound I e hn0 hs hshi hq
    hqhalf hqsqrt hqsmall he hsum
  have ht : Real.sqrt n / 4 ≤ n / (4 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).mpr
    have hm := mul_le_mul_of_nonneg_left hshi (Real.sqrt_nonneg n)
    nlinarith [Real.sq_sqrt hn0.le]
  have hpower := one_high_power_saving n q (1 / 2 - s / (2 * n))
    (n / (4 * s)) hn hq.le hqpow hlam ht
  calc
    _ ≤ q ^ ((1 / 2 - s / (2 * n)) * (n / (4 * s)) / 2) *
        ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n)) :=
      mul_le_mul hlinpow hprod
        (Finset.prod_nonneg (fun i _ => degreeWeight_nonneg hq.le _ _))
        (Real.rpow_nonneg hq.le _)
    _ ≤ n ^ (-(3 * Real.sqrt n) / 160) *
        ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n)) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = _ := by ring

/-- The circuit interface only assumes `n ≥ 64`: the required slope and
threshold bounds follow from `s ≤ sqrt n`. This adapter reconciles the
canonical high-weight estimate with the circuit product interface. -/
theorem expanded_degreeWeight_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    (d : ℕ) {n s q : ℝ} (hn : 64 ≤ n) (hs : 0 < s) (hshi : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqpow : q ≤ n ^ (-(2 / 5 : ℝ))) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (hsum : ∑ i ∈ I, (e i : ℝ) ≤ n)
    (hd : n / (4 * s) ≤ (d : ℝ)) :
    (degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ d *
      (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n / 160)) := by
  have hn0 : 0 < n := by linarith
  have hsq := Real.sq_sqrt hn0.le
  have hsqrt := Real.sqrt_nonneg n
  have hsqrt8 : 8 ≤ Real.sqrt n := by nlinarith
  have ht : Real.sqrt n / 4 ≤ n / (4 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hshi hsqrt]
  have hdiv : s / (2 * n) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
    nlinarith
  simpa only [neg_div] using high_degreeWeight_product_bound I e d
    (by linarith) hs hshi hq hqhalf hqsqrt (by simpa only [neg_div] using hqpow)
    hqsmall (by linarith) (by linarith) hd he hsum

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitWeightBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

private lemma sum_get_eq_map_sum {α M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

private lemma prod_get_eq_map_prod {α M : Type*} [CommMonoid M]
    (l : List α) (f : α → M) :
    (∏ i : Fin l.length, f (l.get i)) = (l.map f).prod := by
  rw [← List.prod_ofFn]
  change (List.ofFn (f ∘ l.get)).prod = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- A `Fin`-indexed product-rank theorem supplies the list interface used by circuits. -/
theorem homogeneousProductRankBound_of_fin {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (q lam D : ℝ)
    (h : ∀ (m : ℕ) (P : Fin m → MvPolynomial σ K) (e : Fin m → ℕ),
      (∀ i, 0 < e i) → (∀ i, (P i).IsHomogeneous (e i)) →
      (∑ i, e i) = n → R (∏ i, P i) ≤ 2 * D * ∏ i, degreeWeight q lam (e i)) :
    HomogeneousProductRankBound R n q lam D := by
  intro factors hf hsum
  have hsum' : (∑ i : Fin factors.length, (factors.get i).2) = n := by
    rw [sum_get_eq_map_sum factors Prod.snd]
    exact hsum
  have hb := h factors.length (fun i => (factors.get i).1) (fun i => (factors.get i).2)
    (fun i => (hf _ (List.get_mem _ _)).1)
    (fun i => (hf _ (List.get_mem _ _)).2) hsum'
  simpa only [prod_get_eq_map_prod factors Prod.fst,
    prod_get_eq_map_prod factors (fun f => degreeWeight q lam f.2)] using hb

lemma lowProductBound_of_product_rank {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (s q D : ℝ)
    (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    LowProductBound R n ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) := by
  intro factors hf hsum
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by have := hp.large; omega)
  have hsumreal : (∑ i : Fin factors.length, ((factors.get i).2 : ℝ)) = n := by
    rw [sum_get_eq_map_sum factors (fun f => (f.2 : ℝ))]
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using
      congrArg (fun k : ℕ => (k : ℝ)) hsum
  have hw := low_degreeWeight_product_bound Finset.univ (fun i : Fin factors.length => (factors.get i).2)
    hn1 hp.s_pos hp.s_lower hp.s_upper hp.q_pos hp.q_half hp.q_sqrt hp.q_pow hp.q_small
    (fun i _ => (hf _ (List.get_mem _ _)).1)
    (fun i _ => (hf _ (List.get_mem _ _)).2.2) hsumreal
  rw [prod_get_eq_map_prod factors (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)] at hw
  have hr := hprod factors (fun f h => ⟨(hf f h).1, (hf f h).2.1⟩) hsum
  have hcommon := all_low_common_rank_bound (n : ℝ) 1 D 6 hn1 (by norm_num) hD
  norm_num only [mul_one, one_mul] at hcommon
  calc
    R (factors.map Prod.fst).prod ≤
        2 * D * (factors.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod := hr
    _ ≤ 2 * D * (Real.exp (24 * Real.sqrt n) * (n : ℝ) ^ (-Real.sqrt n / 20)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ circuitProductEnvelope n D := by
      simpa only [circuitProductEnvelope, show (4 : ℝ) * 6 = 24 by norm_num,
        mul_assoc] using hcommon

lemma highProductBound_of_product_rank {K σ : Type*} [CommSemiring K]
    (R : MvPolynomial σ K → ℝ) (n : ℕ) (s q D : ℝ)
    (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    HighProductBound R n ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) := by
  intro linears others hlin hothers hlarge hsum
  have hn64 : 64 ≤ (n : ℝ) := by exact_mod_cast hp.large
  have hn1 : 1 ≤ (n : ℝ) := by linarith
  have hbudgetNat : (others.map Prod.snd).sum ≤ n := by omega
  have hbudget : (∑ i : Fin others.length, ((others.get i).2 : ℝ)) ≤ n := by
    rw [sum_get_eq_map_sum others (fun f => (f.2 : ℝ))]
    have hc : ((others.map Prod.snd).sum : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbudgetNat
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using hc
  have hw := expanded_degreeWeight_product_bound Finset.univ
    (fun i : Fin others.length => (others.get i).2) linears.length
    hn64 hp.s_pos hp.s_upper hp.q_pos hp.q_half hp.q_sqrt hp.q_pow hp.q_small
    (fun i _ => (hothers _ (List.get_mem _ _)).1) hbudget hlarge
  rw [prod_get_eq_map_prod others (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)] at hw
  let factors := linears.map (fun p => (p, 1)) ++ others
  have hfactor : ∀ f ∈ factors, 0 < f.2 ∧ f.1.IsHomogeneous f.2 := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hf
      exact ⟨by norm_num, hlin p hp'⟩
    · exact hothers f hf
  have htotal : (factors.map Prod.snd).sum = n := by
    simpa [factors, List.map_append, List.map_map, Function.comp_def] using hsum
  have hr := hprod factors hfactor htotal
  have hr' : R (linears.prod * (others.map Prod.fst).prod) ≤
      2 * D * ((degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ linears.length *
        (others.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod) := by
    simpa [factors, List.map_append, List.map_map, Function.comp_def] using hr
  have hcommon := one_high_common_rank_bound (n : ℝ) s 1 D 6 hn1 hp.s_upper
    (by norm_num) hD
  norm_num only [mul_one, one_mul] at hcommon
  calc
    R (linears.prod * (others.map Prod.fst).prod) ≤
        2 * D * ((degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ linears.length *
          (others.map (fun f => degreeWeight q (1 / 2 - s / (2 * n)) f.2)).prod) := hr'
    _ ≤ 2 * D * ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        (n : ℝ) ^ (-(3 * Real.sqrt n / 160))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ circuitProductEnvelope n D := by
      simpa only [circuitProductEnvelope, show (4 : ℝ) * 6 = 24 by norm_num,
        neg_div, mul_assoc] using hcommon

/-- The full circuit upper rank estimate, reducing the actual circuit only to
the homogeneous-product rank theorem and explicit numerical parameters. -/
theorem circuit_rank_bound_from_product_rank
    {K : Type*} [CommSemiring K] {n : ℕ} (c : Depth5Circuit K n)
    (R : MvPolynomial (Fin n × Fin n × Fin n) K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ x y, R (x + y) ≤ R x + R y)
    (hscale : ∀ a p, R (MvPolynomial.C a * p) ≤ R p)
    (s q D : ℝ) (hp : WeightParameters n s q) (hD : 0 ≤ D)
    (houtput : c.outputDegree = n)
    (hprod : HomogeneousProductRankBound R n q (1 / 2 - s / (2 * n)) D) :
    R (circuitValue c) ≤ 2 * (circuitSize c : ℝ) ^ 2 * D *
      Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) * (n : ℝ) ^ (-Real.sqrt n / 100) := by
  have hB : 0 ≤ circuitProductEnvelope n D := by
    unfold circuitProductEnvelope
    positivity
  have h := circuit_measure_le_of_product_estimates c R hzero hadd hscale n houtput
    ((n : ℝ) / (4 * s)) (circuitProductEnvelope n D) hB
    (lowProductBound_of_product_rank R n s q D hp hD hprod)
    (highProductBound_of_product_rank R n s q D hp hD hprod)
  calc
    R (circuitValue c) ≤ (circuitSize c : ℝ) ^ 2 * circuitProductEnvelope n D := h
    _ = _ := by unfold circuitProductEnvelope; ring

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.Bidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace Bidegree

open MvPolynomial Finsupp

variable {σ R : Type*} [CommSemiring R]

theorem weight_add_complement (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (weight side) d +
      Finsupp.weight (weight (fun x => !(side x))) d = d.degree := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases h : side x <;> simp [weight, h]

theorem weight_le_degree (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (weight side) d ≤ d.degree := by
  have := weight_add_complement side d
  omega

theorem component_isWeightedHomogeneous (side : σ → Bool) (i : ℕ)
    (p : MvPolynomial σ R) :
    (component side i p).IsWeightedHomogeneous (weight side) i :=
  weightedHomogeneousComponent_isWeightedHomogeneous i p

/-- A homogeneous polynomial is the sum of its bidegree components. -/
theorem sum_components (side : σ → Bool) {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (∑ i ∈ Finset.range (n + 1), component side i p) = p := by
  classical
  ext d
  simp only [coeff_sum, coeff_component]
  by_cases hd : p.coeff d = 0
  · simp [hd]
  · have hn := hp hd
    change Finsupp.weight (fun _ : σ => 1) d = n at hn
    have hle := weight_le_degree side d
    rw [Finsupp.degree_eq_weight_one] at hle
    have hmem : Finsupp.weight (weight side) d ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single (Finsupp.weight (weight side) d)]
    · simp
    · intro b hb hne
      simp [Ne.symm hne]
    · exact fun h => (h hmem).elim

theorem component_of_weightedHomogeneous (side : σ → Bool)
    {p : MvPolynomial σ R} {i : ℕ}
    (hp : p.IsWeightedHomogeneous (weight side) i) (k : ℕ) :
    component side k p = if k = i then p else 0 := by
  classical
  exact weightedHomogeneousComponent_of_mem hp

/-- Distributing a finite product over all choices of bidegrees. -/
theorem prod_eq_sum_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) :
    (∏ a, p a) =
      ∑ f ∈ Fintype.piFinset (fun a => Finset.range (e a + 1)),
        ∏ a, component side (f a) (p a) := by
  classical
  calc
    (∏ a, p a) = ∏ a, ∑ i ∈ Finset.range (e a + 1), component side i (p a) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (sum_components side (hp a)).symm
    _ = _ := Finset.prod_univ_sum _ _

/-- Projection of the product keeps exactly degree assignments whose sum is `k`. -/
theorem component_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : σ → Bool) (p : ι → MvPolynomial σ R) (e : ι → ℕ)
    (hp : ∀ a, (p a).IsHomogeneous (e a)) (k : ℕ) :
    component side k (∏ a, p a) =
      ∑ f ∈ Fintype.piFinset (fun a => Finset.range (e a + 1)),
        if (∑ a, f a) = k then ∏ a, component side (f a) (p a) else 0 := by
  classical
  rw [prod_eq_sum_components side p e hp, map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  have hprod : (∏ a, component side (f a) (p a)).IsWeightedHomogeneous
      (weight side) (∑ a, f a) := by
    exact IsWeightedHomogeneous.prod _ _ _ (fun a ha =>
      component_isWeightedHomogeneous side (f a) (p a))
  rw [component_of_weightedHomogeneous side hprod]
  simp only [eq_comm]

end Bidegree
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OperatorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bigraded polynomial spaces used by the differentiation--multiplication rank measure.
The Boolean partition assigns derivative variables to `true` and multiplication
variables to `false`.
-/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*}

variable [CommSemiring K]

 theorem bidegreeComponent_eq_self {isV : σ → Bool} {a b : ℕ}
    {p : MvPolynomial σ K} (hp : p ∈ bidegreeSubmodule isV a b) :
    bidegreeComponent isV a b p = p :=
  MvPolynomial.weightedHomogeneousComponent_eq_self hp

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial
variable {σ R : Type*} [CommSemiring R]

/-- The paired weight is exactly the two complementary indicator weights. -/
theorem bidegreeWeight_eq_pair (side : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight side) d =
      (Finsupp.weight (Bidegree.weight side) d,
       Finsupp.weight (Bidegree.weight (fun x => !(side x))) d) := by
  classical
  apply Prod.ext <;>
    simp only [Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
      Prod.smul_fst, Prod.smul_snd] <;>
    apply Finset.sum_congr rfl <;>
    intro x hx <;>
    cases h : side x <;> simp [bidegreeWeight, Bidegree.weight, h]

/-- On total degree `n`, a single degree projection already fixes the other degree. -/
theorem bidegreeComponent_sub_eq_component (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    bidegreeComponent side i (n - i) p = Bidegree.component side i p := by
  classical
  ext d
  rw [coeff_bidegreeComponent, Bidegree.coeff_component, bidegreeWeight_eq_pair]
  by_cases hz : p.coeff d = 0
  · simp [hz]
  · have hn := hp hz
    change Finsupp.weight (fun _ : σ => 1) d = n at hn
    have hsum := Bidegree.weight_add_complement side d
    rw [Finsupp.degree_eq_weight_one] at hsum
    by_cases hi : Finsupp.weight (Bidegree.weight side) d = i
    · have hj : Finsupp.weight (Bidegree.weight (fun x => !(side x))) d = n - i := by
        omega
      simp [hi, hj]
    · simp [hi]

theorem component_mem_bidegreeSubmodule (side : σ → Bool) (i : ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    Bidegree.component side i p ∈ bidegreeSubmodule side i (n - i) := by
  rw [← bidegreeComponent_sub_eq_component side i hp]
  exact bidegreeComponent_mem side i (n - i) p

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.RankMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-dimensional rank bookkeeping

The differentiation--multiplication measure is obtained by applying a linear
family of linear maps to a polynomial. Its rank can be studied independently
of the construction of that family and the choice of homogeneous spaces.
-/

noncomputable section

open scoped BigOperators

namespace Problem335
namespace RankMeasure

universe u v w x y

variable {K : Type u} [Field K]
variable {P : Type v} [AddCommGroup P] [Module K P]
variable {V : Type w} [AddCommGroup V] [Module K V]
variable {W : Type x} [AddCommGroup W] [Module K W]
variable {Z : Type y} [AddCommGroup Z] [Module K Z]

theorem mapRank_smul_le [FiniteDimensional K V] (f : V →ₗ[K] W) (a : K) :
    mapRank (a • f) ≤ mapRank f := by
  exact Submodule.finrank_mono (LinearMap.range_smul_le_range f a)

theorem mapRank_add_le [FiniteDimensional K V] (f g : V →ₗ[K] W) :
    mapRank (f + g) ≤ mapRank f + mapRank g := by
  have h := LinearMap.rank_add_le f g
  rw [LinearMap.rank, LinearMap.rank, LinearMap.rank,
    ← Module.finrank_eq_rank, ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem mapRank_comp_le_left [FiniteDimensional K Z]
    (f : V →ₗ[K] Z) (g : Z →ₗ[K] W) :
    mapRank (g.comp f) ≤ mapRank g := by
  apply Submodule.finrank_mono
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range

/-- Factorization through a finite-dimensional intermediate space bounds rank. -/
theorem mapRank_factor_le [FiniteDimensional K Z]
    (f : V →ₗ[K] Z) (g : Z →ₗ[K] W) :
    mapRank (g.comp f) ≤ Module.finrank K Z :=
  (mapRank_comp_le_left f g).trans g.finrank_range_le

/-- Changing to finite bases identifies our rank convention with matrix rank. -/
theorem mapRank_eq_matrixRank {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W) (f : V →ₗ[K] W) :
    mapRank f = (LinearMap.toMatrix bV bW f).rank := by
  classical
  rw [Matrix.rank_eq_finrank_range_toLin _ bW bV]
  rw [Matrix.toLin_toMatrix]
  rfl

/-- The rank of a restricted map does not depend on whether its codomain is
viewed as a subspace or as the ambient space. -/
theorem mapRank_subtype_comp (S : Submodule K W) (f : V →ₗ[K] S) :
    mapRank (S.subtype.comp f) = mapRank f := by
  unfold mapRank
  rw [LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype f.range).finrank_eq.symm

theorem measure_smul_le [FiniteDimensional K V]
    (F : P →ₗ[K] (V →ₗ[K] W)) (a : K) (p : P) :
    measure F (a • p) ≤ measure F p := by
  simpa only [measure, map_smul] using mapRank_smul_le (F p) a

theorem measure_add_le [FiniteDimensional K V]
    (F : P →ₗ[K] (V →ₗ[K] W)) (p q : P) :
    measure F (p + q) ≤ measure F p + measure F q := by
  simpa only [measure, map_add] using mapRank_add_le (F p) (F q)

end RankMeasure
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FiniteOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-source rank measure and its product decomposition. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

 theorem bidegreeRank_add_le [Finite σ] (isV : σ → Bool) (a b k m : ℕ)
    (q r : MvPolynomial σ K) :
    bidegreeRank isV a b k m (q + r) ≤
      bidegreeRank isV a b k m q + bidegreeRank isV a b k m r :=
  RankMeasure.measure_add_le _ q r

/-- The intrinsic finite-dimensional map and the ambient-codomain rank agree. -/
theorem finiteMixedOperator_rank (isV : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) :
    RankMeasure.mapRank (finiteMixedOperator isV a b k m q) =
      bidegreeRank isV a b k m q := by
  have h := RankMeasure.mapRank_subtype_comp
    (bidegreeSubmodule (K := K) isV (a - k) (b + m))
    (finiteMixedOperator isV a b k m q)
  exact h.symm

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IntermediateFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factorization of mixed operators through intermediate bidegree spaces.
The codomain is initially the full polynomial space.  Restricting it to a
bidegree submodule leaves the range dimension unchanged, as proved below. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K : Type*} [Field K]

/-- Factorization is an equality of actual linear maps, not merely a rank
inequality.  The rightmost polynomial factor operates first. -/
theorem sourceMixedOperator_mul_factorization (isV : σ → Bool) (a b c d : ℕ)
    (p q : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    sourceMixedOperator isV a b (q * p) =
      (sourceMixedOperator isV c d q).comp
        (intermediateStart isV a b c d p h) := by
  apply LinearMap.ext
  intro f
  exact mixedOperator_mul_apply isV q p f

/-- Any factorization through an intermediate bidegree space bounds rank by
that space's dimension. -/
theorem sourceMixedOperator_mul_rank_le [Finite σ]
    (isV : σ → Bool) (a b c d : ℕ) (p q : MvPolynomial σ K)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV p (f : MvPolynomial σ K) ∈ bidegreeSubmodule isV c d) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (q * p)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV c d) := by
  rw [sourceMixedOperator_mul_factorization isV a b c d p q h]
  exact RankMeasure.mapRank_factor_le _ _

/-- The bidegree of a selected subproduct is the sum of the selected
bidegrees, with no condition on the unselected factors. -/
theorem selected_bidegree_product_mem {ι : Type*} (s : Finset ι)
    (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (i j : ι → ℕ) (isV : σ → Bool)
    (hQ : ∀ l ∈ s, Q l ∈ bidegreeSubmodule isV (i l) (j l)) :
    (∏ l ∈ s.filter selected, Q l) ∈
      bidegreeSubmodule isV (∑ l ∈ s.filter selected, i l)
        (∑ l ∈ s.filter selected, j l) := by
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (s.filter selected) Q
    (fun l => (i l, j l)) (w := bidegreeWeight isV)
    (fun l hl => hQ l (Finset.mem_filter.mp hl).1)
  rw [← prod_mk_sum] at hp
  exact hp

/-- In a commutative polynomial product, any chosen group of factors can be
applied first.  In the product-rank proof this group consists of the factors
with positive proportional bidegree discrepancy. -/
theorem sourceMixedOperator_prod_rank_le [Finite σ] {ι : Type*}
    (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (isV : σ → Bool) (a b c d : ℕ)
    (h : ∀ f : bidegreeSubmodule (K := K) isV a b,
      mixedOperator isV (∏ j ∈ s.filter selected, Q j) (f : MvPolynomial σ K) ∈
        bidegreeSubmodule isV c d) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (∏ j ∈ s, Q j)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV c d) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not s selected Q, mul_comm]
  exact sourceMixedOperator_mul_rank_le isV a b c d _ _ h

/-- A selected homogeneous subproduct gives the actual intermediate dimension
bound.  Only its total derivative degree needs to fit inside the source. -/
theorem sourceMixedOperator_homogeneous_prod_rank_le [Finite σ] {ι : Type*}
    (s : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (Q : ι → MvPolynomial σ K) (i j : ι → ℕ) (isV : σ → Bool) (a b : ℕ)
    (hQ : ∀ l ∈ s, Q l ∈ bidegreeSubmodule isV (i l) (j l))
    (hi : (∑ l ∈ s.filter selected, i l) ≤ a) :
    RankMeasure.mapRank (sourceMixedOperator isV a b (∏ l ∈ s, Q l)) ≤
      Module.finrank K (bidegreeSubmodule (K := K) isV
        (a - ∑ l ∈ s.filter selected, i l)
        (b + ∑ l ∈ s.filter selected, j l)) := by
  apply sourceMixedOperator_prod_rank_le s selected Q isV a b
  intro f
  exact mixedOperator_mem_bidegreeSubmodule isV hi
    (selected_bidegree_product_mem s selected Q i j isV hQ) f.property

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OperatorRankBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of the finite-source APIs used by the product bound and the trace bound. -/
noncomputable section

namespace Problem335

variable {σ K : Type*} [Field K]

/-- The independently useful source-only constructions define the same linear family. -/
theorem sourceMixedOperator_eq_rawOperatorFamily (side : σ → Bool) (a b : ℕ) :
    sourceMixedOperator (K := K) side a b = rawOperatorFamily side a b := by
  ext q p
  rfl

/-- The canonical rank is the source-only rank of the paired projection. -/
theorem bidegreeRank_eq_source_measure (side : σ → Bool) (a b k m : ℕ)
    (q : MvPolynomial σ K) :
    bidegreeRank side a b k m q =
      RankMeasure.measure (sourceMixedOperator side a b) (bidegreeComponent side k m q) := by
  rw [sourceMixedOperator_eq_rawOperatorFamily]
  rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.HomogeneousSpaceDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

universe u v w

/-- The number of monomials of total degree `d`. -/
theorem card_degree_exponents (σ : Type u) [Fintype σ] (d : ℕ) :
    Nat.card { m : σ →₀ ℕ // m.degree = d } =
      Nat.multichoose (Fintype.card σ) d := by
  rw [Nat.card_congr (degreeExponentsEquivSym σ d)]
  simpa only [Nat.card_eq_fintype_card] using Sym.natCard_sym_eq_multichoose (α := σ) d

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

universe u v

/-- Counting bidegree monomials separates into the two variable groups. -/
theorem card_bidegree_finsupp_exponents {σ : Type u} [Fintype σ]
    (side : σ → Bool) (a b : ℕ) :
    Nat.card {m : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) m = (a, b)} =
      Nat.multichoose (Fintype.card {i : σ // side i = true}) a *
      Nat.multichoose (Fintype.card {i : σ // side i = false}) b := by
  rw [Nat.card_congr (bidegreeFinsuppExponentsEquiv side a b), Nat.card_prod,
    card_degree_exponents, card_degree_exponents]

/-- Exact finite dimension of the polynomial subspace used by the mixed operator. -/
theorem bidegreeSubmodule_finrank (K : Type u) [Field K]
    {σ : Type v} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    Module.finrank K (bidegreeSubmodule (K := K) side a b) =
      Nat.multichoose (Fintype.card {i : σ // side i = true}) a *
      Nat.multichoose (Fintype.card {i : σ // side i = false}) b := by
  unfold bidegreeSubmodule
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank K (MvPolynomial.restrictSupport K
    {m : σ →₀ ℕ | Finsupp.weight (bidegreeWeight side) m = (a, b)}) = _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact card_bidegree_finsupp_exponents side a b

/-- Stars-and-bars form, with no nonemptiness hypothesis needed. -/
theorem bidegreeSubmodule_finrank_choose (K : Type u) [Field K]
    {σ : Type v} [Fintype σ] (side : σ → Bool) (a b : ℕ) :
    Module.finrank K (bidegreeSubmodule (K := K) side a b) =
      Nat.choose (Fintype.card {i : σ // side i = true} + a - 1) a *
      Nat.choose (Fintype.card {i : σ // side i = false} + b - 1) b := by
  rw [bidegreeSubmodule_finrank, Nat.multichoose_eq, Nat.multichoose_eq]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BinomialRatios
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binomial dimension estimates for the intermediate spaces in the
differentiation--multiplication rank argument. -/

namespace Problem335

theorem homogeneousDim_pos {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    0 < homogeneousDim r t := by
  apply Nat.choose_pos
  omega

theorem homogeneousDim_succ_mul {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    homogeneousDim r (t + 1) * (t + 1) = homogeneousDim r t * (r + t) := by
  have h := Nat.add_one_mul_choose_eq (r + t - 1) t
  have hrt : r + t - 1 + 1 = r + t := by omega
  have hrt' : r + (t + 1) - 1 = r + t := by omega
  simpa only [homogeneousDim, hrt, hrt', Nat.mul_comm] using h.symm

theorem homogeneousDim_succ_cast {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    (homogeneousDim r (t + 1) : ℝ) =
      (homogeneousDim r t : ℝ) * ((r : ℝ) + t) / ((t : ℝ) + 1) := by
  apply (eq_div_iff (by positivity : (t : ℝ) + 1 ≠ 0)).2
  exact_mod_cast homogeneousDim_succ_mul hr t

theorem homogeneousDim_cast_eq_succ {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    (homogeneousDim r t : ℝ) =
      (homogeneousDim r (t + 1) : ℝ) * ((t : ℝ) + 1) / ((r : ℝ) + t) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  apply (eq_div_iff (by positivity : (r : ℝ) + t ≠ 0)).2
  exact_mod_cast (homogeneousDim_succ_mul hr t).symm

/-- Moving down one degree costs at most the largest ratio on the interval. -/
theorem homogeneousDim_down_step {r a t : ℕ} (hr : 1 ≤ r)
    (ht : t + 1 ≤ a) :
    (homogeneousDim r t : ℝ) ≤
      (homogeneousDim r (t + 1) : ℝ) *
        ((a : ℝ) / ((a : ℝ) + r - 1)) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht' : (t : ℝ) + 1 ≤ a := by exact_mod_cast ht
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hden : (0 : ℝ) < (a : ℝ) + r - 1 := by linarith
  have hratio : ((t : ℝ) + 1) / ((r : ℝ) + t) ≤
      (a : ℝ) / ((a : ℝ) + r - 1) := by
    apply (div_le_div_iff₀ (by linarith) hden).2
    nlinarith
  rw [homogeneousDim_cast_eq_succ hr t, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)

/-- Moving up one degree costs at most the initial coarse ratio. -/
theorem homogeneousDim_up_step {r b t : ℕ} (hr : 1 ≤ r)
    (hb : 0 < b) (ht : b ≤ t) :
    (homogeneousDim r (t + 1) : ℝ) ≤
      (homogeneousDim r t : ℝ) * (((b : ℝ) + r) / b) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ht' : (b : ℝ) ≤ t := by exact_mod_cast ht
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hratio : ((r : ℝ) + t) / ((t : ℝ) + 1) ≤
      ((b : ℝ) + r) / b := by
    apply (div_le_div_iff₀ (by positivity) hb').2
    nlinarith
  rw [homogeneousDim_succ_cast hr t, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)

/-- Iterating the descending degree ratio. -/
theorem homogeneousDim_down_bound {r a : ℕ} (hr : 1 ≤ r) (I : ℕ) :
    I ≤ a → (homogeneousDim r (a - I) : ℝ) ≤
      (homogeneousDim r a : ℝ) * ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hq : 0 ≤ (a : ℝ) / ((a : ℝ) + r - 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    linarith [Nat.cast_nonneg (α := ℝ) a]
  induction I with
  | zero => simp
  | succ I ih =>
      intro hI
      have hindex : a - (I + 1) + 1 = a - I := by omega
      have hstep := homogeneousDim_down_step (a := a) (t := a - (I + 1)) hr
        (by omega)
      rw [hindex] at hstep
      calc
        (homogeneousDim r (a - (I + 1)) : ℝ) ≤
            (homogeneousDim r (a - I) : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) := hstep
        _ ≤ ((homogeneousDim r a : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hq
        _ = (homogeneousDim r a : ℝ) *
              ((a : ℝ) / ((a : ℝ) + r - 1)) ^ (I + 1) := by
          rw [pow_succ, mul_assoc]

/-- Iterating the ascending degree ratio. -/
theorem homogeneousDim_up_bound {r b : ℕ} (hr : 1 ≤ r) (hb : 0 < b) (J : ℕ) :
    (homogeneousDim r (b + J) : ℝ) ≤
      (homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ J := by
  have hq : 0 ≤ ((b : ℝ) + r) / b := by positivity
  induction J with
  | zero => simp
  | succ J ih =>
      calc
        (homogeneousDim r (b + (J + 1)) : ℝ) ≤
            (homogeneousDim r (b + J) : ℝ) * (((b : ℝ) + r) / b) := by
          simpa only [Nat.add_assoc] using
            homogeneousDim_up_step hr hb (Nat.le_add_right b J)
        _ ≤ ((homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ J) *
              (((b : ℝ) + r) / b) := mul_le_mul_of_nonneg_right ih hq
        _ = (homogeneousDim r b : ℝ) * (((b : ℝ) + r) / b) ^ (J + 1) := by
          rw [pow_succ, mul_assoc]

theorem homogeneousDim_down_ratio {r a I : ℕ} (hr : 1 ≤ r) (hI : I ≤ a) :
    (homogeneousDim r (a - I) : ℝ) / homogeneousDim r a ≤
      ((a : ℝ) / ((a : ℝ) + r - 1)) ^ I := by
  have hd : (0 : ℝ) < homogeneousDim r a := by
    exact_mod_cast homogeneousDim_pos hr a
  apply (div_le_iff₀ hd).2
  simpa only [mul_comm] using homogeneousDim_down_bound hr I hI

theorem homogeneousDim_up_ratio {r b : ℕ} (hr : 1 ≤ r) (hb : 0 < b) (J : ℕ) :
    (homogeneousDim r (b + J) : ℝ) / homogeneousDim r b ≤
      (((b : ℝ) + r) / b) ^ J := by
  have hd : (0 : ℝ) < homogeneousDim r b := by
    exact_mod_cast homogeneousDim_pos hr b
  apply (div_le_iff₀ hd).2
  simpa only [mul_comm] using homogeneousDim_up_bound hr hb J

/-- The product of the two degree-space ratios bounds the relative size
of the intermediate space in the mixed operator factorization. -/
theorem intermediate_dimension_ratio_le {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (hb : 0 < b) (hI : I ≤ a) :
    ((homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J)) /
        ((homogeneousDim v a : ℝ) * homogeneousDim u b) ≤
      ((a : ℝ) / ((a : ℝ) + v - 1)) ^ I *
        (((b : ℝ) + u) / b) ^ J := by
  rw [← div_mul_div_comm]
  apply mul_le_mul (homogeneousDim_down_ratio hv hI)
    (homogeneousDim_up_ratio hu hb J)
  · positivity
  · apply pow_nonneg
    apply div_nonneg (Nat.cast_nonneg _)
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    linarith [Nat.cast_nonneg (α := ℝ) a]

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.DimensionCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem335

/-- A uniform Bernoulli bound for the rounding correction in the descending
homogeneous-space dimension ratio. -/
theorem inverse_one_sub_pow_le_two (N : ℝ) (I : ℕ)
    (hN : 1 ≤ N) (hI : 2 * (I : ℝ) ≤ N) :
    ((1 - 1 / N) ^ I)⁻¹ ≤ 2 := by
  have hNpos : 0 < N := by linarith
  have hinv : 1 / N ≤ 1 := (div_le_one hNpos).2 hN
  have hber := one_add_mul_le_pow (a := -(1 / N)) (by linarith : -2 ≤ -(1 / N)) I
  have hfrac : (I : ℝ) / N ≤ 1 / 2 := (div_le_iff₀ hNpos).2 (by linarith)
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 1 / N) ^ I := by
    simp only [mul_neg, mul_one_div, ← sub_eq_add_neg] at hber
    nlinarith
  have hpow : 0 < (1 - 1 / N) ^ I := lt_of_lt_of_le (by norm_num) hhalf
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpow).2
  linarith

/-- Rounding loss and the balanced multiplication cost combine into one
absolute-discrepancy exponent. -/
theorem corrected_ratio_product_le (α β N ρ : ℝ) (I J : ℕ)
    (hα : 0 < α) (hβ : α ^ ρ ≤ β)
    (hN : 1 ≤ N) (hI : 2 * (I : ℝ) ≤ N) :
    (α / (1 - 1 / N)) ^ I * β ^ (-(J : ℝ)) ≤
      2 * α ^ ((I : ℝ) - ρ * J) := by
  have hβpos : 0 < β := lt_of_lt_of_le (Real.rpow_pos_of_pos hα _) hβ
  have hdown : (α / (1 - 1 / N)) ^ I ≤ 2 * α ^ I := by
    rw [div_pow, div_eq_mul_inv]
    have := mul_le_mul_of_nonneg_left (inverse_one_sub_pow_le_two N I hN hI)
      (pow_nonneg hα.le I)
    simpa only [mul_comm] using this
  have hup := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hα ρ) hβ
    (neg_nonpos.mpr (Nat.cast_nonneg J))
  rw [← Real.rpow_mul hα.le] at hup
  calc
    _ ≤ (2 * α ^ I) * α ^ (ρ * -(J : ℝ)) :=
      mul_le_mul hdown hup (Real.rpow_nonneg hβpos.le _) (by positivity)
    _ = 2 * α ^ ((I : ℝ) - ρ * J) := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hα]
      congr 2
      ring

/-- The exact intermediate-dimension bound after the harmless rounding factor
has been absorbed. The hypotheses are purely numerical and field-independent. -/
theorem intermediate_dimension_ratio_le_balanced {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b) (hI : I ≤ a)
    (hbudget : 2 * I ≤ a + v) (ρ : ℝ)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    ((homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J)) /
        ((homogeneousDim v a : ℝ) * homogeneousDim u b) ≤
      2 * ((a : ℝ) / ((a : ℝ) + v)) ^ ((I : ℝ) - ρ * J) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hN : (1 : ℝ) < (a : ℝ) + v := by linarith
  have hdown : (a : ℝ) / ((a : ℝ) + v - 1) =
      ((a : ℝ) / ((a : ℝ) + v)) / (1 - 1 / ((a : ℝ) + v)) := by
    field_simp
  have hup : (((b : ℝ) + u) / b) ^ J =
      ((b : ℝ) / ((b : ℝ) + u)) ^ (-(J : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow, inv_div]
  calc
    _ ≤ ((a : ℝ) / ((a : ℝ) + v - 1)) ^ I *
        (((b : ℝ) + u) / b) ^ J := intermediate_dimension_ratio_le hv hu hb hI
    _ = ((((a : ℝ) / ((a : ℝ) + v)) / (1 - 1 / ((a : ℝ) + v))) ^ I) *
        ((b : ℝ) / ((b : ℝ) + u)) ^ (-(J : ℝ)) := by rw [hdown, hup]
    _ ≤ _ := corrected_ratio_product_le _ _ _ ρ I J (by positivity) hbalance hN.le
      (by exact_mod_cast hbudget)

/-- Unnormalized form of the balanced intermediate-dimension estimate. -/
theorem intermediate_dimension_le_balanced {v u a b I J : ℕ}
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b) (hI : I ≤ a)
    (hbudget : 2 * I ≤ a + v) (ρ : ℝ)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (homogeneousDim v (a - I) : ℝ) * homogeneousDim u (b + J) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ((a : ℝ) / ((a : ℝ) + v)) ^ ((I : ℝ) - ρ * J) := by
  have hd : (0 : ℝ) < (homogeneousDim v a : ℝ) * homogeneousDim u b := by
    exact mul_pos (by exact_mod_cast homogeneousDim_pos hv a)
      (by exact_mod_cast homogeneousDim_pos hu b)
  have h := (div_le_iff₀ hd).mp
    (intermediate_dimension_ratio_le_balanced (J := J) hv hu ha hb hI hbudget ρ hbalance)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.IntermediateDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

theorem positiveBidegreeV_le {ι : Type*} (s : Finset ι) (e i : ι → ℕ) (lam : ℝ) :
    positiveBidegreeV s e i lam ≤ ∑ j ∈ s, i j := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)

/-- Natural bidegree assignments give exactly the discrepancy-weight product. -/
theorem positiveBidegree_rpow {ι : Type*} (s : Finset ι) (e i : ι → ℕ)
    (ρ lam α : ℝ) (hα : 0 < α) (hie : ∀ j ∈ s, i j ≤ e j)
    (hlam : (1 + ρ) * lam = ρ)
    (hbalance : lam * (∑ j ∈ s, e j : ℕ) = (∑ j ∈ s, i j : ℕ)) :
    α ^ ((positiveBidegreeV s e i lam : ℝ) - ρ * positiveBidegreeU s e i lam) =
      ∏ j ∈ s, (α ^ ((1 + ρ) / 2)) ^ |(i j : ℝ) - lam * e j| := by
  classical
  have hzero : ∑ j ∈ s, ((i j : ℝ) - lam * e j) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    norm_cast at hbalance ⊢
    exact sub_eq_zero.mpr hbalance.symm
  have hcast : (positiveBidegreeU s e i lam : ℝ) =
      ∑ j ∈ s.filter (fun j => 0 < (i j : ℝ) - lam * e j), ((e j : ℝ) - i j) := by
    unfold positiveBidegreeU positiveBidegreeSet
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.cast_sub (hie j (Finset.mem_filter.mp hj).1)
  rw [hcast]
  simp only [positiveBidegreeV, positiveBidegreeSet, Nat.cast_sum]
  exact positive_bidegree_rpow s (fun j => (e j : ℝ)) (fun j => (i j : ℝ))
    ρ lam α hα hlam hzero

/-- The intermediate space associated to an admissible natural bidegree
assignment is bounded by its product of discrepancy weights. -/
theorem intermediate_dimension_le_weight_product {ι : Type*} (s : Finset ι)
    (e i : ι → ℕ) (k n v u a b : ℕ) (ρ lam : ℝ)
    (hie : ∀ j ∈ s, i j ≤ e j)
    (he : ∑ j ∈ s, e j = n) (hi : ∑ j ∈ s, i j = k)
    (hproportion : lam * n = k) (hlam : (1 + ρ) * lam = ρ)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ ρ ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (homogeneousDim v (a - positiveBidegreeV s e i lam) : ℝ) *
        homogeneousDim u (b + positiveBidegreeU s e i lam) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ∏ j ∈ s, (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + ρ) / 2)) ^
          |(i j : ℝ) - lam * e j| := by
  have hVk : positiveBidegreeV s e i lam ≤ k := by
    simpa only [hi] using positiveBidegreeV_le s e i lam
  have hVa : positiveBidegreeV s e i lam ≤ a := hVk.trans hka
  have hVbudget : 2 * positiveBidegreeV s e i lam ≤ a + v := by omega
  have hα : 0 < (a : ℝ) / ((a : ℝ) + v) := by positivity
  have hprop : lam * (∑ j ∈ s, e j : ℕ) = (∑ j ∈ s, i j : ℕ) := by
    rw [he, hi]
    exact hproportion
  have h := intermediate_dimension_le_balanced
    (I := positiveBidegreeV s e i lam) (J := positiveBidegreeU s e i lam)
    hv hu ha hb hVa hVbudget ρ hbalance
  rw [positiveBidegree_rpow s e i ρ lam _ hα hie hlam hprop] at h
  exact h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ProductRankAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace ProductRankAssembly

variable {σ K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]

/-- The rank subadditivity step, stated for a real-valued polynomial measure. -/
theorem measure_sum_le (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    {α : Type*} (s : Finset α) (f : α → MvPolynomial σ K) :
    R (∑ a ∈ s, f a) ≤ ∑ a ∈ s, R (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hadd _ _).trans (add_le_add le_rfl ih)

/-- A product's fixed bidegree has rank at most the sum over exactly those
assignments with matching total degree. -/
theorem measure_component_product_le_sum
    (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    (side : σ → Bool) (p : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ) :
    R (Bidegree.component side k (∏ j, p j)) ≤
      ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), R (∏ j, Bidegree.component side (i j) (p j)) := by
  classical
  have hdecomp : Bidegree.component side k (∏ j, p j) =
      ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), ∏ j, Bidegree.component side (i j) (p j) := by
    rw [Bidegree.component_prod side p e hp k, Finset.sum_filter]
  rw [hdecomp]
  exact measure_sum_le R hzero hadd _ _

/-- The constrained bidegree decomposition and the nonnegative assignment sum
turn per-assignment weight bounds into the product-rank estimate. -/
theorem measure_component_product_le_degreeWeight
    (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    (side : σ → Bool) (p : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ)
    (C q lam : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hterm : ∀ i : ι → ℕ, (∀ j, i j ≤ e j) → (∑ j, i j) = k →
      R (∏ j, Bidegree.component side (i j) (p j)) ≤
        C * ∏ j, q ^ |(i j : ℝ) - lam * e j|) :
    R (Bidegree.component side k (∏ j, p j)) ≤
      C * ∏ j, degreeWeight q lam (e j) := by
  classical
  calc
    _ ≤ ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), R (∏ j, Bidegree.component side (i j) (p j)) :=
      measure_component_product_le_sum R hzero hadd side p e hp k
    _ ≤ ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), C * ∏ j, q ^ |(i j : ℝ) - lam * e j| := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi, hsum⟩ := Finset.mem_filter.mp hi
      apply hterm i _ hsum
      intro j
      have hj := (Fintype.mem_piFinset.mp hi) j
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    _ = C * (∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), ∏ j, q ^ |(i j : ℝ) - lam * e j|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∏ j, degreeWeight q lam (e j) :=
      mul_le_mul_of_nonneg_left (bidegree_weight_sum_le e k q lam hq) hC

end ProductRankAssembly
end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ProductRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed-operator product-rank estimate.  Unlike the abstract assembly
lemma, the intermediate-space rank bounds here are proved from the actual
operator, and its dimension is computed from the two variable groups. -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]

/-- The product-rank lemma for a homogeneous product, under the elementary
numerical hypotheses on the source degrees and balancing ratios.
There is no circuit or polynomial rank hypothesis in this statement. -/
theorem mixed_product_rank_le
    (side : σ → Bool) (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j))
    (k n v u a b : ℕ) (rho lam : ℝ)
    (hvcard : Fintype.card {x : σ // side x = true} = v)
    (hucard : Fintype.card {x : σ // side x = false} = u)
    (he : ∑ j, e j = n) (hproportion : lam * n = k)
    (hslope : (1 + rho) * lam = rho)
    (hv : 1 ≤ v) (hu : 1 ≤ u) (ha : 0 < a) (hb : 0 < b)
    (hka : k ≤ a) (hbudget : 2 * k ≤ a + v)
    (hbalance : ((a : ℝ) / ((a : ℝ) + v)) ^ rho ≤
      (b : ℝ) / ((b : ℝ) + u)) :
    (RankMeasure.mapRank (sourceMixedOperator side a b
      (bidegreeComponent side k (n - k) (∏ j, Q j))) : ℝ) ≤
      2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b) *
        ∏ j, degreeWeight (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + rho) / 2)) lam (e j) := by
  classical
  have htotal : (∏ j, Q j).IsHomogeneous n := by
    rw [← he]
    exact MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => hQ j)
  rw [bidegreeComponent_sub_eq_component side k htotal]
  change (RankMeasure.measure (sourceMixedOperator side a b)
    (Bidegree.component side k (∏ j, Q j)) : ℝ) ≤ _
  refine ProductRankAssembly.measure_component_product_le_degreeWeight
    (fun p => (RankMeasure.measure (sourceMixedOperator side a b) p : ℝ))
    (by simp) ?_ side Q e hQ k
    (2 * ((homogeneousDim v a : ℝ) * homogeneousDim u b))
    (((a : ℝ) / ((a : ℝ) + v)) ^ ((1 + rho) / 2)) lam
    (by positivity) (by positivity) ?_
  · intro p q
    exact_mod_cast RankMeasure.measure_add_le (sourceMixedOperator side a b) p q
  · intro i hie hi
    have hIa : positiveBidegreeV Finset.univ e i lam ≤ a := by
      calc
        _ ≤ ∑ j, i j := positiveBidegreeV_le Finset.univ e i lam
        _ = k := hi
        _ ≤ a := hka
    have hrank := sourceMixedOperator_homogeneous_prod_rank_le Finset.univ
      (fun j => 0 < (i j : ℝ) - lam * e j)
      (fun j => Bidegree.component side (i j) (Q j))
      i (fun j => e j - i j) side a b
      (fun j _ => component_mem_bidegreeSubmodule side (i j) (hQ j)) hIa
    rw [bidegreeSubmodule_finrank_choose K side, hvcard, hucard] at hrank
    have hrankR :
        (RankMeasure.measure (sourceMixedOperator side a b)
          (∏ j, Bidegree.component side (i j) (Q j)) : ℝ) ≤
        (homogeneousDim v (a - positiveBidegreeV Finset.univ e i lam) : ℝ) *
          homogeneousDim u (b + positiveBidegreeU Finset.univ e i lam) := by
      exact_mod_cast hrank
    exact hrankR.trans (intermediate_dimension_le_weight_product Finset.univ
      e i k n v u a b rho lam (fun j _ => hie j) he hi
      hproportion hslope hv hu ha hb hka hbudget hbalance)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualProductRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-rank estimates specialized to the actual rounded rank parameters. -/
noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

theorem sourceDimension_pos {n : ℕ} (hn : 4 ≤ n) : 0 < sourceDimension n := by
  unfold sourceDimension
  exact mul_pos (by exact_mod_cast homogeneousDim_pos (v_pos hn) (a n))
    (by exact_mod_cast homogeneousDim_pos (u_pos hn) (b n))

theorem slope_lambda {n : ℕ} (hn : 4 ≤ n) :
    (1 + rho n) * lambda n = rho n := by
  rw [lambda_eq_rho_div hn]
  have h : 1 + rho n ≠ 0 := by have := rho_pos hn; linarith
  exact mul_div_cancel₀ _ h

theorem twice_k_le_a_add_v {n : ℕ} (hn : 4 ≤ n) :
    2 * k n ≤ a n + v n := by
  have h := k_mul_n_le_a hn
  have hmul : 2 * k n ≤ k n * n := by nlinarith
  omega

/-- All numerical hypotheses of the mixed product-rank lemma hold for our
chosen parameters. Only the cardinalities of the variable partition remain. -/
theorem actual_mixed_product_rank_le
    {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n)
    (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (he : ∑ j, e j = n) :
    (RankMeasure.mapRank (sourceMixedOperator side (a n) (b n)
      (bidegreeComponent side (k n) (m n) (∏ j, Q j))) : ℝ) ≤
      2 * sourceDimension n * ∏ j, degreeWeight (q n) (lambda n) (e j) := by
  have hmk : n - k n = m n := by have := k_add_m n; omega
  simpa only [hmk, sourceDimension, q, alpha] using
    mixed_product_rank_le side Q e hQ (k n) n (v n) (u n) (a n) (b n)
      (rho n) (lambda n) hvcard hucard he (lambda_mul_n n) (slope_lambda hn)
      (v_pos hn) (u_pos hn) (a_pos hn) (b_pos hn) (k_le_a hn)
      (twice_k_le_a_add_v hn) (alpha_rpow_rho_le_beta hn)

/-- The canonical finite-source rank has the actual-parameter product bound. -/
theorem actual_bidegreeRank_product_le
    {σ K ι : Type*} [Fintype σ] [Field K] [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n)
    (Q : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hQ : ∀ j, (Q j).IsHomogeneous (e j)) (he : ∑ j, e j = n) :
    (bidegreeRank side (a n) (b n) (k n) (m n) (∏ j, Q j) : ℝ) ≤
      2 * sourceDimension n * ∏ j, degreeWeight (q n) (lambda n) (e j) := by
  rw [bidegreeRank_eq_source_measure]
  exact actual_mixed_product_rank_le hn side hvcard hucard Q e hQ he

/-- The full list interface consumed by the circuit estimate, with every
analytic and operator-rank hypothesis discharged for the actual parameters. -/
theorem actual_homogeneousProductRankBound
    {σ K : Type*} [Fintype σ] [Field K]
    {n : ℕ} (hn : 4 ≤ n) (side : σ → Bool)
    (hvcard : Fintype.card {x : σ // side x = true} = v n)
    (hucard : Fintype.card {x : σ // side x = false} = u n) :
    HomogeneousProductRankBound
      (fun p : MvPolynomial σ K =>
        (bidegreeRank side (a n) (b n) (k n) (m n) p : ℝ))
      n (q n) (lambda n) (sourceDimension n) := by
  apply homogeneousProductRankBound_of_fin
  intro r P e _hepos hP he
  exact actual_bidegreeRank_product_le hn side hvcard hucard P e hP he

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OddDegreeThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform eventual smallness used to absorb the constant loss in the odd
low-degree estimate.  The threshold is independent of the factor degree and
of the particular parameter `q` below its stated envelope. -/

open Filter

namespace Problem335

/-- A polynomially decaying envelope absorbs every fixed positive power
and fixed nonnegative multiplicative constant, uniformly below the envelope. -/
theorem eventually_small_power_of_envelope (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q →
      q ≤ (n : ℝ) ^ (-a) → C * q ^ b ≤ 1 := by
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(a * b)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (mul_pos ha hb)).comp
        tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (-(a * b)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N, ?_⟩
  intro n hn q hq henv
  calc
    C * q ^ b ≤ C * ((n : ℝ) ^ (-a)) ^ b :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq henv hb.le) hC
    _ = C * (n : ℝ) ^ (-(a * b)) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 2
      ring
    _ ≤ 1 := (hN n hn).le

/-- The exact eventual smallness hypothesis used for all low odd degrees. -/
theorem eventually_odd_degree_smallness :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q →
      q ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) →
      5 * q ^ (3 / 16 : ℝ) ≤ 1 := by
  exact eventually_small_power_of_envelope (2 / 5) (3 / 16) 5
    (by norm_num) (by norm_num) (by norm_num)

end Problem335

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FractionRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335

/-- Quantitative monotonicity of the fraction used in the rounded rank parameters. -/
theorem fraction_rounding_ratio_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    1 ≤ (a / (a + v)) / (x / (x + v)) ∧
      (a / (a + v)) / (x / (x + v)) ≤ 1 + 1 / x := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hxv : 0 < x + v := add_pos hx hv
  have hav : 0 < a + v := add_pos ha hv
  have hratio : (a / (a + v)) / (x / (x + v)) =
      a * (x + v) / (x * (a + v)) := by field_simp
  rw [hratio]
  constructor
  · apply (le_div_iff₀ (mul_pos hx hav)).mpr
    nlinarith
  · apply (div_le_iff₀ (mul_pos hx hav)).mpr
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp
    nlinarith

/-- Equivalent multiplicative exponential form of the rounding estimate. -/
theorem fraction_rounding_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    x / (x + v) ≤ a / (a + v) ∧
      a / (a + v) ≤ x / (x + v) * Real.exp (1 / x) := by
  have hbase : 0 < x / (x + v) := div_pos hx (add_pos hx hv)
  obtain ⟨hlo, hhi⟩ := fraction_rounding_ratio_bounds hx hv hxa hax
  constructor
  · exact (one_le_div hbase).mp hlo
  · have hexp : 1 + 1 / x ≤ Real.exp (1 / x) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / x)
    have hratio := hhi.trans hexp
    exact (div_le_iff₀ hbase).mp hratio |>.trans_eq (mul_comm _ _)

/-- The first rank parameter has ideal fraction `1/s`; here `s = sqrt n`. -/
theorem fraction_natCeil_inverse_bounds {s v : ℝ} (hs : 1 < s) (hv : 0 < v) :
    let a : ℝ := ⌈v / (s - 1)⌉₊
    1 / s ≤ a / (a + v) ∧
      a / (a + v) ≤ 1 / s * Real.exp ((s - 1) / v) := by
  have hsm : 0 < s - 1 := sub_pos.mpr hs
  have hx : 0 < v / (s - 1) := div_pos hv hsm
  have hbase : (v / (s - 1)) / (v / (s - 1) + v) = 1 / s := by
    field_simp
    ring
  have hinv : 1 / (v / (s - 1)) = (s - 1) / v := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

/-- The second rank parameter is rounded from a prescribed target fraction `p`. -/
theorem fraction_natCeil_target_bounds {p v : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hv : 0 < v) :
    let b : ℝ := ⌈v * p / (1 - p)⌉₊
    p ≤ b / (b + v) ∧
      b / (b + v) ≤ p * Real.exp ((1 - p) / (v * p)) := by
  have hpm : 0 < 1 - p := sub_pos.mpr hp1
  have hx : 0 < v * p / (1 - p) := div_pos (mul_pos hv hp) hpm
  have hbase : (v * p / (1 - p)) / (v * p / (1 - p) + v) = p := by
    field_simp
    ring
  have hinv : 1 / (v * p / (1 - p)) = (1 - p) / (v * p) := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PowerPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small change in exponent from one to `rho` does not destroy the
inverse-square-root scale of the rounded operator parameters. -/

noncomputable section
open Filter Topology

namespace Problem335.PowerPerturbation

lemma tendsto_error : Tendsto error atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  convert (hlog.const_mul 2).add (hinv.const_mul 2) using 1
  · funext x
    simp [error, div_eq_mul_inv, mul_assoc]
  · norm_num

lemma eventually_error_le_log_two :
    ∀ᶠ n : ℝ in atTop, error n ≤ Real.log 2 := by
  exact tendsto_error.eventually_le_const (Real.log_pos (by norm_num))

/-- Deterministic perturbation estimate, with all rounding and exponent
hypotheses explicit. The extra `exp (1/n)` allows a second ceiling error. -/
lemma rpow_mul_exp_le {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n) :
    a ^ e * Real.exp (1 / n) ≤
      n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hi0 : 0 ≤ 1 / n := by positivity
  have hlog : Real.log a ≤ -(Real.log n / 2) + 1 / n := by
    have h := Real.log_le_log ha haUpper
    rw [Real.log_mul (Real.rpow_pos_of_pos hn0 _).ne' (Real.exp_ne_zero _),
      Real.log_rpow hn0, Real.log_exp] at h
    convert h using 1; ring
  have h1 := mul_le_mul_of_nonneg_right hlog he0
  have h2 := mul_le_mul_of_nonneg_right hgap hl0
  have h3 := mul_le_mul_of_nonneg_right he1 hi0
  have hexp : Real.log a * e + 1 / n ≤
      Real.log n * (-(1 / 2 : ℝ)) + error n := by
    unfold error
    simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
    nlinarith
  rw [Real.rpow_def_of_pos ha, ← Real.exp_add,
    Real.rpow_def_of_pos hn0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

lemma rpow_mul_exp_le_two {n a e : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (haUpper : a ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (1 / n))
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hgap : 1 - e ≤ 4 / Real.sqrt n)
    (herr : error n ≤ Real.log 2) :
    a ^ e * Real.exp (1 / n) ≤ 2 / Real.sqrt n := by
  calc
    a ^ e * Real.exp (1 / n) ≤ n ^ (-(1 / 2 : ℝ)) * Real.exp (error n) :=
      rpow_mul_exp_le hn ha haUpper he0 he1 hgap
    _ ≤ n ^ (-(1 / 2 : ℝ)) * 2 := by
      gcongr
      exact (Real.exp_le_exp.mpr herr).trans_eq (Real.exp_log (by norm_num))
    _ = 2 / Real.sqrt n := by
      rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
      ring

/-- Uniform in both the rounded parameter and the varying exponent. -/
theorem eventually_rpow_mul_exp_le_two :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a e : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ e → e ≤ 1 → 1 - e ≤ 4 / Real.sqrt (n : ℝ) →
      a ^ e * Real.exp (1 / (n : ℝ)) ≤ 2 / Real.sqrt (n : ℝ) := by
  have he := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually eventually_error_le_log_two
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max n₀ 1, fun n hn a e ha haUpper he0 he1 hgap => ?_⟩
  apply rpow_mul_exp_le_two (by exact_mod_cast (le_trans (le_max_right _ _) hn))
    ha haUpper he0 he1 hgap
  exact hn₀ n (le_trans (le_max_left _ _) hn)

/-- The exponent used for `q` is also covered by the uniform estimate. -/
theorem eventually_q_beta_bounds :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ a rho beta : ℝ,
      0 < a → a ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) →
      0 ≤ rho → rho ≤ 1 → 1 - rho ≤ 4 / Real.sqrt (n : ℝ) →
      beta ≤ a ^ rho * Real.exp (1 / (n : ℝ)) →
      a ^ ((1 + rho) / 2) ≤ 2 / Real.sqrt (n : ℝ) ∧
      beta ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := eventually_rpow_mul_exp_le_two
  refine ⟨n₀, fun n hn a rho beta ha haUpper hr0 hr1 hgap hbeta => ?_⟩
  constructor
  · have he0 : 0 ≤ (1 + rho) / 2 := by linarith
    have he1 : (1 + rho) / 2 ≤ 1 := by linarith
    have hegap : 1 - (1 + rho) / 2 ≤ 4 / Real.sqrt (n : ℝ) := by linarith
    calc
      a ^ ((1 + rho) / 2) = a ^ ((1 + rho) / 2) * 1 := (mul_one _).symm
      _ ≤ a ^ ((1 + rho) / 2) * Real.exp (1 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ha.le _)
        exact Real.one_le_exp_iff.mpr (by positivity)
      _ ≤ 2 / Real.sqrt (n : ℝ) := h n hn a _ ha haUpper he0 he1 hegap
  · exact hbeta.trans (h n hn a rho ha haUpper hr0 hr1 hgap)

/-- The inverse-square-root estimate implies both weaker bounds used in the
circuit rank analysis after increasing the absolute threshold. -/
theorem eventually_inverse_sqrt_bounds :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      2 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) ∧
      2 / Real.sqrt (n : ℝ) ≤ 1 / 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop 2)
  refine ⟨max n₀ 16, fun n hn => ?_⟩
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  have hn0 : 0 < (n : ℝ) := by linarith
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs4 : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hn0.le).2
    norm_num
    exact_mod_cast hn16
  constructor
  · calc
      2 / Real.sqrt (n : ℝ) = 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
        rfl
      _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (hn₀ n (le_trans (le_max_left _ _) hn))
        positivity
      _ = (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
        rw [← Real.rpow_add hn0]
        norm_num
  · apply (div_le_iff₀ hs0).2
    linarith

end Problem335.PowerPerturbation

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of the numerical inequalities for the actual rank parameters. -/
noncomputable section
namespace Problem335.LowerParameters

theorem n_le_a0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ a0 n := by
  have hk : (1 : ℝ) ≤ k n := by exact_mod_cast k_pos hn
  calc
    (n : ℝ) ≤ (k n : ℝ) * (n : ℝ) := by nlinarith
    _ ≤ a0 n := k_mul_n_le_a0 hn

theorem n_le_b0 {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ≤ b0 n :=
  ((n_le_a0 hn).trans (a0_le_a n)).trans (a_le_b0 hn)

theorem alpha_le_inv_sqrt_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ * Real.exp (1 / (n : ℝ)) := by
  have hs := sqrt_ge_two hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : alpha n ≤ (Real.sqrt (n : ℝ))⁻¹ *
      Real.exp ((Real.sqrt (n : ℝ) - 1) / (v n : ℝ)) := by
    simpa [alpha, a, a0, one_div] using
      (fraction_natCeil_inverse_bounds (by linarith : 1 < Real.sqrt (n : ℝ)) hv).2
  have herr : (Real.sqrt (n : ℝ) - 1) / (v n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_a0 hn)
    simpa [a0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (by positivity))

theorem alpha_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (1 / (n : ℝ)) := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  exact alpha_le_inv_sqrt_mul_exp hn

theorem beta_le_rpow_mul_exp {n : ℕ} (hn : 4 ≤ n) :
    beta n ≤ (alpha n) ^ (rho n) * Real.exp (1 / (n : ℝ)) := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hraw : beta n ≤ (alpha n) ^ (rho n) *
      Real.exp ((1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n))) := by
    simpa [beta, b, b0] using (fraction_natCeil_target_bounds
      (alpha_rpow_rho_pos hn) (alpha_rpow_rho_lt_one hn) hu).2
  have herr : (1 - (alpha n) ^ (rho n)) / ((u n : ℝ) * (alpha n) ^ (rho n)) ≤
      1 / (n : ℝ) := by
    have h := one_div_le_one_div_of_le hn' (n_le_b0 hn)
    simpa [b0, one_div_div] using h
  exact hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr herr)
    (alpha_rpow_rho_pos hn).le)

theorem one_sub_rho_le_two_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 2 / Real.sqrt (n : ℝ) := by
  have hm : (0 : ℝ) < m n := by exact_mod_cast m_pos hn
  have hs := sqrt_ge_two hn
  have hsn := s_le_sqrt n
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hnm : (n : ℝ) ≤ 2 * (m n : ℝ) := by exact_mod_cast n_le_two_mul_m n
  rw [one_sub_rho hn]
  apply (div_le_div_iff₀ hm (by linarith)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsn (Real.sqrt_nonneg (n : ℝ))]

theorem one_sub_rho_le_four_div_sqrt {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n ≤ 4 / Real.sqrt (n : ℝ) := by
  exact (one_sub_rho_le_two_div_sqrt hn).trans
    (div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _))

theorem eventually_q_beta_le_two_div_sqrt :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      q n ≤ 2 / Real.sqrt (n : ℝ) ∧ beta n ≤ 2 / Real.sqrt (n : ℝ) := by
  obtain ⟨n₀, h⟩ := PowerPerturbation.eventually_q_beta_bounds
  refine ⟨max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  exact h n ((le_max_left _ _).trans hn) (alpha n) (rho n) (beta n)
    (alpha_pos hn4) (alpha_le_rpow_mul_exp hn4)
    (rho_pos hn4).le (rho_lt_one hn4).le
    (one_sub_rho_le_four_div_sqrt hn4) (beta_le_rpow_mul_exp hn4)

theorem eventually_admissible : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Admissible n := by
  obtain ⟨n₁, h₁⟩ := eventually_q_beta_le_two_div_sqrt
  obtain ⟨n₂, h₂⟩ := PowerPerturbation.eventually_inverse_sqrt_bounds
  refine ⟨max (max n₁ n₂) 16, fun n hn => ?_⟩
  have hn16 : 16 ≤ n := (le_max_right _ _).trans hn
  have hn4 : 4 ≤ n := by omega
  have hn1 : n₁ ≤ n := (le_max_left n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right n₁ n₂).trans ((le_max_left _ _).trans hn)
  exact ⟨hn16, sqrt_half_le_s hn16, s_le_sqrt n, lambda_ge_three_eighths hn16,
    rho_pos hn4, rho_lt_one hn4, k_le_a hn4, four_mul_n_le_a hn16,
    four_mul_n_le_b hn16, alpha_pos hn4, alpha_lt_one hn4, inv_sqrt_le_alpha hn4,
    inv_alpha_le_sqrt hn4, alpha_rpow_rho_le_beta hn4, (h₁ n hn1).2,
    inv_sqrt_le_q hn4, (h₁ n hn1).1, (h₂ n hn2).1, (h₂ n hn2).2⟩

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualWeightParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

/-- All hypotheses of the circuit weight estimate hold simultaneously for
the actual integer and analytic parameters beyond one uniform threshold. -/
theorem exists_weightParameters_cutoff :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → WeightParameters n (s n : ℝ) (q n) := by
  obtain ⟨n₁, h₁⟩ := eventually_admissible
  obtain ⟨n₂, h₂⟩ := eventually_odd_degree_smallness
  refine ⟨max (max n₁ n₂) 64, ?_⟩
  intro n hn
  have hn64 : 64 ≤ n := (le_max_right _ _).trans hn
  have hn4 : 4 ≤ n := by omega
  have hn1 : n₁ ≤ n := (le_max_left n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hA := h₁ n hn1
  have hq := q_pos hn4
  have henv := hA.q_upper.trans hA.sqrt_upper_power
  refine ⟨hn64, ?_, hA.s_lower, hA.s_upper, hq,
    hA.q_upper.trans hA.sqrt_upper_half, hA.q_upper, henv, ?_⟩
  · exact_mod_cast s_pos hn4
  · exact h₂ n hn2 (q n) hq.le henv

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {K : Type*} [CommSemiring K]

/-- A product of matrices whose entries are linear is homogeneous in its length. -/
theorem matrix_list_prod_isHomogeneous {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix ι ι (MvPolynomial σ K)))
    (hL : ∀ A ∈ L, ∀ i j, (A i j).IsHomogeneous 1) (i j : ι) :
    (L.prod i j).IsHomogeneous L.length := by
  induction L generalizing i j with
  | nil =>
      simp only [List.prod_nil, List.length_nil, Matrix.one_apply]
      split_ifs
      · exact MvPolynomial.isHomogeneous_one σ K
      · exact MvPolynomial.isHomogeneous_zero σ K 0
  | cons A L ih =>
      simp only [List.prod_cons, List.length_cons, Matrix.mul_apply]
      apply MvPolynomial.IsHomogeneous.sum
      intro k hk
      simpa only [Nat.add_comm] using
        (hL A (List.mem_cons_self) i k).mul
          (ih (fun B hB => hL B (List.mem_cons_of_mem A hB)) k j)

/-- The iterated matrix multiplication polynomial has its expected degree. -/
theorem imm_isHomogeneous (K : Type*) [CommSemiring K] (n : ℕ) :
    (imm K n).IsHomogeneous n := by
  classical
  unfold imm
  split_ifs with hn
  · simpa only [List.length_ofFn] using
      matrix_list_prod_isHomogeneous (List.ofFn (fun t : Fin n => immLayer K n t))
        (by
          intro A hA i j
          obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hA
          exact MvPolynomial.isHomogeneous_X K (t, i, j))
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- Matrix multiplication adds weighted degrees, including repeated layer occurrences. -/
theorem matrix_list_map_prod_isWeightedHomogeneous {σ ι τ M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (w : σ → M) (A : τ → Matrix ι ι (MvPolynomial σ K)) (d : τ → M)
    (L : List τ) (hA : ∀ t ∈ L, ∀ i j, (A t i j).IsWeightedHomogeneous w (d t))
    (i j : ι) :
    ((L.map A).prod i j).IsWeightedHomogeneous w (L.map d).sum := by
  induction L generalizing i j with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Matrix.one_apply]
      split_ifs
      · exact MvPolynomial.isWeightedHomogeneous_one K w
      · exact MvPolynomial.isWeightedHomogeneous_zero K w 0
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Matrix.mul_apply]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro k hk
      exact (hA t List.mem_cons_self i k).mul
        (ih (fun s hs => hA s (List.mem_cons_of_mem t hs)) k j)

/-- Every monomial of IMM uses each matrix layer once, expressed with arbitrary additive weights. -/
theorem imm_isWeightedHomogeneous (K : Type*) [CommSemiring K] (n : ℕ)
    {M : Type*} [AddCommMonoid M] (w : Fin n → M) :
    (imm K n).IsWeightedHomogeneous (fun x => w x.1) (∑ t, w t) := by
  classical
  unfold imm
  split_ifs with hn
  · simpa only [← List.ofFn_eq_map, List.sum_ofFn] using
      matrix_list_map_prod_isWeightedHomogeneous
        (fun x : Fin n × Fin n × Fin n => w x.1) (immLayer K n) w (List.finRange n)
        (fun t ht i j => MvPolynomial.isWeightedHomogeneous_X K _ (t, i, j))
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

@[simp] theorem immIdentityEvaluation_imm (n : ℕ) (hn : 0 < n) :
    immIdentityEvaluation K n (imm K n) = 1 := by
  classical
  unfold imm
  simp only [dite_eq_left hn]
  have h : (immIdentityEvaluation K n).mapMatrix
      (List.ofFn (fun t : Fin n => immLayer K n t)).prod = 1 := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, immIdentityEvaluation_layer]
    simp
  exact congrArg (fun A : Matrix (Fin n) (Fin n) K =>
    A ⟨0, hn⟩ ⟨0, hn⟩) h

/-- IMM does not vanish over any nontrivial coefficient semiring when its size is positive. -/
theorem imm_ne_zero (K : Type*) [CommSemiring K] [Nontrivial K] (n : ℕ) (hn : 0 < n) :
    imm K n ≠ 0 := by
  intro h
  have he := immIdentityEvaluation_imm (K := K) n hn
  rw [h, map_zero] at he
  exact zero_ne_one he

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CircuitOutputDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

/-- A nonzero IMM output forces the assigned syntactic output degree to be the layer count. -/
theorem outputDegree_eq_of_circuitValue_eq_imm {K : Type*} [CommSemiring K]
    [Nontrivial K] {n : ℕ} (hn : 0 < n) (c : Depth5Circuit K n)
    (hc : circuitValue c = imm K n) : c.outputDegree = n := by
  have hh := circuitValue_isHomogeneous c
  rw [hc] at hh
  exact hh.inj_right (imm_isHomogeneous K n) (imm_ne_zero K n hn)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

lemma balancedLayer_card_true {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = true)).card = k n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = true)).card =
    (balancedWord n).count true at h
  simpa [balancedWord] using h

lemma balancedLayer_card_false {n : ℕ} (hn : 4 ≤ n) :
    (Finset.univ.filter (fun i => balancedLayer hn i = false)).card = m n := by
  let vec : List.Vector Bool n := ⟨balancedWord n, balancedWord_length hn⟩
  have h := Fin.card_filter_univ_eq_vector_get_eq_count false vec
  change (Finset.univ.filter (fun i => balancedLayer hn i = false)).card =
    (balancedWord n).count false at h
  simpa [balancedWord, BalancedSchedule.word_count_false (k_pos hn), m_eq_k_add_s] using h

lemma balancedVariable_card_true {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = true} = v n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) true)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_true]
  simp [v, pow_two]

lemma balancedVariable_card_false {n : ℕ} (hn : 4 ≤ n) :
    Fintype.card {x : Fin n × Fin n × Fin n // balancedLayer hn x.1 = false} = u n := by
  classical
  rw [Fintype.card_congr (layerVariableEquiv (balancedLayer hn) false)]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype]
  rw [balancedLayer_card_false]
  simp [u, pow_two]

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ConfiguredRankData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common, concrete data for the two sides of the IMM rank comparison. -/

noncomputable section

namespace Problem335.LowerParameters

theorem rankData_eq {n : ℕ} (hn : 4 ≤ n)
    (p : MvPolynomial (Fin n × Fin n × Fin n) ℂ) :
    rankData n p =
      (bidegreeRank (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1)
        (a n) (b n) (k n) (m n) p : ℝ) := by
  simp [rankData, hn]

theorem rankDimension_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rankDimension n := by
  have hv : 0 < homogeneousDim (v n) (a n) :=
    homogeneousDim_pos (v_pos hn) (a n)
  have hu : 0 < homogeneousDim (u n) (b n) :=
    homogeneousDim_pos (u_pos hn) (b n)
  unfold rankDimension
  positivity

theorem rankMomentScale_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rankMomentScale n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  unfold rankMomentScale
  positivity

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualCircuitRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The circuit rank bound for the actual rounded parameters. -/
noncomputable section

namespace Problem335.LowerParameters

/-- The full quantitative circuit estimate with actual source degrees and
dimension. The weight-parameter premise is discharged uniformly eventually. -/
theorem actual_circuit_rank_bound_of_weightParameters
    {K : Type*} [Field K] {n : ℕ} (c : Depth5Circuit K n)
    (side : (Fin n × Fin n × Fin n) → Bool)
    (hvcard : Fintype.card {x // side x = true} = v n)
    (hucard : Fintype.card {x // side x = false} = u n)
    (hp : WeightParameters n (s n) (q n))
    (hc : circuitValue c = imm K n) :
    (bidegreeRank side (a n) (b n) (k n) (m n) (circuitValue c) : ℝ) ≤
      2 * (circuitSize c : ℝ) ^ 2 * sourceDimension n *
        Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
          (n : ℝ) ^ (-Real.sqrt n / 100) := by
  have hn4 : 4 ≤ n := by have := hp.large; omega
  have hnpos : 0 < n := by omega
  let R := fun p : MvPolynomial (Fin n × Fin n × Fin n) K =>
    (bidegreeRank side (a n) (b n) (k n) (m n) p : ℝ)
  have hprod : HomogeneousProductRankBound R n (q n) (lambda n)
      (sourceDimension n) := by
    exact actual_homogeneousProductRankBound hn4 side hvcard hucard
  have hzero : R 0 = 0 := by simp [R]
  have hadd : ∀ p r, R (p + r) ≤ R p + R r := by
    intro p r
    dsimp [R]
    exact_mod_cast bidegreeRank_add_le side (a n) (b n) (k n) (m n) p r
  have hscale : ∀ z p, R (MvPolynomial.C z * p) ≤ R p := by
    intro z p
    dsimp [R, bidegreeRank]
    rw [MvPolynomial.C_mul']
    exact_mod_cast RankMeasure.measure_smul_le
      (bidegreeOperatorFamily side (a n) (b n) (k n) (m n)) z p
  exact circuit_rank_bound_from_product_rank c R hzero hadd hscale
    (s n) (q n) (sourceDimension n) hp (sourceDimension_pos hn4).le
    (outputDegree_eq_of_circuitValue_eq_imm hnpos c hc)
    (by simpa only [lambda_eq_half_sub hnpos] using hprod)

/-- The actual, fixed rank measure satisfies the circuit upper bound after
one absolute threshold. No numerical, product-rank, or partition hypotheses
remain. This is the upper estimate used in the final rank sandwich. -/
theorem exists_rankData_circuit_upper_cutoff :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      rankData n (circuitValue c) ≤
        2 * (circuitSize c : ℝ) ^ 2 * rankDimension n *
          Real.exp ((24 + 4 * Real.log 5) * Real.sqrt n) *
            (n : ℝ) ^ (-Real.sqrt n / 100) := by
  obtain ⟨n₀, hn₀⟩ := exists_weightParameters_cutoff
  refine ⟨n₀, fun n hn c hc => ?_⟩
  have hp := hn₀ n hn
  have hn4 : 4 ≤ n := by have := hp.large; omega
  rw [rankData_eq hn4]
  exact actual_circuit_rank_bound_of_weightParameters c
    (fun x : Fin n × Fin n × Fin n => balancedLayer hn4 x.1)
    (balancedVariable_card_true hn4) (balancedVariable_card_false hn4) hp hc

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma complexFockBasis_apply (d : σ →₀ ℕ) :
    complexFockBasis d = complexFockMonomial d := by
  simp [complexFockBasis, Module.Basis.isUnitSMul_apply, complexFockMonomial_eq,
    MvPolynomial.smul_monomial]

omit [DecidableEq σ] in
lemma complexFockBasis_repr (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    complexFockBasis.repr p d =
      (Real.sqrt (multiFactorial d : ℝ) : ℂ) * p.coeff d := by
  simp only [complexFockBasis, Module.Basis.repr_isUnitSMul, Units.smul_def,
    IsUnit.unit_spec, Units.val_inv_eq_inv_val, Complex.ofReal_inv, inv_inv]
  rfl

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace Problem335

/-- Cauchy--Schwarz with only the nonzero summands counted. -/
theorem sq_sum_le_support_card_mul_sum_sq {ι : Type*} [Fintype ι]
    (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card {i // f i ≠ 0} : ℝ) * ∑ i, f i ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i => f i ≠ 0)
  have hsum : ∑ i ∈ s, f i = ∑ i, f i := by
    exact Finset.sum_filter_ne_zero _
  have hsq : ∑ i ∈ s, f i ^ 2 = ∑ i, f i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi his
    have hf : f i = 0 := by simpa [s] using his
    simp [hf]
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  simpa only [hsum, hsq, Fintype.card_subtype] using h

/-- The second spectral moment of a Hermitian matrix. -/
theorem hermitian_trace_sq_eq_sum_eigenvalues_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  simp [Matrix.diagonal_pow, Function.comp_def]

/-- The trace-rank bound used in the moment method. Positivity is not needed
for this squared formulation: Hermitian symmetry suffices. -/
theorem hermitian_trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    A.trace.re ^ 2 ≤ (A.rank : ℝ) * (A ^ 2).trace.re := by
  rw [hA.trace_eq_sum_eigenvalues, hermitian_trace_sq_eq_sum_eigenvalues_sq hA,
    hA.rank_eq_card_non_zero_eigs]
  simpa [← Complex.ofReal_pow] using
    sq_sum_le_support_card_mul_sum_sq hA.eigenvalues

/-- A nonzero Hermitian matrix has strictly positive second moment. -/
theorem hermitian_trace_sq_pos {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hne : A ≠ 0) :
    0 < (A ^ 2).trace.re := by
  have he : hA.eigenvalues ≠ 0 := by
    intro hz
    exact hne (hA.eigenvalues_eq_zero_iff.mp hz)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp he
  rw [hermitian_trace_sq_eq_sum_eigenvalues_sq hA]
  simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- The ratio form of the trace-rank bound. -/
theorem hermitian_rank_ge_trace_ratio {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsecond : 0 < (A ^ 2).trace.re) :
    A.trace.re ^ 2 / (A ^ 2).trace.re ≤ (A.rank : ℝ) := by
  apply (div_le_iff₀ hsecond).2
  exact hermitian_trace_sq_le_rank_mul_trace_sq hA

/-- Applied to the Gram matrix, the moment method bounds the rank of the
original rectangular matrix. -/
theorem gram_rank_ge_trace_ratio {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℂ)
    (hsecond : 0 < ((A.conjTranspose * A) ^ 2).trace.re) :
    (A.conjTranspose * A).trace.re ^ 2 / ((A.conjTranspose * A) ^ 2).trace.re ≤ (A.rank : ℝ) := by
  have h := hermitian_rank_ge_trace_ratio (Matrix.isHermitian_conjTranspose_mul_self A) hsecond
  simpa only [Matrix.rank_conjTranspose_mul_self] using h

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace Problem335

section MomentComparison

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Comparing the first two normalized trace moments gives the rank bound used
in the IMM argument. Here `w` contains the path count and local moment factor. -/
theorem rank_lower_bound_of_trace_moment_bounds (A : Matrix κ ι ℂ)
    {D w δ ε : ℝ} (hD : 0 < D) (hw : 0 < w)
    (hfirst : D * w * Real.exp (-δ) ≤ (Aᴴ * A).trace.re)
    (hsecond : (((Aᴴ * A) ^ 2).trace.re) ≤ D * w ^ 2 * Real.exp ε) :
    D * Real.exp (-(2 * δ + ε)) ≤ (A.rank : ℝ) := by
  let T := (Aᴴ * A).trace.re
  let T₂ := (((Aᴴ * A) ^ 2).trace.re)
  let L := D * w * Real.exp (-δ)
  let U := D * w ^ 2 * Real.exp ε
  have hL : 0 < L := by dsimp [L]; positivity
  have hT : 0 < T := lt_of_lt_of_le hL hfirst
  have hHne : Aᴴ * A ≠ 0 := by
    intro hz
    simp [T, hz] at hT
  have hT₂ : 0 < T₂ :=
    hermitian_trace_sq_pos (Matrix.isHermitian_conjTranspose_mul_self A) hHne
  have hU : 0 < U := lt_of_lt_of_le hT₂ hsecond
  have hsq : L ^ 2 ≤ T ^ 2 := by nlinarith [hfirst]
  have hratio : L ^ 2 / U ≤ (A.rank : ℝ) := calc
    L ^ 2 / U ≤ T ^ 2 / U := div_le_div_of_nonneg_right hsq hU.le
    _ ≤ T ^ 2 / T₂ := div_le_div_of_nonneg_left (sq_nonneg T) hT₂ hsecond
    _ ≤ (A.rank : ℝ) := gram_rank_ge_trace_ratio A hT₂
  have hexp : Real.exp (-(2 * δ + ε)) * Real.exp ε = Real.exp (-δ) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heq : D * Real.exp (-(2 * δ + ε)) = L ^ 2 / U := by
    apply (eq_div_iff (ne_of_gt hU)).2
    dsimp [L, U]
    calc
      D * Real.exp (-(2 * δ + ε)) * (D * w ^ 2 * Real.exp ε) =
          D ^ 2 * w ^ 2 * (Real.exp (-(2 * δ + ε)) * Real.exp ε) := by ring
      _ = D ^ 2 * w ^ 2 * Real.exp (-δ) ^ 2 := by rw [hexp]
      _ = (D * w * Real.exp (-δ)) ^ 2 := by ring
  rw [heq]
  exact hratio

end MomentComparison

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FockPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
lemma occupationAmplitude_nonneg (isV : σ → Bool) (d : σ →₀ ℕ) (i : σ) :
    0 ≤ occupationAmplitude isV d i := Real.sqrt_nonneg _

omit [Fintype σ] [DecidableEq σ] in
/-- Squaring the normalized path amplitude gives exactly the occupation
polynomial, with no factorials or square roots left. -/
theorem pathAmplitude_sq (isV : σ → Bool) (l : List σ) (d : σ →₀ ℕ) :
    ((l.map (occupationAmplitude isV d)).prod) ^ 2 =
      (l.map (fun i => if isV i then (d i : ℝ) else (d i : ℝ) + 1)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_pow, ih]
    congr 1
    apply Real.sq_sqrt
    cases isV i <;> positivity

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmBidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- With a layerwise partition, IMM is already in the selected bidegree. -/
theorem imm_mem_bidegreeSubmodule (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    imm K n ∈ bidegreeSubmodule (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card := by
  classical
  have h := imm_isWeightedHomogeneous K n (bidegreeWeight side)
  have hs : (∑ t, bidegreeWeight side t) =
      ((Finset.univ.filter (fun t => side t = true)).card,
       (Finset.univ.filter (fun t => side t = false)).card) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
    · simp only [Prod.snd_sum, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t ht
      cases hs : side t <;> simp [bidegreeWeight, hs]
  rw [hs] at h
  exact h

/-- A bidegree projection does not change IMM when the selected index is its layer count. -/
theorem bidegreeComponent_imm (K : Type*) [CommSemiring K] (n : ℕ)
    (side : Fin n → Bool) :
    bidegreeComponent (fun x => side x.1)
      (Finset.univ.filter (fun t => side t = true)).card
      (Finset.univ.filter (fun t => side t = false)).card (imm K n) = imm K n :=
  bidegreeComponent_eq_self (imm_mem_bidegreeSubmodule K n side)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ ι R : Type*}

theorem list_sum_map_flatMap [AddMonoid R] {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → R) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Matrix multiplication is the sum of the products along its labelled paths. -/
theorem matrixEntryPaths_sum_prod [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : σ → Matrix ι ι R) (labels : List σ) (i j : ι) :
    ((matrixEntryPaths labels i j).map
      (fun p => (p.map (fun e => A e.1 e.2.1 e.2.2)).prod)).sum =
      ((labels.map A).prod) i j := by
  induction labels generalizing i with
  | nil => by_cases hij : i = j <;> simp [matrixEntryPaths, hij]
  | cons t ts ih =>
      cases ts with
      | nil => simp [matrixEntryPaths]
      | cons u us =>
          rw [matrixEntryPaths, list_sum_map_flatMap]
          simp only [List.map_map, Function.comp_def, List.map_cons, List.prod_cons]
          simp_rw [List.sum_map_mul_left, ih]
          simp [Finset.sum_map_toList, Matrix.mul_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmOperatorPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open MvPolynomial

/-- The number of endpoint paths is `n^(n-1)`. -/
theorem immPaths_length (n : ℕ) (hn : 0 < n) :
    (immPaths n hn).length = n ^ (n - 1) := by
  unfold immPaths
  rw [matrixEntryPaths_length _ (by simpa using (Nat.ne_of_gt hn))]
  simp

variable {K : Type*} [CommSemiring K]

/-- The endpoint IMM polynomial is the sum of its labelled path monomials. -/
theorem imm_eq_sum_path_products (n : ℕ) (hn : 0 < n) :
    imm K n = ((immPaths n hn).map fun p => (p.map (X (R := K))).prod).sum := by
  have h := matrixEntryPaths_sum_prod (immLayer K n) (List.finRange n)
    (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  simp only [imm, dite_eq_left hn, List.ofFn_eq_map]
  exact h.symm

/-- The full IMM polynomial operator is a sum of products of its edge operators. -/
theorem mixedOperator_imm_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ((immPaths n hn).map fun p =>
        (p.map (variableOperator (K := K) isV)).prod).sum := by
  rw [imm_eq_sum_path_products n hn, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_list_prod, mixedOperator_X]

/-- The operator expansion indexed by the finite type of paths. -/
theorem mixedOperator_imm_eq_sum_paths_fin (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool) :
    mixedOperator (K := K) isV (imm K n) =
      ∑ p : Fin (immPaths n hn).length,
        (((immPaths n hn).get p).map (variableOperator (K := K) isV)).prod := by
  rw [mixedOperator_imm_eq_sum_paths n hn isV]
  symm
  simpa only [List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem (immPaths n hn)
      (fun p => (p.map (variableOperator (K := K) isV)).prod))

/-- Applying the IMM operator is the sum of its individual path actions. -/
theorem mixedOperator_imm_apply_eq_sum_paths (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (f : MvPolynomial (Fin n × Fin n × Fin n) K) :
    mixedOperator isV (imm K n) f =
      ∑ p : Fin (immPaths n hn).length,
        ((((immPaths n hn).get p).map (variableOperator isV)).prod) f := by
  rw [mixedOperator_imm_eq_sum_paths_fin n hn isV, LinearMap.sum_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFockMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

theorem immPathAmplitude_nonneg (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) (p : Fin (immPaths n hn).length) :
    0 ≤ immPathAmplitude n hn isV d p := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact occupationAmplitude_nonneg isV d i

/-- The actual IMM operator on a normalized monomial is the sum of its sparse path actions. -/
theorem mixedOperator_imm_complexFockMonomial (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d : (Fin n × Fin n × Fin n) →₀ ℕ) :
    mixedOperator isV (imm ℂ n) (complexFockMonomial d) =
      ∑ p : Fin (immPaths n hn).length,
        (immPathAmplitude n hn isV d p : ℂ) •
          complexFockMonomial (immPathOccupation n hn isV d p) := by
  rw [mixedOperator_imm_apply_eq_sum_paths n hn isV]
  apply Finset.sum_congr rfl
  intro p hp
  have h := mixedOperator_path_complexFockMonomial isV ((immPaths n hn).get p)
    (immPaths_nodup n hn _ (List.get_mem _ p)) d
  simpa only [map_list_prod, List.map_map, Function.comp_def, mixedOperator_X,
    immPathAmplitude, immPathOccupation] using h

/-- Normalized matrix entries of the actual IMM operator are weighted path-shift counts. -/
theorem complexFockBasis_repr_mixedOperator_imm (n : ℕ) (hn : 0 < n)
    (isV : (Fin n × Fin n × Fin n) → Bool)
    (d e : (Fin n × Fin n × Fin n) →₀ ℕ) :
    complexFockBasis.repr (mixedOperator isV (imm ℂ n) (complexFockMonomial d)) e =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn isV d p = e then (immPathAmplitude n hn isV d p : ℂ)
        else 0 := by
  classical
  rw [mixedOperator_imm_complexFockMonomial n hn isV]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← complexFockBasis_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite matrix expansions for the two trace moments in the IMM argument.
These identities contain no analytic or asymptotic assumptions. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P R : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- Expanding a real Gram matrix gives the sum of squared entries. -/
theorem trace_transpose_mul_self {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    Matrix.trace (A.transpose * A) = ∑ i, ∑ j, (A j i) ^ 2 := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFiniteMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Each finite normalized matrix entry is exactly the weighted sum of its IMM path shifts. -/
theorem immNormalizedMatrix_apply (n : ℕ) (hn : 0 < n) (side : Fin n → Bool)
    (a b : ℕ) (e : ImmTargetIndex n side a b) (d : ImmSourceIndex n side a b) :
    immNormalizedMatrix n side a b e d =
      ∑ p : Fin (immPaths n hn).length,
        if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
        then (immPathAmplitude n hn (fun x => side x.1) d.1 p : ℂ) else 0 := by
  classical
  unfold immNormalizedMatrix
  rw [LinearMap.toMatrix_apply, bidegreeComplexFockBasis_repr]
  change (Real.sqrt (multiFactorial e.1 : ℝ) : ℂ) *
    (mixedOperator (fun x => side x.1)
        (bidegreeComponent (fun x => side x.1) (immLayerVCount side) (immLayerUCount side)
          (imm ℂ n))
        ((bidegreeComplexFockBasis (σ := Fin n × Fin n × Fin n)
          (fun x => side x.1) a b d) : MvPolynomial (Fin n × Fin n × Fin n) ℂ)).coeff e.1 = _
  rw [bidegreeComplexFockBasis_apply]
  simp only [immLayerVCount, immLayerUCount, bidegreeComponent_imm]
  rw [← complexFockBasis_repr]
  exact complexFockBasis_repr_mixedOperator_imm n hn (fun x => side x.1) d.1 e.1

/-- The finite normalized matrix computes exactly the manuscript's rank measure. -/
theorem immNormalizedMatrix_rank (n : ℕ) (side : Fin n → Bool) (a b : ℕ) :
    (immNormalizedMatrix n side a b).rank =
      bidegreeRank (fun x => side x.1) a b
        (immLayerVCount side) (immLayerUCount side) (imm ℂ n) := by
  rw [immNormalizedMatrix, ← RankMeasure.mapRank_eq_matrixRank, finiteMixedOperator_rank]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.TraceComplexification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real nonnegative path matrix can be read over the complex numbers
without changing either of its two trace moments. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- Real entrywise complexification sends the real Gram matrix to the complex Gram matrix. -/
theorem complexify_gram {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    (A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal =
      (A.transpose * A).map Complex.ofReal := by
  ext i k
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]

/-- Entrywise complexification preserves the real part of the trace. -/
theorem trace_complexify_re {I : Type u_1} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) :
    (A.map Complex.ofReal).trace.re = A.trace := by
  simp [Matrix.trace, Matrix.map_apply]

/-- First moment agrees over the real and complex coefficient fields. -/
theorem complexify_first_trace (A : Matrix J I ℝ) :
    ((A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal).trace.re =
      (A.transpose * A).trace := by
  rw [complexify_gram, trace_complexify_re]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFirstTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

theorem immNormalizedMatrix_eq_map_real (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) :
    immNormalizedMatrix n side a b =
      (immRealNormalizedMatrix n hn side a b).map Complex.ofReal := by
  classical
  ext e d
  rw [immNormalizedMatrix_apply n hn]
  simp only [Matrix.map_apply, immRealNormalizedMatrix, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- Every nonzero path amplitude occurs in exactly one genuine target row.
Zero-amplitude paths need no artificial target-row choice. -/
theorem immPathAmplitude_sq_sum_target (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length) :
    (∑ e : ImmTargetIndex n side a b,
      (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
       then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2) =
      immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := by
  classical
  by_cases hw : immPathAmplitude n hn (fun x => side x.1) d.1 p = 0
  · simp [hw]
  let e : ImmTargetIndex n side a b :=
    ⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
      immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p hw⟩
  rw [Finset.sum_eq_single e]
  · simp [e]
  · intro e' he' hne
    have hocc : immPathOccupation n hn (fun x => side x.1) d.1 p ≠ e'.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq.symm
    simp [hocc]
  · simp

/-- Actual normalized IMM first trace dominates the total occupation mass.
Nonnegative coefficients make path-collision analysis unnecessary for this
lower bound. All sources and targets are the genuine finite bidegree spaces. -/
theorem immNormalizedMatrix_first_trace_lower (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) :
    (∑ d : ImmSourceIndex n side a b, ∑ p : Fin (immPaths n hn).length,
      immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2) ≤
      ((immNormalizedMatrix n side a b).conjTranspose *
        immNormalizedMatrix n side a b).trace.re := by
  classical
  rw [immNormalizedMatrix_eq_map_real n hn, complexify_first_trace,
    trace_transpose_mul_self]
  apply Finset.sum_le_sum
  intro d hd
  calc
    _ = ∑ p : Fin (immPaths n hn).length, ∑ e : ImmTargetIndex n side a b,
        (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
         then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (immPathAmplitude_sq_sum_target n hn side a b d p).symm
    _ = ∑ e : ImmTargetIndex n side a b, ∑ p : Fin (immPaths n hn).length,
        (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
         then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2 :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_sq_le_sq_sum_of_nonneg
      intro p hp
      split_ifs
      · exact immPathAmplitude_nonneg n hn _ d.1 p
      · exact le_rfl

/-- Uniform actual-source occupation averages lift to the normalized IMM
first trace with exactly `n^(n-1)` endpoint paths. -/
theorem immNormalizedMatrix_first_trace_lower_of_average
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) (L : ℝ)
    (hmean : ∀ p : Fin (immPaths n hn).length,
      L ≤ (∑ d : ImmSourceIndex n side a b,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2) /
          (Fintype.card (ImmSourceIndex n side a b) : ℝ)) :
    (Fintype.card (ImmSourceIndex n side a b) : ℝ) * (n : ℝ) ^ (n - 1) * L ≤
      ((immNormalizedMatrix n side a b).conjTranspose *
        immNormalizedMatrix n side a b).trace.re := by
  classical
  have hsum (p : Fin (immPaths n hn).length) :
      (Fintype.card (ImmSourceIndex n side a b) : ℝ) * L ≤
        ∑ d : ImmSourceIndex n side a b,
          immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := by
    by_cases hz : Fintype.card (ImmSourceIndex n side a b) = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg (fun d _ => sq_nonneg _)
    · have hpos : (0 : ℝ) < Fintype.card (ImmSourceIndex n side a b) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      simpa only [mul_comm] using (le_div_iff₀ hpos).mp (hmean p)
  calc
    _ = ∑ p : Fin (immPaths n hn).length,
        (Fintype.card (ImmSourceIndex n side a b) : ℝ) * L := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        immPaths_length, nsmul_eq_mul, Nat.cast_pow]
      ring
    _ ≤ ∑ p : Fin (immPaths n hn).length, ∑ d : ImmSourceIndex n side a b,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 :=
      Finset.sum_le_sum (fun p _ => hsum p)
    _ = ∑ d : ImmSourceIndex n side a b, ∑ p : Fin (immPaths n hn).length,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := Finset.sum_comm
    _ ≤ _ := immNormalizedMatrix_first_trace_lower n hn side a b

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.AlphaParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

theorem sqrt_ge_four {n : ℕ} (hn : 16 ≤ n) : 4 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

theorem a_ideal_le {n : ℕ} (_hn : 16 ≤ n) :
    (v n : ℝ) / (Real.sqrt (n : ℝ) - 1) ≤ (a n : ℝ) := Nat.le_ceil _

theorem a_scale_lower {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 4 ≤ (a n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hden : 0 < Real.sqrt (n : ℝ) - 1 := by linarith
  have hv : 3 * (n : ℝ) ^ 3 ≤ 8 * (v n : ℝ) := by
    exact_mod_cast three_mul_cube_le_eight_mul_v hn
  have heq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) ^ 3 := by
    calc
      _ = (n : ℝ) ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = (n : ℝ) ^ 3 := by rw [Real.sq_sqrt (by positivity)]; ring
  apply le_trans _ (a_ideal_le hn)
  apply (le_div_iff₀ hden).mpr
  have hnonneg : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by positivity
  nlinarith

/-- The occupation-moment error from differentiation is of order `n^(-1/2)`. -/
theorem sq_div_a_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (a n : ℝ) ≤ 4 / Real.sqrt (n : ℝ) := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hs : 0 < Real.sqrt (n : ℝ) := by have := sqrt_ge_four hn; linarith
  apply (div_le_div_iff₀ ha hs).mpr
  have h := a_scale_lower hn
  linarith

/-- The ambient-variable occupation error has the better order `1/n`. -/
theorem sq_div_v_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (v n : ℝ) ≤ 8 / (3 * (n : ℝ)) := by
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_div_iff₀ hv (by positivity)).mpr
  have h : 3 * (n : ℝ) ^ 3 ≤ 8 * (v n : ℝ) := by
    exact_mod_cast three_mul_cube_le_eight_mul_v hn
  nlinarith

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem335.LowerParameters

theorem sq_div_b_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (b n : ℝ) ≤ 4 / Real.sqrt (n : ℝ) := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hab : (a n : ℝ) ≤ b n := by exact_mod_cast a_le_b (by omega : 4 ≤ n)
  exact (div_le_div_of_nonneg_left (sq_nonneg _) ha hab).trans (sq_div_a_le hn)

theorem sq_div_u_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (u n : ℝ) ≤ 2 / (n : ℝ) := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos (by omega : 4 ≤ n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_div_iff₀ hu hnR).mpr
  have h : (n : ℝ) ^ 3 ≤ 2 * (u n : ℝ) := by exact_mod_cast cube_le_two_mul_u n
  nlinarith

/-- A concrete bound for the combined occupation-comparison error in both groups. -/
theorem occupation_parameter_loss_le {n : ℕ} (hn : 16 ≤ n) :
    (n : ℝ) ^ 2 / (a n : ℝ) + (n : ℝ) ^ 2 / (v n : ℝ) +
      (n : ℝ) ^ 2 / (b n : ℝ) + (n : ℝ) ^ 2 / (u n : ℝ) ≤
      16 / Real.sqrt (n : ℝ) := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hvbound : 8 / (3 * (n : ℝ)) ≤ 3 / Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hspos).mpr
    linarith
  have hubound : 2 / (n : ℝ) ≤ 2 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hspos hroot
  have ha := sq_div_a_le hn
  have hv := (sq_div_v_le hn).trans hvbound
  have hb := sq_div_b_le hn
  have hu := (sq_div_u_le hn).trans hubound
  have hpos : 0 < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hspos
  simp only [div_eq_mul_inv] at ha hv hb hu hpos ⊢
  linarith

/-- Both finite occupation laws have uniformly small logarithmic comparison loss. -/
theorem occupation_order_loss_le {n : ℕ} (hn : 16 ≤ n) {H : ℝ}
    (hH : 0 ≤ H) (hHn : H ≤ 2 * (n : ℝ)) :
    H ^ 2 / (a n : ℝ) + H ^ 2 / (2 * (v n : ℝ)) +
      H ^ 2 / (b n : ℝ) + H ^ 2 / (2 * (u n : ℝ)) ≤
      64 / Real.sqrt (n : ℝ) := by
  have hsq : H ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos (by omega : 4 ≤ n)
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos (by omega : 4 ≤ n)
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos (by omega : 4 ≤ n)
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos (by omega : 4 ≤ n)
  have h1 := div_le_div_of_nonneg_right hsq ha.le
  have h2 := div_le_div_of_nonneg_right hsq hv.le
  have h3 := div_le_div_of_nonneg_right hsq hb.le
  have h4 := div_le_div_of_nonneg_right hsq hu.le
  have h2' : H ^ 2 / (2 * (v n : ℝ)) ≤ H ^ 2 / (v n : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hv (by linarith)
  have h4' : H ^ 2 / (2 * (u n : ℝ)) ≤ H ^ 2 / (u n : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hu (by linarith)
  have hloss := occupation_parameter_loss_le hn
  simp only [mul_div_assoc] at h1 h2 h3 h4
  simp only [div_eq_mul_inv] at h1 h2 h3 h4 h2' h4' hloss ⊢
  linarith

/-- Separate derivative and multiplication expansion orders obey the same loss bound. -/
theorem occupation_two_orders_loss_le {n : ℕ} (hn : 16 ≤ n) {H₁ H₂ : ℝ}
    (hH₁ : 0 ≤ H₁) (hH₁n : H₁ ≤ 2 * (n : ℝ))
    (hH₂ : 0 ≤ H₂) (hH₂n : H₂ ≤ 2 * (n : ℝ)) :
    H₁ ^ 2 / (a n : ℝ) + H₁ ^ 2 / (2 * (v n : ℝ)) +
      H₂ ^ 2 / (b n : ℝ) + H₂ ^ 2 / (2 * (u n : ℝ)) ≤
      64 / Real.sqrt (n : ℝ) := by
  calc
    _ ≤ (2 * (n : ℝ)) ^ 2 / (a n : ℝ) +
        (2 * (n : ℝ)) ^ 2 / (2 * (v n : ℝ)) +
        (2 * (n : ℝ)) ^ 2 / (b n : ℝ) +
        (2 * (n : ℝ)) ^ 2 / (2 * (u n : ℝ)) := by
      gcongr
    _ ≤ _ := occupation_order_loss_le hn (by positivity) le_rfl

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ExponentCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinalities of homogeneous and bihomogeneous exponent sets -/

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*}

/-- Each selected matrix layer contributes all `n²` ambient variables. -/
theorem card_layer_variables {n : ℕ} (s : Finset (Fin n)) :
    Fintype.card {x : Fin n × Fin n × Fin n // x.1 ∈ s} = s.card * n ^ 2 := by
  classical
  rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
    (α := Fin n) (β := Fin n × Fin n) (p := fun x => x ∈ s))]
  simp [pow_two]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.BidegreeAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- Summing a separated function over bihomogeneous exponent vectors factors
into the two weak-composition sums. This is the independence of the two
occupation groups, not independence of coordinates within either group. -/
theorem sum_split {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) =
      (∑' v : Composition {x // isV x = true} a, f v.val) *
        (∑' u : Composition {x // ¬ isV x = true} b, g u.val) := by
  classical
  let : Fintype (Composition {x // isV x = true} a) :=
    Fintype.ofEquiv (Sym {x // isV x = true} a)
      (Sym.equivNatSumOfFintype _ _)
  let : Fintype (Composition {x // ¬ isV x = true} b) :=
    Fintype.ofEquiv (Sym {x // ¬ isV x = true} b)
      (Sym.equivNatSumOfFintype _ _)
  calc
    _ = ∑' z : Composition {x // isV x = true} a ×
        Composition {x // ¬ isV x = true} b, f z.1.val * g z.2.val :=
      (bidegreeExponentsEquiv isV a b).tsum_eq (fun z => f z.1.val * g z.2.val)
    _ = _ := by
      simp only [tsum_fintype, Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun v : Composition {x // isV x = true} a => f v.val)
        (fun u : Composition {x // ¬ isV x = true} b => g u.val)).symm

/-- The normalized form of `sum_split`: the uniform domain occupation average
is the product of the two uniform weak-composition averages. Empty index sets
are handled by the usual convention that division by zero is zero. -/
theorem average_split {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Nat.card (Index isV a b) : ℝ) =
      ((∑' v : Composition {x // isV x = true} a, f v.val) /
        (Nat.card (Composition {x // isV x = true} a) : ℝ)) *
      ((∑' u : Composition {x // ¬ isV x = true} b, g u.val) /
        (Nat.card (Composition {x // ¬ isV x = true} b) : ℝ)) := by
  rw [sum_split, Nat.card_congr (bidegreeExponentsEquiv isV a b),
    Nat.card_prod, Nat.cast_mul, div_mul_div_comm]

end Problem335.BidegreeAverages

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The elementary logarithmic lower bound used for factorial moment ratios. -/
theorem log_one_sub_ge_neg_two_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  linarith

/-- A single factor of the occupation ratio has an exponential lower bound. -/
theorem exp_le_occupation_factor {x y : ℝ}
    (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (hy : 0 ≤ y) :
    Real.exp (-2 * x - y) ≤ (1 - x) / (1 + y) := by
  have hxpos : 0 < 1 - x := by linarith
  have hypos : 0 < 1 + y := by linarith
  have hlower := log_one_sub_ge_neg_two_mul hx hxhalf
  have hupper := Real.log_le_sub_one_of_pos hypos
  have hlog : -2 * x - y ≤ Real.log ((1 - x) / (1 + y)) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hypos)]
    linarith
  exact (Real.le_log_iff_exp_le (div_pos hxpos hypos)).mp hlog

private theorem sum_range_cast_le_half_sq (H : ℕ) :
    (∑ j ∈ Finset.range H, (j : ℝ)) ≤ (H : ℝ) ^ 2 / 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

/-- The exponential lower bound for the occupation ratio from the manuscript. -/
theorem exp_le_occupationRatio {t r : ℝ} {H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : (H : ℝ) ≤ t / 2) :
    Real.exp (-(H : ℝ) ^ 2 / t - (H : ℝ) ^ 2 / (2 * r)) ≤
      occupationRatio t r H := by
  have hfactor : ∀ j ∈ Finset.range H,
      Real.exp (-2 * ((j : ℝ) / t) - (j : ℝ) / r) ≤
        (1 - (j : ℝ) / t) / (1 + (j : ℝ) / r) := by
    intro j hj
    apply exp_le_occupation_factor (by positivity) _ (by positivity)
    apply (div_le_iff₀ ht).2
    have hjH : (j : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith
  have hprod := Finset.prod_le_prod
    (fun j (_ : j ∈ Finset.range H) =>
      (Real.exp_pos (-2 * ((j : ℝ) / t) - (j : ℝ) / r)).le) hfactor
  rw [← Real.exp_sum] at hprod
  apply le_trans _ hprod
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div]
  have hsum := sum_range_cast_le_half_sq H
  have hdivt := div_le_div_of_nonneg_right hsum ht.le
  have hdivr := div_le_div_of_nonneg_right hsum hr.le
  ring_nf at hdivt hdivr ⊢
  linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationRatioAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Algebraic removal of the geometric normalization from the occupation ratio. -/
theorem occupationRatio_mul_mean_pow {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (H : ℕ) :
    occupationRatio t r H * (t / r) ^ H =
      (∏ j ∈ Finset.range H, (t - (j : ℝ))) /
        (∏ j ∈ Finset.range H, (r + (j : ℝ))) := by
  have hconst : (t / r) ^ H = ∏ _j ∈ Finset.range H, t / r := by simp [div_pow]
  rw [occupationRatio, hconst, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hsum : r + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hden : 1 + (j : ℝ) / r ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- The exact factorial-moment ratio over weak compositions. -/
theorem descFactorial_div_ascFactorial_eq_ratio {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : H ≤ t) :
    (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) =
      occupationRatio t r H * ((t : ℝ) / r) ^ H := by
  rw [occupationRatio_mul_mean_pow (by exact_mod_cast ht) (by exact_mod_cast hr)]
  congr 1
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_sub (le_trans (Finset.mem_range.mp hj).le hH)
  · rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact Nat.cast_add r j

/-- The lower comparison is uniform over all factorial orders up to half the total. -/
theorem exp_mul_mean_pow_le_descFactorial_div_ascFactorial {t r H : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : 2 * H ≤ t) :
    Real.exp (-(H : ℝ) ^ 2 / t - (H : ℝ) ^ 2 / (2 * r)) *
        ((t : ℝ) / r) ^ H ≤ (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  have hHt : H ≤ t := by omega
  rw [descFactorial_div_ascFactorial_eq_ratio ht hr hHt]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply exp_le_occupationRatio (by exact_mod_cast ht) (by exact_mod_cast hr)
  have hcast : 2 * (H : ℝ) ≤ t := by exact_mod_cast hH
  linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- A common loss bound can be used for all orders bounded by `H₀`. -/
theorem occupation_factorial_ratio_lower_of_le {t r H H₀ : ℕ}
    (ht : 0 < t) (hr : 0 < r) (hH : H ≤ H₀) (hH₀ : 2 * H₀ ≤ t) :
    Real.exp (-(H₀ : ℝ) ^ 2 / t - (H₀ : ℝ) ^ 2 / (2 * r)) *
        ((t : ℝ) / r) ^ H ≤ (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  apply le_trans _ (exp_mul_mean_pow_le_descFactorial_div_ascFactorial ht hr
    (show 2 * H ≤ t by omega))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : (H : ℝ) ^ 2 ≤ (H₀ : ℝ) ^ 2 := by
    have hh : (H : ℝ) ≤ H₀ := by exact_mod_cast hH
    nlinarith [show 0 ≤ (H : ℝ) by positivity]
  have h₁ := div_le_div_of_nonneg_right hsq (show 0 ≤ (t : ℝ) by positivity)
  have h₂ := div_le_div_of_nonneg_right hsq (show 0 ≤ 2 * (r : ℝ) by positivity)
  simp only [neg_div]
  linarith

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.OccupationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

private lemma fallingFactorialSeries_eq (d : ℕ) :
    fallingFactorialSeries d = PowerSeries.C (d.factorial : ℝ) *
      (PowerSeries.X ^ d * (PowerSeries.mk 1 : PowerSeries ℝ) ^ (d + 1)) := by
  ext j
  rw [fallingFactorialSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.mk_one_pow_eq_mk_choose_add]
  by_cases h : d ≤ j
  · rw [ite_eq_left h, PowerSeries.coeff_mk, Nat.add_sub_of_le h,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  · rw [ite_eq_right h, mul_zero, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

private lemma fallingFactorialSeries_prod {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    (∏ i, fallingFactorialSeries (d i)) =
      PowerSeries.C (∏ i, (d i).factorial : ℝ) *
        (PowerSeries.X ^ (∑ i, d i) *
          (PowerSeries.mk 1 : PowerSeries ℝ) ^ ((∑ i, d i) + Fintype.card ι)) := by
  simp only [fallingFactorialSeries_eq, Finset.prod_mul_distrib,
    ← map_prod, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- Exact weighted weak-composition sum, with the impossible-degree case
explicitly zero. This is the coefficient-extraction form of the occupation
factorial moment identity. -/
theorem occupation_factorial_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) =
      (∏ i, (d i).factorial : ℝ) *
        if (∑ i, d i) ≤ t then
          ((t + Fintype.card ι - 1).choose (t - ∑ i, d i) : ℝ) else 0 := by
  classical
  have hr : 0 < Fintype.card ι := Fintype.card_pos
  let H := ∑ i, d i
  have heq : H + Fintype.card ι = (H + Fintype.card ι - 1) + 1 := by omega
  have hcoeff := PowerSeries.coeff_prod (fun i => fallingFactorialSeries (d i)) t Finset.univ
  simp only [fallingFactorialSeries, PowerSeries.coeff_mk] at hcoeff
  rw [← hcoeff]
  change PowerSeries.coeff t (∏ i, fallingFactorialSeries (d i)) = _
  rw [fallingFactorialSeries_prod]
  change PowerSeries.coeff t (PowerSeries.C (∏ i, (d i).factorial : ℝ) *
    (PowerSeries.X ^ H * (PowerSeries.mk 1 : PowerSeries ℝ) ^
      (H + Fintype.card ι))) = _
  rw [heq, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
  by_cases hH : H ≤ t
  · rw [ite_eq_left hH, PowerSeries.coeff_mk, ite_eq_left hH]
    have harr : H + Fintype.card ι - 1 + (t - H) = t + Fintype.card ι - 1 := by
      omega
    rw [harr]
    congr 2
    apply Nat.choose_symm_of_eq_add
    dsimp [H] at *
    omega
  · rw [ite_eq_right hH, ite_eq_right hH]

/-- Stars-and-bars count for the same finite weak-composition index set. -/
theorem occupation_composition_card {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℕ) :
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t + Fintype.card ι - 1).choose t := by
  classical
  have h := occupation_factorial_sum (ι := ι) (fun _ => 0) t
  simp at h
  exact_mod_cast h

lemma occupation_choose_ratio (t r H : ℕ) (hr : 0 < r) (hH : H ≤ t) :
    ((t + r - 1).choose (t - H) : ℝ) / ((t + r - 1).choose t : ℝ) =
      (t.descFactorial H : ℝ) / (r.ascFactorial H : ℝ) := by
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by positivity
  have hdesc : (t.descFactorial H : ℝ) =
      (t.factorial : ℝ) / ((t - H).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_descFactorial hH)
  have hasc : (r.ascFactorial H : ℝ) =
      ((r + H - 1).factorial : ℝ) / ((r - 1).factorial : ℝ) := by
    apply (eq_div_iff (hfac _)).2
    exact_mod_cast (by simpa only [Nat.mul_comm] using
      Nat.factorial_mul_ascFactorial' r H hr)
  rw [Nat.cast_choose ℝ (by omega : t - H ≤ t + r - 1),
    Nat.cast_choose ℝ (by omega : t ≤ t + r - 1), hdesc, hasc]
  rw [show t + r - 1 - (t - H) = r + H - 1 by omega,
    show t + r - 1 - t = r - 1 by omega]
  field_simp

/-- The normalized factorial moment of the uniform distribution on weak
compositions. The result includes total orders above `t`, where both sides
vanish. -/
theorem occupation_factorial_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (d : ι → ℕ) (t : ℕ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t,
      ∏ i, ((M i).descFactorial (d i) : ℝ)) /
        (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card =
      (t.descFactorial (∑ i, d i) : ℝ) /
        ((Fintype.card ι).ascFactorial (∑ i, d i) : ℝ) *
          (∏ i, (d i).factorial : ℝ) := by
  rw [occupation_factorial_sum, occupation_composition_card]
  by_cases hH : (∑ i, d i) ≤ t
  · rw [ite_eq_left hH]
    rw [mul_div_assoc, occupation_choose_ratio t (Fintype.card ι) _
      Fintype.card_pos hH]
    ring
  · rw [ite_eq_right hH, mul_zero, zero_div,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero,
      zero_div, zero_mul]

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.FirstOccupationMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

lemma occupationAverage_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (s : Finset κ) (f : κ → (ι →₀ ℕ) → ℝ) :
    occupationAverage t (fun M => ∑ j ∈ s, f j M) =
      ∑ j ∈ s, occupationAverage t (f j) := by
  unfold occupationAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma occupationAverage_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (f : (ι →₀ ℕ) → ℝ) (hf : ∀ M, 0 ≤ f M) :
    0 ≤ occupationAverage t f := by
  unfold occupationAverage
  exact div_nonneg (Finset.sum_nonneg fun M _ => hf M) (Nat.cast_nonneg _)

/-- The squarefree occupation product needed by differentiated path layers. -/
theorem occupationAverage_prod {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, (M i : ℝ)) =
      (t.descFactorial s.card : ℝ) / ((Fintype.card ι).ascFactorial s.card : ℝ) := by
  have h := occupation_factorial_moment (fun i => if i ∈ s then 1 else 0) t
  simpa [occupationAverage, apply_ite] using h

/-- Multiplication layers supply successor occupations; expand them by subsets. -/
theorem occupationAverage_prod_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) =
      ∑ z ∈ s.powerset,
        (t.descFactorial z.card : ℝ) / ((Fintype.card ι).ascFactorial z.card : ℝ) := by
  simp_rw [Finset.prod_add_one]
  rw [occupationAverage_sum]
  simp_rw [occupationAverage_prod]

lemma occupation_powerset_sum {ι : Type*} (s : Finset ι) (x : ℝ) :
    (∑ z ∈ s.powerset, x ^ z.card) = (1 + x) ^ s.card := by
  simpa using (Finset.prod_one_add (f := fun _ : ι => x) s).symm

/-- A uniform factorial-moment loss transfers to the successor product. -/
theorem occupationAverage_prod_add_one_lower_of_factorial {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℕ) (s : Finset ι) (L : ℝ)
    (hL : ∀ H ≤ s.card,
      L * ((t : ℝ) / Fintype.card ι) ^ H ≤
        (t.descFactorial H : ℝ) / ((Fintype.card ι).ascFactorial H : ℝ)) :
    L * (1 + (t : ℝ) / Fintype.card ι) ^ s.card ≤
      occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) := by
  rw [occupationAverage_prod_add_one, ← occupation_powerset_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact hL z.card (Finset.card_le_card (Finset.mem_powerset.mp hz))

/-- Independent composition averages factor without any probabilistic
independence convention being implicit. -/
theorem occupationAverage_tensor {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (a b : ℕ)
    (f : (ι →₀ ℕ) → ℝ) (g : (κ →₀ ℕ) → ℝ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
      ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset κ) b, f M * g N) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card *
          (Finset.finsuppAntidiag (Finset.univ : Finset κ) b).card : ℝ) =
      occupationAverage a f * occupationAverage b g := by
  unfold occupationAverage
  rw [← Finset.sum_mul_sum, mul_div_mul_comm]

theorem occupationAverage_prod_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) (ht : 0 < t) (hs : 2 * s.card ≤ t) :
    Real.exp (-(s.card : ℝ) ^ 2 / t - (s.card : ℝ) ^ 2 / (2 * Fintype.card ι)) *
      ((t : ℝ) / Fintype.card ι) ^ s.card ≤
        occupationAverage t (fun M => ∏ i ∈ s, (M i : ℝ)) := by
  rw [occupationAverage_prod]
  exact exp_mul_mean_pow_le_descFactorial_div_ascFactorial ht Fintype.card_pos hs

theorem occupationAverage_prod_add_one_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) (ht : 0 < t) (hs : 2 * s.card ≤ t) :
    Real.exp (-(s.card : ℝ) ^ 2 / t - (s.card : ℝ) ^ 2 / (2 * Fintype.card ι)) *
      (1 + (t : ℝ) / Fintype.card ι) ^ s.card ≤
        occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) := by
  apply occupationAverage_prod_add_one_lower_of_factorial
  intro H hH
  exact occupation_factorial_ratio_lower_of_le ht Fintype.card_pos hH hs

/-- The two-group first-trace occupation estimate, with its exact finite-size
loss and no asymptotic or independence premises. -/
theorem occupation_first_moment_lower {V U : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (a b : ℕ) (s : Finset V) (z : Finset U)
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a - (s.card : ℝ) ^ 2 / (2 * Fintype.card V)) +
        (-(z.card : ℝ) ^ 2 / b - (z.card : ℝ) ^ 2 / (2 * Fintype.card U))) *
      (((a : ℝ) / Fintype.card V) ^ s.card *
        (1 + (b : ℝ) / Fintype.card U) ^ z.card) ≤
      (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset V) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset U) b,
          (∏ i ∈ s, (M i : ℝ)) * (∏ j ∈ z, ((N j : ℝ) + 1))) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset V) a).card *
          (Finset.finsuppAntidiag (Finset.univ : Finset U) b).card : ℝ) := by
  rw [occupationAverage_tensor]
  have h₁ := occupationAverage_prod_lower a s ha hs
  have h₂ := occupationAverage_prod_add_one_lower b z hb hz
  have hprod := mul_le_mul h₁ h₂ (by positivity)
    (occupationAverage_nonneg a _ (fun M => by positivity))
  rw [Real.exp_add]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.CompositionAntidiag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- Convert a sum over function compositions to the canonical occupation finset. -/
theorem sum_compositions_eq_antidiag {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : ℕ) (f : (σ → ℕ) → ℝ) :
    (∑' d : Composition σ a, f d.val) =
      ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) a, f M := by
  calc
    _ = ∑' M : (Finset.finsuppAntidiag (Finset.univ : Finset σ) a), f M.val :=
      (compositionAntidiagEquiv σ a).tsum_eq (fun M => f M.val)
    _ = _ := by
      rw [tsum_fintype]
      exact Finset.sum_coe_sort _ (fun M : σ →₀ ℕ => f M)

/-- Denominator conversion for the same index equivalence. -/
theorem card_compositions_eq_antidiag {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : ℕ) :
    Nat.card (Composition σ a) =
      (Finset.finsuppAntidiag (Finset.univ : Finset σ) a).card := by
  rw [Nat.card_congr (compositionAntidiagEquiv σ a), Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-- The function-composition average is exactly the canonical occupation average. -/
theorem composition_average_eq_occupationAverage {σ : Type*}
    [Fintype σ] [DecidableEq σ] (a : ℕ) (f : (σ → ℕ) → ℝ) :
    (∑' d : Composition σ a, f d.val) / (Nat.card (Composition σ a) : ℝ) =
      occupationAverage a (fun M : σ →₀ ℕ => f M) := by
  rw [sum_compositions_eq_antidiag, card_compositions_eq_antidiag]
  rfl

/-- The actual bidegree-domain average, expressed directly using the canonical
occupation-average API. This bridges the Fock/matrix source indices and both
first- and second-moment inequalities. -/
theorem bidegree_average_eq_occupationAverage {σ : Type*} [Fintype σ] [DecidableEq σ]
    (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Nat.card (Index isV a b) : ℝ) =
      occupationAverage a (fun M : {x // isV x = true} →₀ ℕ => f M) *
        occupationAverage b (fun M : {x // ¬ isV x = true} →₀ ℕ => g M) := by
  classical
  rw [average_split, composition_average_eq_occupationAverage,
    composition_average_eq_occupationAverage]

/-- Matrix-indexed finite-sum version of the bridge. -/
theorem bidegree_average_eq_occupationAverage_fintype {σ : Type*}
    [Fintype σ] [DecidableEq σ] (isV : σ → Bool) (a b : ℕ)
    [Fintype (Index isV a b)]
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑ d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Fintype.card (Index isV a b) : ℝ) =
      occupationAverage a (fun M : {x // isV x = true} →₀ ℕ => f M) *
        occupationAverage b (fun M : {x // ¬ isV x = true} →₀ ℕ => g M) := by
  simpa only [tsum_fintype, Nat.card_eq_fintype_card] using
    bidegree_average_eq_occupationAverage isV a b f g

/-- The first occupation-moment lower estimate on the ACTUAL bidegree exponent
source, rather than on an auxiliary Cartesian product of composition finsets. -/
theorem bidegree_first_moment_lower {σ : Type*} [Fintype σ] [DecidableEq σ]
    (isV : σ → Bool) (a b : ℕ)
    [Fintype (Index isV a b)]
    [Nonempty {x // isV x = true}] [Nonempty {x // ¬ isV x = true}]
    (s : Finset {x // isV x = true}) (z : Finset {x // ¬ isV x = true})
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a -
        (s.card : ℝ) ^ 2 / (2 * Fintype.card {x // isV x = true})) +
      (-(z.card : ℝ) ^ 2 / b -
        (z.card : ℝ) ^ 2 / (2 * Fintype.card {x // ¬ isV x = true}))) *
      (((a : ℝ) / Fintype.card {x // isV x = true}) ^ s.card *
        (1 + (b : ℝ) / Fintype.card {x // ¬ isV x = true}) ^ z.card) ≤
      (∑ d : Index isV a b,
        (∏ i ∈ s, (d.val i : ℝ)) * (∏ i ∈ z, ((d.val i : ℝ) + 1))) /
        (Fintype.card (Index isV a b) : ℝ) := by
  rw [bidegree_average_eq_occupationAverage_fintype isV a b
    (fun M => ∏ i ∈ s, (M i : ℝ))
    (fun M => ∏ i ∈ z, ((M i : ℝ) + 1))]
  have h := occupation_first_moment_lower a b s z ha hb hs hz
  rw [occupationAverage_tensor] at h
  exact h

end Problem335.BidegreeAverages

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathOccupationGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [DecidableEq σ]

theorem card_selectedPathCoordinates (side : σ → Bool) (p : List σ)
    (hp : p.Nodup) (b : Bool) :
    (selectedPathCoordinates side p b).card =
      (p.filter (fun x => side x == b)).length := by
  rw [selectedPathCoordinates, Finset.card_subtype]
  have hf : p.toFinset.filter (fun x => side x = b) =
      (p.filter (fun x => side x == b)).toFinset := by
    ext x
    simp
  rw [hf]
  exact List.toFinset_card_of_nodup (hp.filter _)

/-- Partitioning a squarefree path product into its two coordinate groups. -/
theorem path_product_split {R : Type*} [CommMonoid R]
    (side : σ → Bool) (p : List σ) (hp : p.Nodup) (f g : σ → R) :
    (p.map (fun x => if side x then f x else g x)).prod =
      (∏ x ∈ selectedPathCoordinates side p true, f x.val) *
        ∏ x ∈ selectedPathCoordinates side p false, g x.val := by
  rw [← List.prod_toFinset _ hp]
  simp only [selectedPathCoordinates, Finset.prod_subtype_eq_prod_filter]
  rw [← Finset.prod_filter_mul_prod_filter_not p.toFinset
    (fun x => side x = true) (fun x => if side x then f x else g x)]
  congr 1
  · apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]
  · have hf : p.toFinset.filter (fun x => ¬side x = true) =
        p.toFinset.filter (fun x => side x = false) := by
      ext x
      simp
    rw [hf]
    apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]

/-- The squared Fock amplitude is exactly the product of the derivative
occupations and successor multiplication occupations, on disjoint group types. -/
theorem pathAmplitude_sq_split [Fintype σ] (side : σ → Bool)
    (p : List σ) (hp : p.Nodup) (d : σ →₀ ℕ) :
    ((p.map (occupationAmplitude side d)).prod) ^ 2 =
      (∏ x ∈ selectedPathCoordinates side p true, (d x.val : ℝ)) *
        ∏ x ∈ selectedPathCoordinates side p false, ((d x.val : ℝ) + 1) := by
  rw [pathAmplitude_sq]
  exact path_product_split side p hp _ _

/-- Selecting coordinates from a path selects exactly the same number as
selecting its layer labels. -/
theorem card_selectedPathCoordinates_of_labels {ι : Type*} [DecidableEq ι]
    (side : σ → Bool) (labels : List σ) (p : List (σ × ι × ι))
    (hlabels : p.map Prod.fst = labels) (hnodup : labels.Nodup) (b : Bool) :
    (selectedPathCoordinates (fun x : σ × ι × ι => side x.1) p b).card =
      (labels.filter (fun x => side x == b)).length := by
  have hp : p.Nodup := List.Nodup.of_map Prod.fst (hlabels ▸ hnodup)
  rw [card_selectedPathCoordinates _ _ hp]
  rw [← hlabels, List.filter_map, List.length_map]
  rfl

/-- Every actual IMM path selects one coordinate in each selected layer,
including when the ambient layer has inactive endpoint coordinates. -/
theorem immPath_selectedCoordinates_card (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n hn) (b : Bool) :
    (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1) p b).card =
      (Finset.univ.filter (fun t : Fin n => side t = b)).card := by
  rw [card_selectedPathCoordinates_of_labels side (List.finRange n) p
    (immPaths_labels n hn p hp) (List.nodup_finRange n)]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter
    (fun x => side x == b))]
  congr 1
  ext x
  simp

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathMassLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open BidegreeAverages

/-- Boolean-fiber form of the occupation lower estimate. -/
theorem bidegree_first_moment_lower_bool {σ : Type*} [Fintype σ] [DecidableEq σ]
    (side : σ → Bool) (a b : ℕ) [Fintype (Index side a b)]
    [Nonempty {x // side x = true}] [Nonempty {x // side x = false}]
    (s : Finset {x // side x = true}) (z : Finset {x // side x = false})
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a -
        (s.card : ℝ) ^ 2 / (2 * Fintype.card {x // side x = true})) +
      (-(z.card : ℝ) ^ 2 / b -
        (z.card : ℝ) ^ 2 / (2 * Fintype.card {x // side x = false}))) *
      (((a : ℝ) / Fintype.card {x // side x = true}) ^ s.card *
        (1 + (b : ℝ) / Fintype.card {x // side x = false}) ^ z.card) ≤
      (∑ d : Index side a b,
        (∏ i ∈ s, (d.val i : ℝ)) * (∏ i ∈ z, ((d.val i : ℝ) + 1))) /
        (Fintype.card (Index side a b) : ℝ) := by
  let : Nonempty {x // ¬ side x = true} := by
    simpa only [Bool.not_eq_true] using
      (inferInstance : Nonempty {x // side x = false})
  let e : {x // ¬ side x = true} ≃ {x // side x = false} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  have hcard : Fintype.card {x // ¬ side x = true} =
      Fintype.card {x // side x = false} := Fintype.card_congr e
  have h := BidegreeAverages.bidegree_first_moment_lower side a b
    s (z.map e.symm.toEmbedding) ha hb hs (by simpa using hz)
  simpa only [Finset.card_map, hcard, Finset.prod_map,
    Equiv.coe_toEmbedding, Equiv.subtypeEquivRight_symm_apply, e] using h

/-- Each squarefree Fock path has large average squared amplitude over the
actual bidegree source. No independence of coordinates within a group is assumed. -/
theorem path_source_mass_lower {σ : Type*} [Fintype σ] [DecidableEq σ]
    (side : σ → Bool) (a b : ℕ) [Fintype (Index side a b)]
    [Nonempty {x // side x = true}] [Nonempty {x // side x = false}]
    (p : List σ) (hp : p.Nodup) (ha : 0 < a) (hb : 0 < b)
    (hs : 2 * (selectedPathCoordinates side p true).card ≤ a)
    (hz : 2 * (selectedPathCoordinates side p false).card ≤ b) :
    Real.exp ((-((selectedPathCoordinates side p true).card : ℝ) ^ 2 / a -
        ((selectedPathCoordinates side p true).card : ℝ) ^ 2 /
          (2 * Fintype.card {x // side x = true})) +
      (-((selectedPathCoordinates side p false).card : ℝ) ^ 2 / b -
        ((selectedPathCoordinates side p false).card : ℝ) ^ 2 /
          (2 * Fintype.card {x // side x = false}))) *
      (((a : ℝ) / Fintype.card {x // side x = true}) ^
          (selectedPathCoordinates side p true).card *
        (1 + (b : ℝ) / Fintype.card {x // side x = false}) ^
          (selectedPathCoordinates side p false).card) ≤
      (∑ d : Index side a b,
        ((p.map (occupationAmplitude side d.val)).prod) ^ 2) /
        (Fintype.card (Index side a b) : ℝ) := by
  simpa only [pathAmplitude_sq_split side p hp] using
    bidegree_first_moment_lower_bool side a b
      (selectedPathCoordinates side p true) (selectedPathCoordinates side p false)
      ha hb hs hz

/-- Concrete IMM per-path first moment. The loss and geometric benchmark depend
only on the selected layer counts, not on the chosen path. -/
theorem immPath_source_mass_lower (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ)
    [Fintype (Index (fun x : Fin n × Fin n × Fin n => side x.1) a b)]
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = true}]
    [Nonempty {x : Fin n × Fin n × Fin n // side x.1 = false}]
    (p : List (Fin n × Fin n × Fin n)) (hp : p ∈ immPaths n hn)
    (ha : 0 < a) (hb : 0 < b)
    (hs : 2 * (Finset.univ.filter (fun t : Fin n => side t = true)).card ≤ a)
    (hz : 2 * (Finset.univ.filter (fun t : Fin n => side t = false)).card ≤ b) :
    Real.exp ((-((Finset.univ.filter (fun t : Fin n => side t = true)).card : ℝ) ^ 2 / a -
        ((Finset.univ.filter (fun t : Fin n => side t = true)).card : ℝ) ^ 2 /
          (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true})) +
      (-((Finset.univ.filter (fun t : Fin n => side t = false)).card : ℝ) ^ 2 / b -
        ((Finset.univ.filter (fun t : Fin n => side t = false)).card : ℝ) ^ 2 /
          (2 * Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false}))) *
      (((a : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true}) ^
          (Finset.univ.filter (fun t : Fin n => side t = true)).card *
        (1 + (b : ℝ) / Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false}) ^
          (Finset.univ.filter (fun t : Fin n => side t = false)).card) ≤
      (∑ d : Index (fun x : Fin n × Fin n × Fin n => side x.1) a b,
        ((p.map (occupationAmplitude (fun x => side x.1) d.val)).prod) ^ 2) /
        (Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1) a b) : ℝ) := by
  have hs' : 2 * (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
      p true).card ≤ a := by
    rwa [immPath_selectedCoordinates_card n hn side p hp true]
  have hz' : 2 * (selectedPathCoordinates (fun x : Fin n × Fin n × Fin n => side x.1)
      p false).card ≤ b := by
    rwa [immPath_selectedCoordinates_card n hn side p hp false]
  simpa only [immPath_selectedCoordinates_card n hn side p hp] using
    path_source_mass_lower (fun x : Fin n × Fin n × Fin n => side x.1) a b p
      (immPaths_nodup n hn p hp) ha hb hs' hz'

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.PathMassParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open BidegreeAverages LowerParameters

/-- A Boolean layer choice includes all square-matrix coordinates in that layer. -/
theorem card_bool_layer_variables {n : ℕ} (side : Fin n → Bool) (ε : Bool) :
    Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = ε} =
      (Finset.univ.filter (fun t : Fin n => side t = ε)).card * n ^ 2 := by
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    card_layer_variables (Finset.univ.filter (fun t : Fin n => side t = ε))

/-- Uniform per-path first-moment estimate at the canonical lower-bound
parameters. Its only partition hypotheses are the two selected layer counts. -/
theorem immPath_source_mass_lower_parameters {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool)
    (hk : (Finset.univ.filter (fun t : Fin n => side t = true)).card = k n)
    (hm : (Finset.univ.filter (fun t : Fin n => side t = false)).card = m n)
    [Fintype (Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n))]
    (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n (by omega)) :
    Real.exp (-64 / Real.sqrt (n : ℝ)) *
      (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n) ≤
      (∑ d : Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n),
        ((p.map (occupationAmplitude (fun x => side x.1) d.val)).prod) ^ 2) /
        (Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1)
          (a n) (b n)) : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  have hv : Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true} = v n := by
    rw [card_bool_layer_variables, hk]
    rfl
  have hu : Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false} = u n := by
    rw [card_bool_layer_variables, hm]
    rfl
  let : Nonempty {x : Fin n × Fin n × Fin n // side x.1 = true} :=
    Fintype.card_pos_iff.mp (by rw [hv]; exact v_pos hn4)
  let : Nonempty {x : Fin n × Fin n × Fin n // side x.1 = false} :=
    Fintype.card_pos_iff.mp (by rw [hu]; exact u_pos hn4)
  have hs : 2 * (Finset.univ.filter (fun t : Fin n => side t = true)).card ≤ a n := by
    rw [hk]
    have := four_mul_n_le_a hn
    have := k_le_n n
    omega
  have hz : 2 * (Finset.univ.filter (fun t : Fin n => side t = false)).card ≤ b n := by
    rw [hm]
    have := four_mul_n_le_b hn
    have := m_le_n n
    omega
  have hpath := immPath_source_mass_lower n (by omega) side (a n) (b n) p hp
    (a_pos hn4) (b_pos hn4) hs hz
  simp only [hk, hm, hv, hu] at hpath
  have hkn : (k n : ℝ) ≤ 2 * (n : ℝ) := by
    have h : (k n : ℝ) ≤ n := by exact_mod_cast k_le_n n
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmn : (m n : ℝ) ≤ 2 * (n : ℝ) := by
    have h : (m n : ℝ) ≤ n := by exact_mod_cast m_le_n n
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hloss := occupation_two_orders_loss_le hn
    (Nat.cast_nonneg (α := ℝ) (k n)) hkn (Nat.cast_nonneg (α := ℝ) (m n)) hmn
  have hexp : Real.exp (-64 / Real.sqrt (n : ℝ)) ≤
      Real.exp ((-(k n : ℝ) ^ 2 / a n - (k n : ℝ) ^ 2 / (2 * (v n : ℝ))) +
        (-(m n : ℝ) ^ 2 / b n - (m n : ℝ) ^ 2 / (2 * (u n : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_div] at hloss ⊢
    linarith
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hpath

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ImmFirstMomentParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

open LowerParameters

/-- The first trace of the actual finite normalized IMM matrix at the canonical
occupation parameters. The path-count and geometric scale agree with the second
moment normalization; there are no auxiliary matrix-identity hypotheses. -/
theorem immNormalizedMatrix_first_moment_lower_parameters {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool) (hk : immLayerVCount side = k n)
    (hm : immLayerUCount side = m n) :
    (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) *
      ((n : ℝ) ^ (n - 1) *
        (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) *
          Real.exp (-64 / Real.sqrt (n : ℝ)) ≤
      ((immNormalizedMatrix n side (a n) (b n)).conjTranspose *
        immNormalizedMatrix n side (a n) (b n)).trace.re := by
  classical
  have h := immNormalizedMatrix_first_trace_lower_of_average n (by omega)
    side (a n) (b n)
    (Real.exp (-64 / Real.sqrt (n : ℝ)) *
      (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) (by
      intro p
      have hpath := immPath_source_mass_lower_parameters hn side hk hm
        ((immPaths n (by omega)).get p) (List.get_mem _ p)
      change _ ≤ (∑ d : ImmSourceIndex n side (a n) (b n),
        immPathAmplitude n (by omega) (fun x => side x.1) d.1 p ^ 2) /
          (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) at hpath
      exact hpath)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- A weaker square-root-exponential version is convenient for the final
rank lower bound, whose constant absorbs both trace losses. -/
theorem immNormalizedMatrix_first_moment_lower_sqrt {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool) (hk : immLayerVCount side = k n)
    (hm : immLayerUCount side = m n) :
    (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) *
      ((n : ℝ) ^ (n - 1) *
        (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) *
          Real.exp (-64 * Real.sqrt (n : ℝ)) ≤
      ((immNormalizedMatrix n side (a n) (b n)).conjTranspose *
        immNormalizedMatrix n side (a n) (b n)).trace.re := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hexp : Real.exp (-64 * Real.sqrt (n : ℝ)) ≤
      Real.exp (-64 / Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hspos).mpr
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans
    (immNormalizedMatrix_first_moment_lower_parameters hn side hk hm)

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.ActualImmRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the concrete rank measure with the finite normalized
matrix used in the IMM trace estimates. -/

noncomputable section

namespace Problem335.LowerParameters

theorem card_immSourceIndex_eq_rankDimension {n : ℕ} (hn : 4 ≤ n) :
    (Fintype.card (ImmSourceIndex n (balancedLayer hn) (a n) (b n)) : ℝ) =
      rankDimension n := by
  have h := card_bidegree_finsupp_exponents
    (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1) (a n) (b n)
  rw [balancedVariable_card_true hn, balancedVariable_card_false hn,
    Nat.multichoose_eq, Nat.multichoose_eq] at h
  simp only [Nat.card_eq_fintype_card] at h
  unfold rankDimension homogeneousDim
  exact_mod_cast h

theorem rankData_imm_eq_matrixRank {n : ℕ} (hn : 4 ≤ n) :
    rankData n (imm ℂ n) =
      ((immNormalizedMatrix n (balancedLayer hn) (a n) (b n)).rank : ℝ) := by
  rw [rankData_eq hn, immNormalizedMatrix_rank]
  simp only [immLayerVCount, immLayerUCount,
    balancedLayer_card_true hn, balancedLayer_card_false hn]

/-- The configured actual first trace, in the common normalization used by
the final rank comparison. -/
theorem configured_imm_first_trace_lower {n : ℕ} (hn : 16 ≤ n) :
    rankDimension n * rankMomentScale n * Real.exp (-(64 * Real.sqrt (n : ℝ))) ≤
      ((immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).trace.re := by
  have hn4 : 4 ≤ n := by omega
  have h := immNormalizedMatrix_first_moment_lower_sqrt hn (balancedLayer hn4)
    (balancedLayer_card_true hn4) (balancedLayer_card_false hn4)
  rw [card_immSourceIndex_eq_rankDimension hn4] at h
  simpa only [rankMomentScale, mul_assoc, neg_mul] using h

/-- After the actual first-moment estimate is discharged, the sole remaining
matrix hypothesis for the configured rank lower bound is the second trace. -/
theorem rankData_imm_lower_of_second_trace_bound {n : ℕ} (hn : 16 ≤ n) (C : ℝ)
    (hsecond :
      (((immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 * Real.exp (C * Real.sqrt (n : ℝ))) :
    rankDimension n * Real.exp (-((128 + C) * Real.sqrt (n : ℝ))) ≤
      rankData n (imm ℂ n) := by
  have hn4 : 4 ≤ n := by omega
  have h := rank_lower_bound_of_trace_moment_bounds
    (immNormalizedMatrix n (balancedLayer hn4) (a n) (b n))
    (rankDimension_pos hn4) (rankMomentScale_pos hn4)
    (configured_imm_first_trace_lower hn) hsecond
  rw [← rankData_imm_eq_matrixRank hn4] at h
  have he : 2 * (64 * Real.sqrt (n : ℝ)) + C * Real.sqrt (n : ℝ) =
      (128 + C) * Real.sqrt (n : ℝ) := by ring
  simpa only [he] using h

end Problem335.LowerParameters

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem335

open Filter

/-- The numerical comparison in the lower-bound argument, with an explicit
sufficient logarithmic threshold. No algebraic complexity hypotheses enter here. -/
theorem size_lower_bound_of_rank_bounds
    (x S D R C₁ C₂ : ℝ)
    (hx : 1 ≤ x) (hS : 0 ≤ S) (hD : 0 < D)
    (hlog : 400 * (|C₁| + |C₂| + 1) ≤ Real.log x)
    (hlower : D * Real.exp (-C₁ * Real.sqrt x) ≤ R)
    (hupper : R ≤ 2 * S ^ 2 * D * Real.exp (C₂ * Real.sqrt x) *
      x ^ (-Real.sqrt x / 100)) :
    x ^ (Real.sqrt x / 400) ≤ S := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hbounds := hlower.trans hupper
  have hleftpos : 0 < D * Real.exp (-C₁ * Real.sqrt x) :=
    mul_pos hD (Real.exp_pos _)
  have hSpos : 0 < S := by
    by_contra h
    have hzero : S = 0 := le_antisymm (le_of_not_gt h) hS
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hbounds
    exact (not_le_of_gt hleftpos) hbounds
  have hlogs := Real.log_le_log hleftpos hbounds
  have hDne : D ≠ 0 := ne_of_gt hD
  have hSne : S ≠ 0 := ne_of_gt hSpos
  simp [Real.log_mul, Real.log_pow, Real.log_rpow hxpos,
    hDne, hSne, ne_of_gt (Real.rpow_pos_of_pos hxpos (-Real.sqrt x / 100))] at hlogs
  have hsqrt : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have habs₁ := le_abs_self C₁
  have habs₂ := le_abs_self C₂
  have hnonneg₁ := abs_nonneg C₁
  have hnonneg₂ := abs_nonneg C₂
  have hslack : C₁ + C₂ + 1 ≤ Real.log x / 400 := by linarith
  have hslackmul := mul_le_mul_of_nonneg_right hslack (Real.sqrt_nonneg x)
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have htarget : Real.sqrt x / 400 * Real.log x ≤ Real.log S := by
    nlinarith
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) hSpos).mp
  rw [Real.log_rpow hxpos]
  exact htarget

/-- Fixed exponential losses can be absorbed uniformly into the power saving.
The threshold is independent of `S`, `D`, and the rank value `R`. -/
theorem eventual_size_lower_bound_of_rank_bounds (C₁ C₂ : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ S D R : ℝ,
      0 ≤ S → 0 < D →
      D * Real.exp (-C₁ * Real.sqrt (n : ℝ)) ≤ R →
      R ≤ 2 * S ^ 2 * D * Real.exp (C₂ * Real.sqrt (n : ℝ)) *
        (n : ℝ) ^ (-Real.sqrt (n : ℝ) / 100) →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ S := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hcast
  have hone : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n :=
    hcast.eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      400 * (|C₁| + |C₂| + 1) ≤ Real.log (n : ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hone.and hlarge)
  refine ⟨n₀, ?_⟩
  intro n hn S D R hS hD hlower hupper
  exact size_lower_bound_of_rank_bounds (n : ℝ) S D R C₁ C₂
    (hn₀ n hn).1 hS hD (hn₀ n hn).2 hlower hupper

end Problem335

end

end OAI
end

section
-- module Solutions.OAIQW_Problem335.LowerBoundAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circuit-size lower bounds from eventual rank and second-trace estimates
for the normalized IMM matrix. -/

noncomputable section

namespace Problem335

open LowerParameters

/-- An eventual lower bound for the configured IMM rank, together with the
proved circuit upper bound, gives the exact complex circuit-size conclusion. -/
theorem complex_depth_five_lower_bound_of_eventual_rank_lower (C : ℝ)
    (hlower : ∀ᶠ n : ℕ in Filter.atTop,
      rankDimension n * Real.exp (-C * Real.sqrt (n : ℝ)) ≤
        rankData n (imm ℂ n)) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  obtain ⟨Nlower, hNlower⟩ := Filter.eventually_atTop.mp hlower
  obtain ⟨Nupper, hNupper⟩ := exists_rankData_circuit_upper_cutoff
  obtain ⟨Nnumeric, hNnumeric⟩ :=
    eventual_size_lower_bound_of_rank_bounds C (24 + 4 * Real.log 5)
  refine ⟨max 4 (max Nlower (max Nupper Nnumeric)), ?_⟩
  intro n hn c hc
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hnlo : Nlower ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnup : Nupper ≤ n :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnnum : Nnumeric ≤ n :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  apply hNnumeric n hnnum (circuitSize c) (rankDimension n)
    (rankData n (imm ℂ n)) (Nat.cast_nonneg _) (rankDimension_pos hn4)
    (hNlower n hnlo)
  simpa only [hc] using hNupper n hnup c hc

/-- The second-trace bound, together with the first-trace and circuit
estimates, implies the complex circuit-size lower bound. -/
theorem complex_depth_five_lower_bound_of_eventual_second_trace_oai (C : ℝ)
    (hsecond : ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 16 ≤ n,
      (((immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 *
          Real.exp (C * Real.sqrt (n : ℝ))) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  apply complex_depth_five_lower_bound_of_eventual_rank_lower (128 + C)
  filter_upwards [hsecond, Filter.eventually_ge_atTop 16] with n hn hlarge
  simpa only [neg_mul] using
    rankData_imm_lower_of_second_trace_bound hlarge C (hn hlarge)

end Problem335

end

end OAI
end

theorem solution : type_of% @OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace_oai := @OAI.Problem335.complex_depth_five_lower_bound_of_eventual_second_trace_oai
