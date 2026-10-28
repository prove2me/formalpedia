-- Prove2me | solution 1 for OAI.TraceReconstruction.source_reference_clipped_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:05:45.748028+00:00
-- url     : https://prove2.me/submissions/9f73b393-d9e5-4a1b-929c-ff35ebc29380

import Mathlib
import Definitions.Def_OAIQ9Tr002

section
-- module Solutions.OAIQ9_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem product_succ_expect (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      P.expect (fun a => (P.product n).expect (fun b => f (Fin.cons a b))) := by
  unfold expect product
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (∏ j, P.mass ((Fin.cons a b : Fin (n + 1) → α) j)) * f (Fin.cons a b) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
theorem small_geometric_sum (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 2)) :
    (∑ j ∈ Finset.range n, x ^ j) ≤ 2 := by
  have he := geom_sum_mul x n
  have hn : 0 ≤ ∑ j ∈ Finset.range n, x ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hx.1 j)
  have hp := pow_nonneg hx.1 n
  nlinarith [mul_le_mul_of_nonneg_left hx.2 hn]

/-- Elementary tail of a binomial polynomial after cancelling orders zero and one. -/
theorem small_binomial_tail (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (∑ j ∈ Finset.range (n - 1), (n.choose (j + 2) : ℝ) * x ^ (j + 2)) ≤
      2 * ((n : ℝ) * x) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ 2 * ((n : ℝ) * x) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hc : (n.choose (j + 2) : ℝ) ≤ (n : ℝ) ^ (j + 2) := by
        exact_mod_cast Nat.choose_le_pow n (j + 2)
      calc
        _ ≤ (n : ℝ) ^ (j + 2) * x ^ (j + 2) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
        _ = _ := by rw [← mul_pow, pow_add]; ring
    _ = ((n : ℝ) * x) ^ 2 * ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ j := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := small_geometric_sum (n - 1) ⟨mul_nonneg (Nat.cast_nonneg n) hx, hsmall⟩
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ) * x))]

theorem expect_pow_expansion (P : FiniteLaw α) (Z : α → ℝ) (u : ℝ) (t : ℕ) :
    P.expect (fun a => (1 + u * Z a) ^ t) =
      ∑ j ∈ Finset.range (t + 1), (t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j) := by
  unfold expect
  simp_rw [add_comm (1 : ℝ), add_pow, one_pow, mul_one, mul_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_small_affine_pow (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ) (ht : 2 ≤ t)
    (hcenter : P.expect Z = 0)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2)
    {u : ℝ} (hu : (t : ℝ) * |u| ≤ 1 / 2) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 1 + 4 * ((t : ℝ) * u) ^ 2 := by
  rw [expect_pow_expansion]
  have ht' : t + 1 = 2 + (t - 1) := by omega
  rw [ht', Finset.sum_range_add]
  have hz : P.expect (fun _ : α => (1 : ℝ)) = 1 := by simp [expect, P.total]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
    Nat.choose_one_right, pow_one]
  rw [hz, hcenter]
  simp only [mul_zero, add_zero]
  have hb : (∑ j ∈ Finset.range (t - 1), (t.choose (2 + j) : ℝ) * u ^ (2 + j) *
      P.expect (fun a => Z a ^ (2 + j))) ≤
      2 * ∑ j ∈ Finset.range (t - 1), (t.choose (j + 2) : ℝ) * |u| ^ (j + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjt : 2 + j ≤ t := by have := Finset.mem_range.mp hj; omega
    have hm := hmom (2 + j) hjt
    calc
      _ ≤ |(t.choose (2 + j) : ℝ) * u ^ (2 + j) * P.expect (fun a => Z a ^ (2 + j))| :=
        le_abs_self _
      _ ≤ (t.choose (2 + j) : ℝ) * |u| ^ (2 + j) * 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by rw [Nat.add_comm 2 j]; ring
  have htail := small_binomial_tail t (abs_nonneg u) hu
  have he : ((t : ℝ) * |u|) ^ 2 = ((t : ℝ) * u) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  rw [he] at htail
  linarith

/-- Only the centered first moment must vanish; lower absolute moments
are obtained from the one available source moment, without boundedness. -/
theorem expect_lower_moment_le_two (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (ht : P.expect (fun a => |Z a| ^ t) ≤ 1) (j : ℕ) (hj : j ≤ t) :
    |P.expect (fun a => Z a ^ j)| ≤ 2 := by
  have hpoint (a : α) : |Z a| ^ j ≤ 1 + |Z a| ^ t := by
    by_cases hx : |Z a| ≤ 1
    · have h := pow_le_one₀ (n := j) (abs_nonneg _) hx
      nlinarith [pow_nonneg (abs_nonneg (Z a)) t]
    · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hj
      linarith
  calc
    _ ≤ ∑ a, |P.mass a * Z a ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.mass a * |Z a| ^ j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (P.nonneg a), abs_pow]
    _ ≤ ∑ a, P.mass a * (1 + |Z a| ^ t) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a)
    _ = 1 + P.expect (fun a => |Z a| ^ t) := by
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib, P.total]
      rfl
    _ ≤ 2 := by linarith

theorem expect_affine_pow_le (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 2 * (1 + |u|) ^ t := by
  rw [expect_pow_expansion, add_comm (1 : ℝ), add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := hmom j (by have := Finset.mem_range.mp hj; omega)
  calc
    _ ≤ |(t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j)| := le_abs_self _
    _ ≤ (t.choose j : ℝ) * |u| ^ j * 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by simp only [one_pow, mul_one]; ring

/-- Scalar two-smoothness at even moment order; its constant is linear
in that order after taking the square root, as required for tensorization. -/
theorem scalar_even_moment_unit (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ (2 * k)) ≤
      (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
  have hmom := expect_lower_moment_le_two P Z (2 * k) ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htR : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
  have hbase : 1 ≤ 1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (6 * ((2 * k : ℕ) : ℝ))) (sq_nonneg u)]
  by_cases hu : ((2 * k : ℕ) : ℝ) * |u| ≤ 1 / 2
  · have hs := expect_small_affine_pow P Z (2 * k) (by omega) hcenter hmom hu
    have hb : 1 + 4 * (((2 * k : ℕ) : ℝ) * u) ^ 2 ≤
        1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [sq_nonneg (((2 * k : ℕ) : ℝ) * u)]
    exact hs.trans (hb.trans (le_self_pow₀ hbase (by omega)))
  · have hu' : 1 / 2 ≤ ((2 * k : ℕ) : ℝ) * |u| := le_of_lt (lt_of_not_ge hu)
    have hsum : 1 + |u| ≤ 3 * ((2 * k : ℕ) : ℝ) * |u| := by
      have hh := mul_le_mul_of_nonneg_right htR (abs_nonneg u)
      nlinarith
    have hc : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := le_self_pow₀ (by norm_num) (by omega)
    calc
      _ ≤ 2 * (1 + |u|) ^ (2 * k) := expect_affine_pow_le P Z (2 * k) hmom u
      _ ≤ 2 * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by gcongr
      _ ≤ 2 ^ (2 * k) * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
        rw [← mul_pow, pow_mul]
        congr 1
        simp only [mul_pow, sq_abs]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) k

/-- Homogeneous version of the scalar even-moment inequality. -/
theorem scalar_even_moment (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (b v : ℝ) :
    P.expect (fun a => (b + v * Z a) ^ (2 * k)) ≤
      (b ^ 2 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * v ^ 2) ^ k := by
  have heven (a : α) : |Z a| ^ (2 * k) = Z a ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have hmoment : P.expect (fun a => Z a ^ (2 * k)) ≤ 1 := by
    simpa only [heven] using ht
  have hc : 1 ≤ (6 * (2 * k : ℕ) : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
    nlinarith
  by_cases hb : b = 0
  · subst b
    simp only [zero_add, zero_pow (by omega : 2 ≠ 0)]
    have he : P.expect (fun a => (v * Z a) ^ (2 * k)) =
        v ^ (2 * k) * P.expect (fun a => Z a ^ (2 * k)) := by
      simp only [expect, mul_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he]
    calc
      _ ≤ v ^ (2 * k) := by
        have hv : 0 ≤ v ^ (2 * k) := by rw [pow_mul]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hmoment hv]
      _ = (v ^ 2) ^ k := pow_mul v 2 k
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg v) (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg v)]) k
  · have hs := scalar_even_moment_unit P Z k hk hcenter ht (v / b)
    have hbpow : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; positivity
    have he : P.expect (fun a => (b + v * Z a) ^ (2 * k)) =
        b ^ (2 * k) * P.expect (fun a => (1 + v / b * Z a) ^ (2 * k)) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have h : b + v * Z a = b * (1 + v / b * Z a) := by field_simp [hb]
      dsimp only
      rw [h, mul_pow]
      ring
    rw [he]
    calc
      _ ≤ b ^ (2 * k) * (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * (v / b) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left hs hbpow
      _ = _ := by
        rw [pow_mul, ← mul_pow]
        congr 1
        field_simp [hb]

theorem weighted_minkowski_bound (P : FiniteLaw α) (k : ℕ) (hk : 1 ≤ k)
    (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : P.expect (fun a => f a ^ k) ≤ A ^ k)
    (hgb : P.expect (fun a => g a ^ k) ≤ B ^ k) :
    P.expect (fun a => (f a + g a) ^ k) ≤ (A + B) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  let w : α → ℝ := fun a => P.mass a ^ (1 / (k : ℝ))
  have hw (a : α) : 0 ≤ w a := Real.rpow_nonneg (P.nonneg a) _
  have hwk (a : α) : w a ^ k = P.mass a := by
    dsimp [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (P.nonneg a), one_div_mul_cancel hk0, Real.rpow_one]
  have hsingle (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) :
      (∑ a, |w a * F a| ^ (k : ℝ)) = P.expect (fun a => F a ^ k) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_of_nonneg (mul_nonneg (hw a) (hF a)), Real.rpow_natCast, mul_pow, hwk]
  have hsum : (∑ a, |w a * f a + w a * g a| ^ (k : ℝ)) =
      P.expect (fun a => (f a + g a) ^ k) := by
    simp_rw [← mul_add]
    exact hsingle _ (fun a => add_nonneg (hf a) (hg a))
  have hm := Real.Lp_add_le Finset.univ (fun a => w a * f a) (fun a => w a * g a) hkR
  rw [hsum, hsingle f hf, hsingle g hg] at hm
  have hroots (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) (C : ℝ) (hC : 0 ≤ C)
      (hFC : P.expect (fun a => F a ^ k) ≤ C ^ k) :
      (P.expect (fun a => F a ^ k)) ^ (1 / (k : ℝ)) ≤ C := by
    calc
      _ ≤ (C ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (hF a) k))) hFC (by positivity)
      _ = C := by
        rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv hC hk0]
  have hroot : (P.expect (fun a => (f a + g a) ^ k)) ^ (1 / (k : ℝ)) ≤ A + B :=
    hm.trans (add_le_add (hroots f hf A hA hfa) (hroots g hg B hB hgb))
  have hexp : 0 ≤ P.expect (fun a => (f a + g a) ^ k) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (add_nonneg (hf a) (hg a)) k))
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hexp _) hroot k
  rw [← Real.rpow_natCast, ← Real.rpow_mul hexp, one_div_mul_cancel hk0, Real.rpow_one] at hp
  exact hp
theorem product_succ_expect_tail (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      (P.product n).expect (fun b => P.expect (fun a => f (Fin.cons a b))) := by
  rw [product_succ_expect]
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end TraceReconstruction.FiniteLaw
namespace TraceReconstruction
variable {α : Type*}

theorem multilinearEnergy_nonneg {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    0 ≤ multilinearEnergy A R := by
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro j _
  split <;> positivity

theorem multilinear_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (Z : α → ℝ)
    (x : Fin n → α) (a : α) :
    multilinear A Z (Fin.cons a x) =
      multilinear (fun σ => A (Fin.cons false σ)) Z x +
      Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x := by
  unfold multilinear
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem multilinearEnergy_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R =
      multilinearEnergy (fun σ => A (Fin.cons false σ)) R +
      R ^ 2 * multilinearEnergy (fun σ => A (Fin.cons true σ)) R := by
  unfold multilinearEnergy
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- The finite-product moment inequality used for every score expansion.
The order-cost is linear per degree, and no boundedness assumption is needed. -/
theorem multilinear_even_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z = 0)
    (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => multilinear A Z x ^ (2 * k)) ≤
      (multilinearEnergy A (6 * (2 * k : ℕ))) ^ k := by
  induction n with
  | zero =>
    simp only [FiniteLaw.expect, FiniteLaw.product, multilinear, multilinearEnergy,
      Fintype.prod_empty, mul_one, one_mul]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact le_of_eq (pow_mul _ 2 k)
  | succ n ih =>
    let A0 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons false σ)
    let A1 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons true σ)
    let R : ℝ := 6 * (2 * k : ℕ)
    let F0 : (Fin n → α) → ℝ := fun x => multilinear A0 Z x
    let F1 : (Fin n → α) → ℝ := fun x => multilinear A1 Z x
    have h0 := ih A0
    have h1 := ih A1
    have hA0 := multilinearEnergy_nonneg A0 R
    have hA1 := multilinearEnergy_nonneg A1 R
    rw [FiniteLaw.product_succ_expect_tail, multilinearEnergy_cons]
    calc
      _ ≤ (P.product n).expect (fun x => (F0 x ^ 2 + R ^ 2 * F1 x ^ 2) ^ k) := by
        apply FiniteLaw.expect_mono
        intro x
        simp_rw [multilinear_cons]
        have hs := FiniteLaw.scalar_even_moment P Z k hk hcenter ht (F0 x) (F1 x)
        simpa only [F0, F1, A0, A1, R, mul_comm] using hs
      _ ≤ (multilinearEnergy A0 R + R ^ 2 * multilinearEnergy A1 R) ^ k := by
        apply FiniteLaw.weighted_minkowski_bound (P.product n) k hk
          (fun x => F0 x ^ 2) (fun x => R ^ 2 * F1 x ^ 2)
          (fun x => sq_nonneg _) (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (multilinearEnergy A0 R) (R ^ 2 * multilinearEnergy A1 R) hA0
          (mul_nonneg (sq_nonneg _) hA1)
        · simpa only [← pow_mul] using h0
        · have he : (P.product n).expect (fun x => (R ^ 2 * F1 x ^ 2) ^ k) =
              (R ^ 2) ^ k * (P.product n).expect (fun x => F1 x ^ (2 * k)) := by
            unfold FiniteLaw.expect
            simp only [mul_pow, ← pow_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [he, mul_pow (R ^ 2) (multilinearEnergy A1 R)]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (sq_nonneg R) k)
      _ = _ := rfl

theorem monomial_weight {n : ℕ} (σ : Fin n → Bool) (R : ℝ) :
    (∏ j, if σ j then R ^ 2 else 1) = R ^ (2 * monomialDegree σ) := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, ← pow_mul, monomialDegree]

end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]

theorem eventMass_nonneg (P : FiniteLaw α) (A : Finset α) : 0 ≤ P.eventMass A :=
  Finset.sum_nonneg (fun a _ => P.nonneg a)

theorem eventMass_le_one (P : FiniteLaw α) (A : Finset α) : P.eventMass A ≤ 1 := by
  rw [← P.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => P.nonneg a)

theorem overlap_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    overlap P (condition P A hA) = P.eventMass A := by
  classical
  have he (a : α) : min (P.mass a) ((condition P A hA).mass a) =
      if a ∈ A then P.mass a else 0 := by
    by_cases ha : a ∈ A
    · simp only [condition, ha, ↓reduceIte]
      apply min_eq_left
      apply (le_div_iff₀ hA).mpr
      have h := mul_le_mul_of_nonneg_left (P.eventMass_le_one A) (P.nonneg a)
      simpa only [mul_one] using h
    · simp only [condition, ha, ↓reduceIte, min_eq_right (P.nonneg a)]
  unfold overlap
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, eventMass]

theorem tv_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    tv P (condition P A hA) = 1 - P.eventMass A := by
  have he := P.overlap_condition A hA
  rw [overlap_eq_one_sub_tv] at he
  linarith

theorem density_bad_mass_sq (P : FiniteLaw α) (f : α → ℝ) (A : Finset α) :
    (∑ a ∈ A, P.mass a * f a) ^ 2 ≤
      (P.eventMass A) * P.expect (fun a => f a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun a => Real.sqrt (P.mass a))
    (fun a => Real.sqrt (P.mass a) * f a)
  simp only [mul_pow, Real.sq_sqrt (P.nonneg _)] at h
  have he : (∑ a ∈ A, Real.sqrt (P.mass a) * (Real.sqrt (P.mass a) * f a)) =
      ∑ a ∈ A, P.mass a * f a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (P.nonneg a)]
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (P.eventMass_nonneg A)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
    mul_nonneg (P.nonneg a) (sq_nonneg _))

/-- Loss from the small-reference-density event by the exact available moment. -/
theorem low_density_reference_mass (P : FiniteLaw α) (f : α → ℝ) (t : ℕ)
    (A : Finset α) (hA : ∀ a ∈ A, f a < 1 / 2) :
    P.eventMass A ≤ (2 : ℝ) ^ t * P.expect (fun a => |f a - 1| ^ t) := by
  have hlocal (a : α) (ha : a ∈ A) : 1 ≤ (2 : ℝ) ^ t * |f a - 1| ^ t := by
    rw [← mul_pow]
    apply one_le_pow₀
    have hh := neg_le_abs (f a - 1)
    linarith [hA a ha]
  calc
    _ ≤ ∑ a ∈ A, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      apply Finset.sum_le_sum
      intro a ha
      nlinarith [mul_le_mul_of_nonneg_left (hlocal a ha) (P.nonneg a)]
    _ ≤ ∑ a, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => by positivity [P.nonneg a])
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Exact common-event likelihood ratio: no lower bound is imposed off the event. -/
theorem conditioned_density_identity (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (hfm : R.expect f = 1) (hgm : R.expect g = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 0 < f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A)
    (hQ : 0 < (R.withDensity g hg hgm).eventMass A) (a : α) :
    (condition (R.withDensity g hg hgm) A hQ).mass a =
      (condition (R.withDensity f hf hfm) A hP).mass a *
      ((R.withDensity f hf hfm).eventMass A /
        (R.withDensity g hg hgm).eventMass A * (g a / f a)) := by
  classical
  by_cases ha : a ∈ A
  · simp only [condition, ha, ↓reduceIte]
    change R.mass a * g a / (R.withDensity g hg hgm).eventMass A =
      R.mass a * f a / (R.withDensity f hf hfm).eventMass A *
        ((R.withDensity f hf hfm).eventMass A /
          (R.withDensity g hg hgm).eventMass A * (g a / f a))
    field_simp [ne_of_gt hP, ne_of_gt hQ, ne_of_gt (hAf a ha)]
  · simp only [condition, ha, ↓reduceIte, zero_mul]

/-- The raw likelihood score on a common clipping event, at every integer moment. -/
theorem clipped_raw_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hfm : R.expect f = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 1 / 2 ≤ f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect
        (fun a => |g a / f a - 1| ^ (k + 1)) ≤
      (2 : ℝ) ^ k / (R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |g a - f a| ^ (k + 1)) := by
  classical
  have hpoint (a : α) (ha : a ∈ A) :
      f a * |g a / f a - 1| ^ (k + 1) ≤
        (2 : ℝ) ^ k * |g a - f a| ^ (k + 1) := by
    have hp : 0 < f a := lt_of_lt_of_le (by norm_num) (hAf a ha)
    rw [div_sub_one (ne_of_gt hp), abs_div, abs_of_pos hp]
    have hi : 0 ≤ 1 / f a := by positivity
    have hi2 : 1 / f a ≤ 2 := (div_le_iff₀ hp).mpr (by linarith [hAf a ha])
    calc
      _ = |g a - f a| ^ (k + 1) * (1 / f a) ^ k := by
        rw [div_pow, div_pow, one_pow, pow_succ (f a)]
        field_simp [ne_of_gt hp]
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hi hi2 k) (show 0 ≤ |g a - f a| ^ (k + 1) by positivity)
  unfold expect
  calc
    _ = ∑ a ∈ A, (R.mass a * (f a * |g a / f a - 1| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      simp only [condition, withDensity]
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ A, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum
      intro a ha
      apply div_le_div_of_nonneg_right _ hP.le
      nlinarith [mul_le_mul_of_nonneg_left (hpoint a ha) (R.nonneg a)]
    _ ≤ ∑ a, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro a _ _
      positivity [R.nonneg a]
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; ring

/-- Normalizing the second conditioned law costs only its scalar normalization error. -/
theorem score_rescaling_moment (P : FiniteLaw α) (u : α → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    P.expect (fun a => |c * u a - 1| ^ (k + 1)) ≤
      2 ^ k * (c ^ (k + 1) * P.expect (fun a => |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1)) := by
  have hb (a : α) : |c * u a - 1| ^ (k + 1) ≤
      2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) + |c - 1| ^ (k + 1)) := by
    have he : c * u a - 1 = c * (u a - 1) + (c - 1) := by ring
    rw [he]
    calc
      _ ≤ (|c * (u a - 1)| + |c - 1|) ^ (k + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
      _ ≤ _ := by
        have h := add_pow_le (abs_nonneg (c * (u a - 1))) (abs_nonneg (c - 1)) (k + 1)
        simpa only [Nat.add_sub_cancel, abs_mul, abs_of_nonneg hc, mul_pow] using h
  unfold expect
  calc
    _ ≤ ∑ a, P.mass a * (2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) +
        |c - 1| ^ (k + 1))) := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (hb a) (P.nonneg a))
    _ = 2 ^ k * (c ^ (k + 1) * (∑ a, P.mass a * |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1) * ∑ a, P.mass a) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ = _ := by rw [P.total, mul_one]
end TraceReconstruction.FiniteLaw

namespace TraceReconstruction
variable {α Ω : Type*} [Fintype Ω]

theorem coefficient_nonneg {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : 0 ≤ averagedCoefficient R θ σ := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (R.nonneg ω)
  apply Finset.prod_nonneg
  intro i _
  cases σ i <;> cases θ ω i <;> norm_num

theorem coefficient_le_one {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : averagedCoefficient R θ σ ≤ 1 := by
  rw [← R.total]
  apply Finset.sum_le_sum
  intro ω _
  have h : selectionCoefficient (θ ω) σ ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _; cases σ i <;> cases θ ω i <;> norm_num
    · intro i _; cases σ i <;> cases θ ω i <;> norm_num
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (R.nonneg ω)

/-- The coefficient for the empty subset is exactly one, before or after averaging. -/
theorem averagedCoefficient_empty {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) :
    averagedCoefficient R θ (fun _ => false) = 1 := by
  simp [averagedCoefficient, selectionCoefficient, FiniteLaw.expect, R.total]

end TraceReconstruction

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Parity
attribute [-instance] _root_.OAI.TraceReconstruction.OccupiedParityTree.edgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraLeafEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.labelsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parity

Parity-tree roles, forced leaves, coefficient shapes, and exact unsigned/signed motif expansions.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

theorem signedRoleCount_le_active {n : ℕ} (r : Fin n → Fin 3) :
    signedRoleCount r ≤ activeRoleCount r := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]
  decide

/-- A surviving odd node either has a unique active signed motif (the
local high-order cancellation case), or at least two active children. -/
theorem odd_roles_singleton_or_branch {n : ℕ} (r : Fin n → Fin 3)
    (hodd : Odd (signedRoleCount r)) :
    (∃ i, r i=2 ∧ ∀ j, j≠i → r j=0) ∨ 2 ≤ activeRoleCount r := by
  have hpos : 0 < signedRoleCount r := hodd.pos
  have hle := signedRoleCount_le_active r
  by_cases h : 2 ≤ activeRoleCount r
  · exact Or.inr h
  have ha : activeRoleCount r=1 := by omega
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp ha
  have hmem : ∀ j, r j≠0 ↔ j=i := by
    intro j
    have he := Finset.ext_iff.mp hi j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using he
  have hs : ∃ j, r j=2 := by
    have hs0 : (Finset.univ.filter fun j => r j=2).Nonempty := Finset.card_pos.mp hpos
    obtain ⟨j,hj⟩ := hs0
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  obtain ⟨j,hj⟩ := hs
  have hij := (hmem j).mp (by rw [hj]; decide)
  subst j
  exact Or.inl ⟨i,hj,fun j hji => Classical.byContradiction (fun hn => hji ((hmem j).mp hn))⟩

end TraceReconstruction

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
attribute [local instance] Classical.propDecidable

theorem motif_child_sign {χ σ τ : ℝ} (hm : IsMotifValue χ σ) (ht : IsTypeSign τ) :
    IsTypeSign (1-χ+σ*τ) := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,hσ⟩
  · exact Or.inl (by ring)
  · rcases hσ with rfl | rfl <;> rcases ht with rfl | rfl <;>
      norm_num [IsTypeSign]

theorem sign_pow_parity {τ : ℝ} (ht : IsTypeSign τ) (n : ℕ) :
    τ^n = if Odd n then τ else 1 := by
  rcases ht with rfl | rfl
  · simp
  · split_ifs with hn
    · exact hn.neg_one_pow
    · exact (Nat.not_odd_iff_even.mp hn).neg_one_pow

/-- Product expansion with an arbitrary three-role scalar per child; the
only sign variable is the current vertex type. -/
theorem arbitrary_role_expansion {n : ℕ} (w : Fin n → Fin 3 → ℝ) (τ : ℝ) :
    (∏ i, ∑ a : Fin 3, w i a * (if a=2 then τ else 1)) =
      ∑ a : Fin n → Fin 3, (∏ i, w i (a i))*τ^signedRoleCount a := by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ,Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← Finset.prod_filter]
  simp [signedRoleCount]

theorem bottomRole_sum (χ σ τ : ℝ) :
    (∑ a : Fin 3, bottomRoleWeight χ σ a*(if a=2 then τ else 1)) = (χ-σ*τ)/2 := by
  rw [Fin.sum_univ_three]
  have h01 : (0:Fin 3) ≠ 1 := by decide
  have h02 : (0:Fin 3) ≠ 2 := by decide
  have h12 : (1:Fin 3) ≠ 2 := by decide
  simp only [bottomRoleWeight,h02,h12,Ne.symm h01,Ne.symm h02,Ne.symm h12,
    ↓reduceIte,zero_add,mul_one]
  ring

theorem internalRole_sum (odd : Prop) [Decidable odd] (χ σ τ : ℝ) :
    (∑ a : Fin 3, internalRoleWeight odd χ σ a*(if a=2 then τ else 1)) =
      if odd then 1-χ+σ*τ else 1 := by
  rw [Fin.sum_univ_three]
  have h01 : (0:Fin 3) ≠ 1 := by decide
  have h02 : (0:Fin 3) ≠ 2 := by decide
  have h12 : (1:Fin 3) ≠ 2 := by decide
  by_cases h : odd <;> simp only [internalRoleWeight,roleWeight,h,h02,h12,
    Ne.symm h01,Ne.symm h02,Ne.symm h12,↓reduceIte,zero_mul,add_zero,mul_one]
  ring

namespace CoefficientShape

/-- Full finite coefficient expansion, before any orientation average or
fit-event conditioning. This is the literal algebra behind source
the correlated-anchor estimate, the parity roles being retained in every term. -/
theorem expansion {b : ℕ} (t : CoefficientShape b) (ha : t.Admissible)
    {τ : ℝ} (ht : IsTypeSign τ) :
    t.eval τ = ∑ a : t.Choice, t.weight a * (if (t.termTree a).isOdd then τ else 1) := by
  classical
  induction t generalizing τ with
  | bottom n χ σ =>
    have H := arbitrary_role_expansion (fun i => bottomRoleWeight (χ i) (σ i)) τ
    simp_rw [bottomRole_sum,sign_pow_parity ht] at H
    trans ∑ a : Fin n → Fin 3, (∏ i, bottomRoleWeight (χ i) (σ i) (a i)) *
      (if Odd (signedRoleCount a) then τ else 1)
    · exact H
    · apply Finset.sum_congr rfl
      intro a _
      apply congrArg (fun z => (∏ i, bottomRoleWeight (χ i) (σ i) (a i))*z)
      change _ = @ite ℝ (Odd (signedRoleCount a)) (Classical.propDecidable _) τ 1
      split_ifs <;> rfl
  | @node b n χ σ children ih =>
    change (∏ i, (children i).eval (1-χ i+σ i*τ)) = _
    have he (i : Fin n) := ih i (ha.2 i) (motif_child_sign (ha.1 i) ht)
    simp_rw [he]
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    change (∑ a : (i : Fin n) → (children i).Choice,
      ∏ i, (children i).weight (a i)*
        (if ((children i).termTree (a i)).isOdd then 1-χ i+σ i*τ else 1)) =
      ∑ a : ((i : Fin n) → (children i).Choice) × (Fin n → Fin 3),
        (∏ i, (children i).weight (a.1 i)*
          internalRoleWeight ((children i).termTree (a.1 i)).isOdd (χ i) (σ i) (a.2 i))*
        (@ite ℝ (Odd (signedRoleCount a.2)) (Classical.propDecidable _) τ 1)
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    have H := arbitrary_role_expansion (fun i =>
      internalRoleWeight ((children i).termTree (a i)).isOdd (χ i) (σ i)) τ
    simp_rw [internalRole_sum,sign_pow_parity ht] at H
    rw [Finset.prod_mul_distrib,H,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a' _
    rw [Finset.prod_mul_distrib,mul_assoc]
    congr 2
    split_ifs <;> rfl

/-- Nonzero terms automatically satisfy the source active-odd rule. -/
theorem term_valid {b : ℕ} (t : CoefficientShape b) (a : t.Choice)
    (h : t.weight a ≠ 0) : (t.termTree a).valid := by
  classical
  induction t with
  | bottom n χ σ => exact ⟨fun _ _ => trivial,fun _ => trivial⟩
  | @node b n χ σ children ih =>
    have hp (i : Fin n) : (children i).weight (a.1 i) *
        internalRoleWeight ((children i).termTree (a.1 i)).isOdd (χ i) (σ i) (a.2 i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
    constructor
    · intro i hai
      by_contra hn
      have hz := (mul_ne_zero_iff.mp (hp i)).2
      simp [internalRoleWeight,hn,hai] at hz
    · intro i
      exact ih i (a.1 i) (mul_ne_zero_iff.mp (hp i)).1

/-- The difference of hypotheses consists exactly of odd root terms. -/
theorem difference_expansion {b : ℕ} (t : CoefficientShape b) (ha : t.Admissible) :
    t.eval 1-t.eval (-1) = 2*∑ a : t.Choice,
      if (t.termTree a).isOdd then t.weight a else 0 := by
  classical
  rw [expansion t ha (Or.inl rfl),expansion t ha (Or.inr rfl),
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

end CoefficientShape
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
namespace OccupiedParityTree

/-- Every surviving nonsingleton term has an embedded binary subtree.
The selection depends only on the role-marked shape. -/
theorem forced_nonempty {b : ℕ} (t : OccupiedParityTree b)
    (hv : t.valid) (hn : t.noSingleton) (ho : t.isOdd) : Nonempty t.Forced := by
  classical
  induction t with
  | leaf => exact ⟨.leaf⟩
  | @node b n children roles ih =>
    have hod : Odd (signedRoleCount roles) := ho
    have ha : 2 ≤ activeRoleCount roles := by
      have := signedRoleCount_le_active roles
      have := hod.pos
      have := hn.1 hod
      omega
    obtain ⟨a,ha,c,hc,hne⟩ := Finset.one_lt_card.mp ha
    have ha' : roles a≠0 := (Finset.mem_filter.mp ha).2
    have hc' : roles c≠0 := (Finset.mem_filter.mp hc).2
    obtain ⟨la⟩ := ih a (hv.2 a) (hn.2 a) (hv.1 a ha')
    obtain ⟨lc⟩ := ih c (hv.2 c) (hn.2 c) (hv.1 c hc')
    exact ⟨.node a c hne ha' hc' la lc⟩

theorem levelCount_le_leaves {b : ℕ} (t : OccupiedParityTree b) (ht : t.occupied)
    (k : ℕ) : t.levelCount k ≤ t.leafCount := by
  induction t generalizing k with
  | leaf => cases k <;> norm_num [levelCount,leafCount]
  | @node b n children roles ih =>
    cases k with
    | zero => exact leafCount_pos (.node n children roles) ht
    | succ k => exact Finset.sum_le_sum (fun i _ => ih i (ht.2 i) k)

/-- At every positive nonroot level, each unforced occupied vertex costs
 an extra leaf. This is the exact combinatorial inequality used when
 additional (nonbinary) labels are summed in the correlated-anchor estimate. -/
theorem Forced.level_extra {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (k : ℕ) :
    t.levelCount k+2^b ≤ t.leafCount+2^k := by
  classical
  induction F generalizing k with
  | leaf => cases k <;> simp [levelCount,leafCount]
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    cases k with
    | zero =>
      have hl := (Forced.node a c hne ha hc left right).leaf_lower
      simpa only [levelCount,pow_zero,Nat.add_comm] using Nat.add_le_add_left hl 1
    | succ k =>
      have hh := sum_two_improvements
        (fun i => (children i).levelCount k) (fun i => (children i).leafCount)
        hne (2^b) (2^k) (fun i _ _ => levelCount_le_leaves _ (ht.2 i) k)
        (ihl (ht.2 a) k) (ihr (ht.2 c) k)
      simpa only [levelCount,leafCount,pow_succ,Nat.mul_comm] using hh

theorem Forced.nonforced_vertices_le_extra_leaves {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (ht : t.occupied) (k : ℕ) :
    t.levelCount k-2^k ≤ t.leafCount-2^b := by
  have := F.level_extra ht k
  have := F.leaf_lower
  omega

end OccupiedParityTree
end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/

theorem centralBinom_square_bound (n : ℕ) :
    ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 ≤ (16 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hr : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc : 4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2) ≤
        16 * (n + 1) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
    have hh : ((n : ℝ) + 1) ^ 2 *
        ((n + 2) * ((n + 1).centralBinom : ℝ) ^ 2) ≤
        ((n : ℝ) + 1) ^ 2 * (16 * 16 ^ n) := by
      calc
        _ = (n + 2) * (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) ^ 2 := by ring
        _ = (4 * (2 * (n : ℝ) + 1) ^ 2 * (n + 2)) *
            (n.centralBinom : ℝ) ^ 2 := by rw [hr]; ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 3) * (n.centralBinom : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = (16 * ((n : ℝ) + 1) ^ 2) *
            (((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2) := by ring
        _ ≤ (16 * ((n : ℝ) + 1) ^ 2) * 16 ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
    have := (mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
    rw [pow_succ (16 : ℝ) n]
    convert this using 1 <;> push_cast <;> first | rfl | ring

theorem choose_odd_le_twice_central (n k : ℕ) :
    (2 * n + 1).choose k ≤ 2 * n.centralBinom := by
  cases k with
  | zero => simp only [Nat.choose_zero_right]; have := Nat.centralBinom_pos n; omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h₁ := Nat.choose_le_centralBinom k n
    have h₂ := Nat.choose_le_centralBinom (k + 1) n
    simpa [Nat.succ_eq_add_one, two_mul] using Nat.add_le_add h₁ h₂

theorem fairBinomial_square_bound (n k : ℕ) :
    ((n : ℝ) + 1) * fairBinomial n k ^ 2 ≤ 2 := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hcases with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hc : ((2 * m).choose k : ℝ) ≤ (m.centralBinom : ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom k m
    have hcs : ((2 * m).choose k : ℝ) ^ 2 ≤ (m.centralBinom : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m)) ^ 2 = 16 ^ m := by
      rw [← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity),
      sq_nonneg ((2 * m).choose k : ℝ)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
    have hc : ((2 * m + 1).choose k : ℝ) ≤ 2 * (m.centralBinom : ℝ) :=
      by exact_mod_cast choose_odd_le_twice_central m k
    have hcs : ((2 * m + 1).choose k : ℝ) ^ 2 ≤ 4 * (m.centralBinom : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * m + 1).choose k : ℝ)) hc 2
      nlinarith
    have ht := centralBinom_square_bound m
    have hp : ((2 : ℝ) ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
      rw [pow_add, mul_pow, ← pow_mul, show 2 * m * 2 = 4 * m by omega, pow_mul]
      norm_num
      ring
    unfold fairBinomial
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ (2 * m + 1)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0 : ℝ) ≤ m + 1 by positivity)]


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

theorem series_summable (f : IntSeries) (φ : ℝ → ℝ) (hφ : φ 0 = 0) :
    Summable (fun z : ℤ => φ (f.coeff z)) :=
  summable_of_hasFiniteSupport (f.coeff.hasFiniteSupport.fun_comp hφ)

theorem seriesL1_nonneg (f : IntSeries) : 0 ≤ seriesL1 f :=
  tsum_nonneg fun _ => abs_nonneg _

theorem seriesL2Sq_nonneg (f : IntSeries) : 0 ≤ seriesL2Sq f :=
  tsum_nonneg fun _ => sq_nonneg _

theorem seriesL1_eq_sum (f : IntSeries) :
    seriesL1 f = ∑ z ∈ f.coeff.support, |f.coeff z| := by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]

theorem series_summable_shift (f : IntSeries) (φ : ℝ → ℝ)
    (hφ : φ 0 = 0) (a : ℤ) :
    Summable (fun z : ℤ => φ (f.coeff (a + z))) := by
  exact (Equiv.addLeft a).summable_iff.mpr (series_summable f φ hφ)

theorem series_sum_shift (f : IntSeries) (φ : ℝ → ℝ) (a : ℤ) :
    (∑' z : ℤ, φ (f.coeff (a + z))) = ∑' z : ℤ, φ (f.coeff z) :=
  (Equiv.addLeft a).tsum_eq (fun z => φ (f.coeff z))

theorem series_coeff_mul_abs_le (f g : IntSeries) (z : ℤ) :
    |(f * g).coeff z| ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun a => f.coeff a * g.coeff (-a + z)) f.coeff.support

theorem seriesL1_mul_le (f g : IntSeries) :
    seriesL1 (f * g) ≤ seriesL1 f * seriesL1 g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * |g.coeff (-a + z)|) :=
    (series_summable_shift g abs (by simp) (-a)).mul_left _
  calc
    seriesL1 (f * g) ≤ ∑' z : ℤ, ∑ a ∈ f.coeff.support,
        |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_le_tsum (series_coeff_mul_abs_le f g) (series_summable (f * g) abs (by simp))
        (summable_sum fun a _ => hh a)
    _ = ∑ a ∈ f.coeff.support, ∑' z : ℤ, |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_finsetSum fun a _ => hh a
    _ = (∑ a ∈ f.coeff.support, |f.coeff a|) * seriesL1 g := by
      simp_rw [tsum_mul_left, series_sum_shift]
      exact (Finset.sum_mul _ _ _).symm
    _ = seriesL1 f * seriesL1 g := by rw [seriesL1_eq_sum f]

theorem series_coeff_mul_sq_le (f g : IntSeries) (z : ℤ) :
    (f * g).coeff z ^ 2 ≤ seriesL1 f *
      ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, seriesL1_eq_sum]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _; exact abs_nonneg _
  · intro a _; positivity
  · intro a _
    rw [mul_pow, ← mul_assoc, ← sq, sq_abs]

theorem seriesL2Sq_mul_le (f g : IntSeries) :
    seriesL2Sq (f * g) ≤ seriesL1 f ^ 2 * seriesL2Sq g := by
  have hh (a : ℤ) : Summable (fun z : ℤ => |f.coeff a| * (g.coeff (-a + z)) ^ 2) :=
    (series_summable_shift g (fun x => x ^ 2) (by simp) (-a)).mul_left _
  calc
    seriesL2Sq (f * g) ≤ ∑' z : ℤ, seriesL1 f *
        ∑ a ∈ f.coeff.support, |f.coeff a| * (g.coeff (-a + z)) ^ 2 :=
      Summable.tsum_le_tsum (series_coeff_mul_sq_le f g)
        (series_summable (f * g) (fun x => x ^ 2) (by simp))
        ((summable_sum fun a _ => hh a).mul_left _)
    _ = seriesL1 f * ∑ a ∈ f.coeff.support,
        ∑' z : ℤ, |f.coeff a| * (g.coeff (-a + z)) ^ 2 := by
      rw [tsum_mul_left, Summable.tsum_finsetSum fun a _ => hh a]
    _ = seriesL1 f ^ 2 * seriesL2Sq g := by
      simp_rw [tsum_mul_left, series_sum_shift g (fun x => x ^ 2)]
      rw [← Finset.sum_mul, ← seriesL1_eq_sum]
      unfold seriesL2Sq
      ring

theorem series_coeff_mul_bound (f g : IntSeries) (M : ℝ)
    (hg : ∀ z, |g.coeff z| ≤ M) (z : ℤ) :
    |(f * g).coeff z| ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * |g.coeff (-a + z)| :=
      series_coeff_mul_abs_le f g z
    _ ≤ ∑ a ∈ f.coeff.support, |f.coeff a| * M :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
    _ = seriesL1 f * M := by rw [← Finset.sum_mul, ← seriesL1_eq_sum]

/-! The probability generating series of the fair binomial kernel. -/

theorem fairSeries_add (m n : ℕ) : fairSeries (m + n) = fairSeries m * fairSeries n :=
  pow_add _ m n

theorem seriesL1_eq_sum_range (f : IntSeries) (n : ℕ)
    (hneg : ∀ z < 0, f.coeff z = 0)
    (hhigh : ∀ k : ℕ, n < k → f.coeff k = 0) :
    seriesL1 f = ∑ k ∈ Finset.range (n + 1), |f.coeff (k : ℤ)| := by
  let e : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  calc
    seriesL1 f = ∑ z ∈ (Finset.range (n + 1)).map e, |f.coeff z| := by
      apply tsum_eq_sum
      intro z hz
      by_cases h : 0 ≤ z
      · have heq : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have hh : n < z.toNat := by
          by_contra hn
          apply hz
          exact Finset.mem_map.mpr ⟨z.toNat, Finset.mem_range.mpr (by omega), heq⟩
        rw [← heq, hhigh _ hh, abs_zero]
      · rw [hneg z (by omega), abs_zero]
    _ = _ := Finset.sum_map _ e _

theorem firstDifference_coeff (f : IntSeries) (z : ℤ) :
    (firstDifference * f).coeff z = f.coeff z - f.coeff (z - 1) := by
  rw [firstDifference, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_comm _ f, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [neg_zero, add_zero, mul_one, sub_eq_add_neg]

theorem fairSeries_difference_coeff_zero (n : ℕ) :
    (firstDifference * fairSeries n).coeff 0 = fairBinomial n 0 := by
  rw [firstDifference_coeff]
  norm_num only [zero_sub]
  rw [fairSeries_coeff_neg n (-1) (by norm_num), sub_zero]
  exact fairSeries_coeff_nat n 0

theorem fairSeries_difference_coeff_succ (n k : ℕ) :
    (firstDifference * fairSeries n).coeff (↑(k + 1) : ℤ) =
      fairBinomial n (k + 1) - fairBinomial n k := by
  rw [firstDifference_coeff, fairSeries_coeff_nat]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, fairSeries_coeff_nat]

theorem fairBinomial_unimodal_left (n k : ℕ) (hk : k < n / 2) :
    fairBinomial n k ≤ fairBinomial n (k + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk

theorem fairBinomial_unimodal_right (n k : ℕ) (hk : n / 2 ≤ k) :
    fairBinomial n (k + 1) ≤ fairBinomial n k := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnk : n - k ≤ k + 1 := by omega
  have hmul := Nat.mul_le_mul_left (n.choose k) hnk
  rw [← Nat.choose_succ_right_eq] at hmul
  exact_mod_cast Nat.le_of_mul_le_mul_right hmul (by omega : 0 < k + 1)

theorem fairBinomial_variation (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), |fairBinomial n (k + 1) - fairBinomial n k|) =
      2 * fairBinomial n (n / 2) - fairBinomial n 0 := by
  have hmid : n / 2 ≤ n + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hmid]
  have hl : (∑ k ∈ Finset.range (n / 2),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n 0 := by
    rw [← Finset.sum_range_sub (fairBinomial n) (n / 2)]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr
      (fairBinomial_unimodal_left n k (Finset.mem_range.mp hk)))
  have hr : (∑ k ∈ Finset.Ico (n / 2) (n + 1),
      |fairBinomial n (k + 1) - fairBinomial n k|) =
      fairBinomial n (n / 2) - fairBinomial n (n + 1) := by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2) (n + 1),
          -(fairBinomial n (k + 1) - fairBinomial n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr
          (fairBinomial_unimodal_right n k (Finset.mem_Ico.mp hk).1))
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_Ico_sub _ hmid]; ring
  rw [hl, hr]
  have hzero : fairBinomial n (n + 1) = 0 := by simp [fairBinomial]
  rw [hzero]
  ring

theorem fairSeries_difference_L1 (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) = 2 * fairBinomial n (n / 2) := by
  rw [seriesL1_eq_sum_range _ (n + 1)]
  · rw [Finset.sum_range_succ', Nat.cast_zero, fairSeries_difference_coeff_zero,
      abs_of_nonneg (fairBinomial_nonneg n 0)]
    simp_rw [fairSeries_difference_coeff_succ]
    rw [fairBinomial_variation]
    ring
  · intro z hz
    rw [firstDifference_coeff, fairSeries_coeff_neg n z hz,
      fairSeries_coeff_neg n (z - 1) (by omega), sub_zero]
  · intro k hk
    have hkpos : 0 < k := by omega
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
    rw [fairSeries_difference_coeff_succ]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt (by omega : n < v),
      Nat.choose_eq_zero_of_lt (by omega : n < v + 1)]

theorem binomialBound_nonneg (n : ℕ) : 0 ≤ binomialBound n := Real.sqrt_nonneg _

theorem fairBinomial_le_bound (n k : ℕ) : fairBinomial n k ≤ binomialBound n := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  simpa only [mul_comm] using fairBinomial_square_bound n k

theorem fairSeries_coeff_bound (n : ℕ) (z : ℤ) :
    |(fairSeries n).coeff z| ≤ binomialBound n := by
  by_cases hz : 0 ≤ z
  · rw [← Int.toNat_of_nonneg hz, fairSeries_coeff_nat,
      abs_of_nonneg (fairBinomial_nonneg _ _)]
    exact fairBinomial_le_bound _ _
  · rw [fairSeries_coeff_neg n z (by omega), abs_zero]
    exact binomialBound_nonneg n

theorem fairSeries_L1 (n : ℕ) : seriesL1 (fairSeries n) = 1 := by
  rw [seriesL1_eq_sum_range _ n (fairSeries_coeff_neg n)]
  · simp_rw [fairSeries_coeff_nat, abs_of_nonneg (fairBinomial_nonneg _ _)]
    unfold fairBinomial
    rw [← Finset.sum_div]
    have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum, div_self (by positivity)]
  · intro k hk
    rw [fairSeries_coeff_nat]
    simp [fairBinomial, Nat.choose_eq_zero_of_lt hk]

theorem seriesL2Sq_le_L1_mul_bound (f : IntSeries) (M : ℝ)
    (hf : ∀ z, |f.coeff z| ≤ M) : seriesL2Sq f ≤ seriesL1 f * M := by
  calc
    _ ≤ ∑' z : ℤ, |f.coeff z| * M := by
      apply Summable.tsum_le_tsum
      · intro z
        calc
          f.coeff z ^ 2 = |f.coeff z| * |f.coeff z| := by rw [← sq, sq_abs]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)
      · exact series_summable f (fun x => x ^ 2) (by simp)
      · exact (series_summable f abs (by simp)).mul_right M
    _ = _ := tsum_mul_right

theorem fairSeries_L2Sq_bound (n : ℕ) : seriesL2Sq (fairSeries n) ≤ binomialBound n := by
  simpa only [fairSeries_L1, one_mul] using
    seriesL2Sq_le_L1_mul_bound (fairSeries n) (binomialBound n) (fairSeries_coeff_bound n)

theorem fairSeries_difference_L1_bound (n : ℕ) :
    seriesL1 (firstDifference * fairSeries n) ≤ 2 * binomialBound n := by
  rw [fairSeries_difference_L1]
  exact mul_le_mul_of_nonneg_left (fairBinomial_le_bound n (n / 2)) (by norm_num)

theorem seriesL1_single (z : ℤ) (r : ℝ) :
    seriesL1 (AddMonoidAlgebra.single z r) = |r| := by
  unfold seriesL1
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [apply_ite abs, abs_zero]
  exact tsum_ite_eq' z (fun _ : ℤ => |r|)

theorem seriesL1_one : seriesL1 (1 : IntSeries) = 1 := by
  change seriesL1 (AddMonoidAlgebra.single 0 1) = 1
  rw [seriesL1_single, abs_one]

theorem seriesL1_pow_le (f : IntSeries) (s : ℕ) : seriesL1 (f ^ s) ≤ seriesL1 f ^ s := by
  induction s with
  | zero => simp only [pow_zero, seriesL1_one, le_refl]
  | succ s ih =>
    rw [pow_succ, pow_succ]
    exact (seriesL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (seriesL1_nonneg f))

theorem fairSeries_mul_power (n s : ℕ) :
    firstDifference ^ s * fairSeries ((s + 1) * n) =
      (firstDifference * fairSeries n) ^ s * fairSeries n := by
  simp only [fairSeries, add_mul, one_mul, pow_add, pow_mul, mul_pow]
  ring

/-- Quantitative higher-order smoothing, with n trials assigned to each
    difference and one further group reserved for anti-concentration. -/
theorem binomial_difference_coeff_bound (n s : ℕ) (z : ℤ) :
    |(firstDifference ^ s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 * binomialBound n) ^ s * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (series_coeff_mul_bound _ _ _ (fairSeries_coeff_bound n) z).trans
  apply mul_le_mul_of_nonneg_right _ (binomialBound_nonneg n)
  exact (seriesL1_pow_le _ _).trans
    (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)

theorem binomial_difference_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (firstDifference ^ s * fairSeries ((s + 1) * n)) ≤
      ((2 * binomialBound n) ^ s) ^ 2 * binomialBound n := by
  rw [fairSeries_mul_power]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (seriesL1_nonneg _)
    exact (seriesL1_pow_le _ _).trans
      (pow_le_pow_left₀ (seriesL1_nonneg _) (fairSeries_difference_L1_bound n) s)
  · exact fairSeries_L2Sq_bound n
  · exact seriesL2Sq_nonneg _
  · positivity

theorem seriesL1_add_le (f g : IntSeries) :
    seriesL1 (f + g) ≤ seriesL1 f + seriesL1 g := by
  calc
    _ ≤ ∑' z : ℤ, (|f.coeff z| + |g.coeff z|) := by
      apply Summable.tsum_le_tsum
      · intro z
        simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
          abs_add_le (f.coeff z) (g.coeff z)
      · exact series_summable (f + g) abs (by simp)
      · exact (series_summable f abs (by simp)).add (series_summable g abs (by simp))
    _ = _ := (series_summable f abs (by simp)).tsum_add (series_summable g abs (by simp))

theorem seriesL1_zero : seriesL1 (0 : IntSeries) = 0 := by
  simp [seriesL1]

theorem seriesL1_sum_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∑ i ∈ A, f i) ≤ ∑ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, seriesL1_zero, le_refl]
  | @insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (seriesL1_add_le _ _).trans (add_le_add le_rfl ih)

theorem seriesL1_prod_le {ι : Type*} (A : Finset ι) (f : ι → IntSeries) :
    seriesL1 (∏ i ∈ A, f i) ≤ ∏ i ∈ A, seriesL1 (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, seriesL1_one, le_refl]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (seriesL1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (seriesL1_nonneg _))

theorem geomSeries_difference (k : ℕ) :
    geomSeries k * firstDifference = 1 - (AddMonoidAlgebra.single 1 1 : IntSeries) ^ k := by
  exact geom_sum_mul_neg _ _

theorem geomSeries_L1_le (k : ℕ) : seriesL1 (geomSeries k) ≤ k := by
  apply (seriesL1_sum_le _ _).trans
  simp only [AddMonoidAlgebra.single_pow, one_pow, seriesL1_single, abs_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, le_refl]

theorem prouhetSeries_factor (s : ℕ) :
    prouhetSeries s = prouhetQuotient s * firstDifference ^ s := by
  unfold prouhetSeries prouhetQuotient
  simp_rw [← geomSeries_difference]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]

theorem prouhetQuotient_L1_le (s : ℕ) :
    seriesL1 (prouhetQuotient s) ≤ (2 : ℝ) ^ (s * s) := by
  calc
    _ ≤ ∏ v ∈ Finset.range s, seriesL1 (geomSeries (2 ^ v)) := seriesL1_prod_le _ _
    _ ≤ ∏ _v ∈ Finset.range s, ((2 : ℝ) ^ s) := by
      apply Finset.prod_le_prod
      · intro v _; exact seriesL1_nonneg _
      · intro v hv
        apply (geomSeries_L1_le _).trans
        push_cast
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact (Finset.mem_range.mp hv).le
    _ = _ := by simp only [Finset.prod_const, Finset.card_range, ← pow_mul]

/-- Prouhet smoothing in an explicit finite-trial form.  The constants
    2^(s*s) and (2 sqrt(2/(n+1)))^s are exp(O(s^2)) after assigning
    n = floor(g/(s+1)) trials to each group.  No Fourier theorem or
    probabilistic estimate is assumed. -/
theorem prouhet_binomial_coeff_bound (n s : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (series_coeff_mul_bound _ _ _ (binomial_difference_coeff_bound n s) z).trans
  exact mul_le_mul_of_nonneg_right (prouhetQuotient_L1_le s)
    (by positivity [binomialBound_nonneg n])

theorem prouhet_binomial_L2Sq_bound (n s : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [prouhetSeries_factor, mul_assoc]
  apply (seriesL2Sq_mul_le _ _).trans
  apply mul_le_mul
  · exact pow_le_pow_left₀ (seriesL1_nonneg _) (prouhetQuotient_L1_le s) 2
  · exact binomial_difference_L2Sq_bound n s
  · exact seriesL2Sq_nonneg _
  · positivity

/-- Arbitrary trial counts are obtained by convolving with the independent
    unused trials; this cannot enlarge the coefficient or squared-L2 bounds. -/
theorem prouhet_binomial_coeff_bound_remainder (n s r : ℕ) (z : ℤ) :
    |(prouhetSeries s * fairSeries ((s + 1) * n + r)).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound n) ^ s * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  simpa only [fairSeries_L1, one_mul] using
    series_coeff_mul_bound (fairSeries r) (prouhetSeries s * fairSeries ((s + 1) * n))
      _ (prouhet_binomial_coeff_bound n s) z

theorem prouhet_binomial_L2Sq_bound_remainder (n s r : ℕ) :
    seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n + r)) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound n) ^ s) ^ 2 * binomialBound n) := by
  rw [fairSeries_add, ← mul_assoc, mul_comm (prouhetSeries s * _)]
  calc
    _ ≤ seriesL1 (fairSeries r) ^ 2 *
        seriesL2Sq (prouhetSeries s * fairSeries ((s + 1) * n)) := seriesL2Sq_mul_le _ _
    _ ≤ _ := by simpa only [fairSeries_L1, one_pow, one_mul] using
        prouhet_binomial_L2Sq_bound n s

theorem signed_binomial_smoothing (g s : ℕ) :
    (∀ z : ℤ, |(prouhetSeries s * fairSeries g).coeff z| ≤
      (2 : ℝ) ^ (s * s) * ((2 * binomialBound (g / (s + 1))) ^ s *
        binomialBound (g / (s + 1)))) ∧
    (seriesL2Sq (prouhetSeries s * fairSeries g) ≤
      ((2 : ℝ) ^ (s * s)) ^ 2 * (((2 * binomialBound (g / (s + 1))) ^ s) ^ 2 *
        binomialBound (g / (s + 1)))) := by
  have hg : (s + 1) * (g / (s + 1)) + g % (s + 1) = g := Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using prouhet_binomial_coeff_bound_remainder (g / (s + 1)) s
      (g % (s + 1)) z
  · simpa only [hg] using prouhet_binomial_L2Sq_bound_remainder (g / (s + 1)) s
      (g % (s + 1))

theorem binomialBound_quotient_le (g s : ℕ) :
    binomialBound (g / (s + 1)) ≤
      Real.sqrt (2 * ((s : ℝ) + 1) / ((g : ℝ) + 1)) := by
  apply Real.sqrt_le_sqrt
  have hn : g + 1 ≤ (g / (s + 1) + 1) * (s + 1) := by
    have hmod := Nat.mod_lt g (by omega : 0 < s + 1)
    have hdiv := Nat.div_add_mod g (s + 1)
    nlinarith
  have hnr : (g : ℝ) + 1 ≤ ((g / (s + 1) : ℕ) + (1 : ℝ)) * ((s : ℝ) + 1) := by
    exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (g / (s + 1) : ℕ) + 1)
    (by positivity : (0 : ℝ) < g + 1)).mpr
  nlinarith

theorem prouhetSeries_succ_coeff (s : ℕ) (z : ℤ) :
    (prouhetSeries (s + 1)).coeff z =
    (prouhetSeries s).coeff z - (prouhetSeries s).coeff (z - (2 ^ s : ℕ)) := by
  rw [prouhetSeries, Finset.prod_range_succ, mul_sub, mul_one]
  change (prouhetSeries s - prouhetSeries s *
    (AddMonoidAlgebra.single 1 1 : IntSeries) ^ (2 ^ s)).coeff z = _
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one,
    AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

/-- The exact generating polynomial from the manuscript has unit signed
    coefficients at every index 0,...,2^s-1, and no other coefficients. -/
theorem prouhetSeries_coeff_spec (s : ℕ) :
    (∀ z : ℤ, (z < 0 ∨ (2 ^ s : ℕ) ≤ z) → (prouhetSeries s).coeff z = 0) ∧
    (∀ z : ℤ, 0 ≤ z → z < (2 ^ s : ℕ) → |(prouhetSeries s).coeff z| = 1) := by
  induction s with
  | zero =>
    have hcoeff (z : ℤ) : (prouhetSeries 0).coeff z = if 0 = z then 1 else 0 := by
      change (AddMonoidAlgebra.single 0 (1 : ℝ)).coeff z = _
      exact Finsupp.single_apply
    constructor
    · intro z hz
      rw [hcoeff, ite_eq_right]
      norm_num only [pow_zero, Nat.cast_one] at hz
      omega
    · intro z h0 h1
      have hz : z = 0 := by norm_num only [pow_zero, Nat.cast_one] at h1; omega
      subst hz
      rw [hcoeff, ite_eq_left rfl, abs_one]
  | succ s ih =>
    have hp : (0 : ℤ) < (2 ^ s : ℕ) := by positivity
    have hd : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 * (2 ^ s : ℕ) := by push_cast; ring
    constructor
    · intro z hz
      rw [prouhetSeries_succ_coeff]
      rcases hz with hz | hz
      · rw [ih.1 z (Or.inl hz), ih.1 _ (Or.inl (by omega)), sub_zero]
      · rw [hd] at hz
        rw [ih.1 z (Or.inr (by omega)), ih.1 _ (Or.inr (by omega)), sub_zero]
    · intro z h0 h1
      rw [hd] at h1
      rw [prouhetSeries_succ_coeff]
      by_cases hz : z < (2 ^ s : ℕ)
      · rw [ih.1 (z - (2 ^ s : ℕ)) (Or.inl (by omega)), sub_zero]
        exact ih.2 z h0 hz
      · rw [ih.1 z (Or.inr (by omega)), zero_sub, abs_neg]
        exact ih.2 _ (by omega) (by omega)


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Kernels

Constrained rank-gap sums, correlated anchor kernels, window kernels, lattice Laplace sums, and geometric degree bounds.
-/

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction
theorem fairSeries_total (n : ℕ) : ∑' z : ℤ, (fairSeries n).coeff z = 1 := by
  have h := fairSeries_L1 n
  unfold seriesL1 at h
  simpa only [abs_of_nonneg (fairSeries_nonneg n _)] using h

theorem fairSeries_sum_finite_le_one (n : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, (fairSeries n).coeff (c-z) ≤ 1 := by
  have hs : Summable (fun z : ℤ => (fairSeries n).coeff (c-z)) := by
    exact (Equiv.subLeft c).summable_iff.mpr (series_summable (fairSeries n) id rfl)
  have hh : (∑' z : ℤ, (fairSeries n).coeff (c-z)) = 1 := by
    simpa using ((Equiv.subLeft c).tsum_eq (fun z => (fairSeries n).coeff z)).trans
      (fairSeries_total n)
  rw [← hh]
  exact Summable.sum_le_tsum A (fun _ _ => fairSeries_nonneg n _) hs

theorem windowKernel_nonneg (n L : ℕ) (z : ℤ) : 0 ≤ windowKernel n L z :=
  Finset.sum_nonneg (fun _ _ => fairSeries_nonneg n _)

theorem windowKernel_sup (n L : ℕ) (z : ℤ) :
    windowKernel n L z ≤ L*binomialBound n := by
  calc
    _ ≤ ∑ _a ∈ Finset.range L, binomialBound n := by
      apply Finset.sum_le_sum
      intro a _
      exact (le_abs_self _).trans (fairSeries_coeff_bound n _)
    _ = _ := by simp

theorem windowKernel_sum (n L : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, windowKernel n L (z-c) ≤ L := by
  unfold windowKernel
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _a ∈ Finset.range L, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [show ∀ z : ℤ, (a:ℤ)-(z-c)=(a:ℤ)+c-z from fun z => by omega]
        using fairSeries_sum_finite_le_one n A ((a:ℤ)+c)
    _ = _ := by simp

theorem windowKernel_energy (n L : ℕ) (A : Finset ℤ) (c : ℤ) :
    ∑ z ∈ A, windowKernel n L (z-c)^2 ≤ L^2*binomialBound n := by
  calc
    _ ≤ ∑ z ∈ A, windowKernel n L (z-c)*(L*binomialBound n) := by
      apply Finset.sum_le_sum
      intro z _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left
        (windowKernel_sup n L (z-c)) (windowKernel_nonneg n L (z-c))
    _ = (∑ z ∈ A, windowKernel n L (z-c))*(L*binomialBound n) := by rw [Finset.sum_mul]
    _ ≤ L*(L*binomialBound n) := mul_le_mul_of_nonneg_right
      (windowKernel_sum n L A c) (by positivity [binomialBound_nonneg n])
    _ = _ := by ring

theorem windowKernel_average (g n L : ℕ) (z : ℤ) :
    (∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v * windowKernel n L (z+v)) =
      windowKernel (g+n) L z := by
  unfold windowKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [fairSeries_add, AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro v _
  congr 2
  omega

theorem jointWindowKernel_nonneg (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) :
    0 ≤ jointWindowKernel g n₁ n₂ L z₁ z₂ := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (mul_nonneg (fairSeries_nonneg g v) (windowKernel_nonneg n₁ L _))
    (windowKernel_nonneg n₂ L _)

theorem jointWindowKernel_sup (g n₁ n₂ L : ℕ) (z₁ z₂ : ℤ) :
    jointWindowKernel g n₁ n₂ L z₁ z₂ ≤ L^2*binomialBound g*binomialBound n₂ := by
  have hbound : binomialBound (g+n₁) ≤ binomialBound g := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    simp only [Nat.cast_add]; linarith [show (0:ℝ) ≤ n₁ by positivity]
  calc
    _ ≤ ∑ v ∈ (fairSeries g).coeff.support,
        (fairSeries g).coeff v * windowKernel n₁ L (z₁+v) * (L*binomialBound n₂) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (windowKernel_sup n₂ L _) (mul_nonneg
        (fairSeries_nonneg g v) (windowKernel_nonneg n₁ L _))
    _ = windowKernel (g+n₁) L z₁ * (L*binomialBound n₂) := by
      rw [← Finset.sum_mul, windowKernel_average]
    _ ≤ (L*binomialBound g)*(L*binomialBound n₂) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (binomialBound_nonneg n₂))
      exact (windowKernel_sup (g+n₁) L z₁).trans
        (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ = _ := by ring

theorem jointWindowKernel_sum (g n₁ n₂ L : ℕ) (A B : Finset ℤ) (c₁ c₂ : ℤ) :
    ∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂) ≤ L^2 := by
  unfold jointWindowKernel
  simp_rw [Finset.sum_comm (s := B)]
  rw [Finset.sum_comm]
  calc
    _ = ∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v *
        (∑ z₁ ∈ A, windowKernel n₁ L ((z₁-c₁)+v)) *
        (∑ z₂ ∈ B, windowKernel n₂ L ((z₂-c₂)+v)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v * (L*L) := by
      apply Finset.sum_le_sum
      intro v _
      have h1 : (∑ z₁ ∈ A, windowKernel n₁ L ((z₁-c₁)+v)) ≤ L := by
        simpa only [show ∀ z : ℤ, (z-c₁)+v = z-(c₁-v) from fun z => by omega]
          using windowKernel_sum n₁ L A (c₁-v)
      have h2 : (∑ z₂ ∈ B, windowKernel n₂ L ((z₂-c₂)+v)) ≤ L := by
        simpa only [show ∀ z : ℤ, (z-c₂)+v = z-(c₂-v) from fun z => by omega]
          using windowKernel_sum n₂ L B (c₂-v)
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (fairSeries_nonneg g v)
      exact mul_le_mul h1 h2 (Finset.sum_nonneg (fun z _ => windowKernel_nonneg n₂ L _)) (by positivity)
    _ = L^2 := by
      rw [← Finset.sum_mul]
      have ht : (∑ v ∈ (fairSeries g).coeff.support, (fairSeries g).coeff v) = 1 := by
        have h := fairSeries_L1 g
        rw [seriesL1_eq_sum] at h
        simpa only [abs_of_nonneg (fairSeries_nonneg g _)] using h
      rw [ht]; ring

theorem jointWindowKernel_energy (g n₁ n₂ L : ℕ) (A B : Finset ℤ) (c₁ c₂ : ℤ) :
    ∑ z₁ ∈ A, ∑ z₂ ∈ B, (jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂))^2 ≤
      L^4*binomialBound g*binomialBound n₂ := by
  calc
    _ ≤ ∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂) *
        (L^2*binomialBound g*binomialBound n₂) := by
      apply Finset.sum_le_sum
      intro z₁ _
      apply Finset.sum_le_sum
      intro z₂ _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left
        (jointWindowKernel_sup g n₁ n₂ L _ _) (jointWindowKernel_nonneg g n₁ n₂ L _ _)
    _ = (∑ z₁ ∈ A, ∑ z₂ ∈ B, jointWindowKernel g n₁ n₂ L (z₁-c₁) (z₂-c₂)) *
        (L^2*binomialBound g*binomialBound n₂) := by simp_rw [Finset.sum_mul]
    _ ≤ L^2*(L^2*binomialBound g*binomialBound n₂) := mul_le_mul_of_nonneg_right
      (jointWindowKernel_sum g n₁ n₂ L A B c₁ c₂)
      (mul_nonneg (mul_nonneg (by positivity) (binomialBound_nonneg g)) (binomialBound_nonneg n₂))
    _ = _ := by ring
end TraceReconstruction

open Filter
open scoped Topology


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ranks

Retained subsets, conditional rank experiments, tagged gaps, period geometry, Gaussian Schur estimates, and uniform square sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


namespace TraceReconstruction

/-- Summing nonnegative kernels over actual profiles may drop any remaining constraints. -/
theorem sum_injective_profile_le {α β : Type*} [Fintype α] [Fintype β]
    (profile : α → β) (hinj : Function.Injective profile)
    (P : β → Prop) [DecidablePred P] (hp : ∀ a, P (profile a))
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (profile a)) ≤ ∑ b, if P b then f b else 0 := by
  classical
  let S := Finset.univ.image profile
  have hs : ∀ b ∈ S, P b := by
    intro b hb
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hb
    exact hp a
  calc
    _ = ∑ b ∈ S, f b := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => hinj h)
    _ = ∑ b ∈ S, if P b then f b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [ite_eq_left (hs b hb)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro b _ _
      split_ifs
      · exact hf b
      · rfl)

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section



noncomputable section


noncomputable section

open Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section


noncomputable section


noncomputable section


noncomputable section
open scoped Classical


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem prouhet_motif_value (s : ℕ) (z : ℤ) :
    IsMotifValue (motifIndicator s z) ((prouhetSeries s).coeff z) := by
  by_cases hz : 0 ≤ z ∧ z < (2^s : ℕ)
  · right
    refine ⟨by simp only [motifIndicator,ite_eq_left hz], ?_⟩
    have hv := (prouhetSeries_coeff_spec s).2 z hz.1 hz.2
    exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv
  · left
    refine ⟨by simp only [motifIndicator,ite_eq_right hz], ?_⟩
    apply (prouhetSeries_coeff_spec s).1 z
    omega

end TraceReconstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialDensity

Defect monomials, orthogonality, normalized initial densities, and common mass.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section

noncomputable section

namespace TraceReconstruction
open FiniteLaw

/-- Exact decomposition of the coefficient energy by its degree. -/
theorem multilinearEnergy_degrees {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R = ∑ r ∈ Finset.range (n+1),
      R^(2*r) * ∑ σ : Fin n → Bool, if monomialDegree σ = r then A σ^2 else 0 := by
  classical
  unfold multilinearEnergy
  simp_rw [monomial_weight]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have hd : monomialDegree σ < n+1 := by
    have h := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => σ i = true)
    simpa [monomialDegree] using Nat.lt_succ_of_le h
  rw [Finset.sum_eq_single (monomialDegree σ)]
  · simp [mul_comm]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp [Finset.mem_range,hd]

/-- A zero-degree selection is precisely the empty selection. -/
theorem monomialDegree_eq_zero_iff {n : ℕ} (σ : Fin n → Bool) :
    monomialDegree σ = 0 ↔ σ = fun _ => false := by
  classical
  constructor
  · intro h
    have he : Finset.univ.filter (fun i => σ i = true) = ∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : σ i ≠ true := by
      intro hi
      have : i ∈ Finset.univ.filter (fun j => σ j = true) := by simp [hi]
      rw [he] at this
      exact Finset.notMem_empty i this
    exact Bool.eq_false_iff.mpr hn
  · rintro rfl
    simp [monomialDegree]

end TraceReconstruction

end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem geomSeries_coeff (k : ℕ) (z : ℤ) :
    (geomSeries k).coeff z = if 0 ≤ z ∧ z < k then 1 else 0 := by
  unfold geomSeries
  simp only [AddMonoidAlgebra.single_pow,one_pow,nsmul_eq_mul,mul_one,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases hz : 0 ≤ z ∧ z < k
  · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
    rw [ite_eq_left hz,Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      exact ite_eq_right (by exact_mod_cast hb)
    · intro ha
      have ha' : a < k := by exact_mod_cast hz.2
      exact (ha (Finset.mem_range.mpr ha')).elim
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro a ha
    apply ite_eq_right
    intro haz
    subst z
    exact hz ⟨by positivity,by exact_mod_cast Finset.mem_range.mp ha⟩

end TraceReconstruction


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialMoments

Initial coefficient tails, primitive conditioning, mark-list oracle densities, pure norm estimates, and moment energies.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
noncomputable section
noncomputable section


noncomputable section
noncomputable section



noncomputable section



noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem multilinear_scale {α : Type*} {n : ℕ} (A : (Fin n → Bool) → ℝ)
    (Z : α → ℝ) {L : ℝ} (hL : L≠0) (x : Fin n → α) :
    multilinear (scaleCoefficient A L) (fun a => Z a/L) x=multilinear A Z x := by
  unfold multilinear scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  exact mul_div_cancel₀ _ hL

theorem multilinearEnergy_scale {n : ℕ} (A : (Fin n → Bool) → ℝ) (L R : ℝ) :
    multilinearEnergy (scaleCoefficient A L) R=multilinearEnergy A (R*L) := by
  unfold multilinearEnergy scaleCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_pow,← Finset.prod_pow,mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases σ i <;> simp
  ring

/-- The exact norm-of-input factor in the conditional leaf expansion. -/
theorem multilinear_moment_scaled {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => |multilinear A Z x|^(2*k)) ≤
      (multilinearEnergy A ((6*(2*k:ℕ):ℝ)*L))^k := by
  have hcenter' : P.expect (fun a => Z a/L)=0 := by
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    change P.expect Z / L = 0
    rw [hcenter,zero_div]
  have hmoment' : P.expect (fun a => |Z a/L|^(2*k))≤1 := by
    simp_rw [abs_div,abs_of_pos hL,div_pow]
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    apply (div_le_one (by positivity)).mpr hMoment
  have H := multilinear_even_moment P (fun a => Z a/L) k hk hcenter' hmoment' n (scaleCoefficient A L)
  simp_rw [multilinear_scale A Z hL.ne',multilinearEnergy_scale] at H
  simpa only [pow_mul,sq_abs] using H

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem closeLabels_card (A : Finset ℤ) (L : ℕ) (a : ℤ) :
    (closeLabels A L a).card ≤ 2*L := by
  have hsub : closeLabels A L a ⊆ Finset.Ioo (a-(L:ℤ)) (a+(L:ℤ)) := by
    intro c hc
    have h := abs_lt.mp ((Finset.mem_filter.mp hc).2)
    exact Finset.mem_Ioo.mpr ⟨by omega,by omega⟩
  have H := Finset.card_le_card hsub
  rw [Int.card_Ioo] at H
  omega

/-- Root anchor and close-child energy. This keeps the actual labels finite,
including any additional source plateau cutoff. -/
theorem root_anchor_energy (n L : ℕ) (A B : Finset ℤ) (c : ℤ) :
    (∑ a∈A, ∑ _d∈closeLabels B L a, windowKernel n L (a-c)^2) ≤
      2*L^3*binomialBound n := by
  calc
    _ ≤ ∑a∈A, (2*L:ℝ)*windowKernel n L (a-c)^2 := by
      apply Finset.sum_le_sum
      intro a _
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast closeLabels_card B L a) (sq_nonneg _)
    _ = (2*L:ℝ)*(∑a∈A,windowKernel n L (a-c)^2) := by rw [Finset.mul_sum]
    _ ≤ (2*L:ℝ)*(L^2*binomialBound n) :=
      mul_le_mul_of_nonneg_left (windowKernel_energy n L A c) (by positivity)
    _ = _ := by ring

/-- The shared global jitter stays in the joint kernel until after squaring.
The two close labels cost only (2L)^2, uniformly in parent labels. -/
theorem sibling_anchor_energy (g n₁ n₂ L : ℕ) (A B C D : Finset ℤ) (c₁ c₂ : ℤ) :
    (∑ a∈A, ∑ b∈B, ∑ _c∈closeLabels C L a, ∑ _d∈closeLabels D L b,
      jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2) ≤
      4*L^6*binomialBound g*binomialBound n₂ := by
  calc
    _ ≤ ∑a∈A, ∑b∈B, (2*L:ℝ)^2*jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((closeLabels C L a).card:ℝ)≤2*L := by exact_mod_cast closeLabels_card C L a
      have hd : ((closeLabels D L b).card:ℝ)≤2*L := by exact_mod_cast closeLabels_card D L b
      have hm := mul_le_mul hc hd (by positivity) (by positivity : (0:ℝ)≤2*L)
      rw [mul_assoc] at hm
      nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg (jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)))]
    _ = (2*L:ℝ)^2*(∑a∈A,∑b∈B,jointWindowKernel g n₁ n₂ L (a-c₁) (b-c₂)^2) := by
      simp_rw [Finset.mul_sum]
    _ ≤ (2*L:ℝ)^2*(L^4*binomialBound g*binomialBound n₂) :=
      mul_le_mul_of_nonneg_left (jointWindowKernel_energy g n₁ n₂ L A B c₁ c₂) (by positivity)
    _ = _ := by ring

theorem binaryTreeBudget_nonneg (C : ℕ → ℝ) (hC : ∀n,0≤C n) (n : ℕ) :
    0≤binaryTreeBudget C n := by
  cases n with
  | zero => norm_num [binaryTreeBudget]
  | succ n => exact mul_nonneg (hC n) (sq_nonneg _)

end TraceReconstruction
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_InitialOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# InitialOverlap

Literal periods, count overlap, initial low/high energies, genuine densities, and centered moment bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section



/-! From the actual displaced period words to their conditional oracle
moments.  The coefficient bounds are the rank kernels,
not assumptions on an abstract pair. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem degree_square_sub_le {n : ℕ} (A B : (Fin n → Bool) → ℝ) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then (A σ-B σ)^2 else 0)  ≤ 
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0)+
    2*(∑σ : Fin n → Bool, if monomialDegree σ=r then B σ^2 else 0) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  split_ifs <;> nlinarith [sq_nonneg (A σ+B σ)]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A finite tail is no larger than the full geometric tail. -/
theorem finite_geometric_tail_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (N R : ℕ) :
    (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) ≤ a^R/(1-a) := by
  have ht : HasSum (fun n : ℕ => a^(n+R)) (a^R/(1-a)) := by
    simpa only [pow_add, mul_comm, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one ha ha1).mul_left (a^R)
  have hsum : (∑r ∈ Finset.range N, if R ≤ r then a^r else 0) =
      ∑r ∈ (Finset.range N).filter (R ≤ ·), a^r := by
    rw [Finset.sum_filter]
  rw [hsum]
  calc
    _ = ∑r ∈ ((Finset.range N).filter (R ≤ ·)).image (fun r => r-R), a^(r+R) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [Nat.sub_add_cancel (Finset.mem_filter.mp hr).2]
      · intro r hr s hs h
        dsimp only at h
        have hrR := (Finset.mem_filter.mp hr).2
        have hsR := (Finset.mem_filter.mp hs).2
        omega
    _ ≤ _ := by
      rw [←ht.tsum_eq]
      exact ht.summable.sum_le_tsum _ (fun _ _ => by positivity)

/-- Splitting the exact homogeneous expansion, not a surrogate polynomial. -/
theorem multilinearEnergy_low_high {n R : ℕ} (A : (Fin n → Bool) → ℝ)
    (w a K : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (ha1 : a < 1) (hK : 0 ≤ K)
    (L : ℕ → ℝ)
    (hlow : ∀r < R, (∑σ : Fin n → Bool, if monomialDegree σ=r then A σ^2 else 0) ≤ L r)
    (hhigh : ∀r, R ≤ r → w^(2*r)*(∑σ : Fin n → Bool,
      if monomialDegree σ=r then A σ^2 else 0) ≤ K*a^r)
    (hL : ∀r, 0 ≤ L r) :
    multilinearEnergy A w ≤ (∑r ∈ Finset.range R, w^(2*r)*L r)+K*a^R/(1-a) := by
  rw [multilinearEnergy_degrees]
  calc
    _ ≤ ∑r ∈ Finset.range (n+1),
        ((if r < R then w^(2*r)*L r else 0)+(if R ≤ r then K*a^r else 0)) := by
      apply Finset.sum_le_sum
      intro r _
      by_cases h : r < R
      · simp only [ite_eq_left h,ite_eq_right (show ¬R ≤ r by omega),add_zero]
        exact mul_le_mul_of_nonneg_left (hlow r h) (by positivity)
      · simp only [ite_eq_right h,ite_eq_left (show R ≤ r by omega),zero_add]
        exact hhigh r (by omega)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      apply add_le_add
      · rw [←Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2)
          (fun r _ _ => mul_nonneg (by positivity) (hL r))
      · have he : (∑r ∈ Finset.range (n+1), if R ≤ r then K*a^r else 0)=
            K*∑r ∈ Finset.range (n+1), if R ≤ r then a^r else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          split_ifs <;> ring
        rw [he,mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (finite_geometric_tail_le ha ha1 _ _) hK

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem multilinear_sub {α : Type*} {l : ℕ} (A B : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (fun σ => A σ-B σ) Z x = multilinear A Z x-multilinear B Z x := by
  simp only [multilinear,sub_mul,Finset.sum_sub_distrib]

theorem nonconstant_multilinear {α : Type*} {l : ℕ} (A : (Fin l → Bool) → ℝ)
    (Z : α → ℝ) (x : Fin l → α) :
    multilinear (nonconstantCoefficient A) Z x=multilinear A Z x-A (fun _ => false) := by
  have he : ∀σ, nonconstantCoefficient A σ=A σ-(if σ=(fun _ => false) then A σ else 0) := by
    intro σ
    by_cases h : σ=(fun _ => false) <;> simp [nonconstantCoefficient,h]
  rw [show nonconstantCoefficient A = (fun σ => A σ-(if σ=(fun _ => false) then A σ else 0)) from funext he, multilinear_sub]
  congr 1
  simp [multilinear,ite_mul]

end TraceReconstruction


end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LeafOracle
attribute [-instance] _root_.OAI.TraceReconstruction.OccupiedParityTree.edgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraLeafEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.labelsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem motifChildSign_isSign (s : ℕ) (X : ℤ) (h : ℕ) {τ : ℝ} (hτ : IsTypeSign τ) :
    IsTypeSign (motifChildSign s X h τ) :=
  motif_child_sign (prouhet_motif_value s ((h:ℤ)-X)) hτ

theorem motifChildSign_negative_active (s : ℕ) (X : ℤ) (h : ℕ) (τ : ℝ)
    (ht : motifChildSign s X h τ= -1) : 0 ≤ (h:ℤ)-X ∧ (h:ℤ)-X<(2^s:ℕ) := by
  by_contra hn
  have hz := (prouhetSeries_coeff_spec s).1 ((h:ℤ)-X) (by omega)
  simp only [motifChildSign,motifIndicator,ite_eq_right hn,hz,zero_mul,sub_zero,add_zero] at ht
  norm_num at ht

theorem motif_negative_count (s N : ℕ) (X : ℤ) (τ : ℝ) :
    (Finset.univ.filter (fun i : Fin N => motifChildSign s X i.val τ= -1)).card ≤ 2^s := by
  have H := Finset.card_le_card_of_injOn
    (s:=Finset.univ.filter (fun i : Fin N => motifChildSign s X i.val τ= -1))
    (t:=Finset.range (2^s)) (fun i : Fin N => ((i.val:ℤ)-X).toNat) ?_ ?_
  · simpa using H
  · intro i hi
    have h := motifChildSign_negative_active s X i.val τ (Finset.mem_filter.mp hi).2
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro i hi j hj he
    have h := motifChildSign_negative_active s X i.val τ (Finset.mem_filter.mp hi).2
    have h' := motifChildSign_negative_active s X j.val τ (Finset.mem_filter.mp hj).2
    apply Fin.ext
    dsimp only at he
    omega

theorem windowMinusCount_succ (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) :
    windowMinusCount T s X (b+1) path τ =
      ∑i : Fin (T b), windowMinusCount T s X b (path++[i.val])
        (motifChildSign s (X path) i.val τ) := by
  unfold windowMinusCount
  change (∑v : Fin (T b) × WindowLeaf T b, _) = _
  rw [Fintype.sum_prod_type]
  rfl

/-- Source the block layout high-degree budget, bottom motif length times all
upper window counts. It holds for every latent realization, typical or not. -/
theorem windowMinusCount_bound (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) :
    windowMinusCount T s X (b+1) path τ ≤
      2^s * ∏j∈Finset.range b, T (j+1) := by
  induction b generalizing path τ with
  | zero =>
    rw [windowMinusCount_succ]
    change (∑i : Fin (T 0), ∑v : Fin 1,
      if motifChildSign s (X path) i.val τ= -1 then (1:ℕ) else 0) ≤ _
    simp only [Fin.sum_univ_one,Finset.range_zero,Finset.prod_empty,mul_one]
    simpa only [Finset.card_filter] using motif_negative_count s (T 0) (X path) τ
  | succ b ih =>
    rw [windowMinusCount_succ]
    calc
      _ ≤ ∑i : Fin (T (b+1)), 2^s*∏j∈Finset.range b,T (j+1) :=
        Finset.sum_le_sum (fun _ _ => ih _ _)
      _ = _ := by simp [Finset.prod_range_succ]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem boolSupport_injective {n : ℕ} : Function.Injective (boolSupport (n:=n)) := by
  intro θ φ h
  funext i
  have hi : (θ i=true) ↔ (φ i=true) := by
    simpa [boolSupport] using Finset.ext_iff.mp h i
  cases hθ : θ i <;> cases hφ : φ i <;> simp_all

theorem selectionCoefficient_eq_support {n : ℕ} (θ σ : Fin n → Bool) :
    selectionCoefficient θ σ = if boolSupport σ ⊆ boolSupport θ then 1 else 0 := by
  by_cases h : boolSupport σ ⊆ boolSupport θ
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    cases hs : σ i
    · simp
    · have ht : θ i=true := by simpa [boolSupport] using h (by simp [boolSupport,hs])
      simp [ht]
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp h
    have hs : σ i=true := by simpa [boolSupport] using hi
    have ht : θ i=false := by simpa [boolSupport] using hni
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hs,ht]

/-- Uniform cardinality bound for the actual selected monomials of a sparse
0/1 coefficient vector; mixing does not add a squared-cardinality loss. -/
theorem selection_degree_sum_le {n : ℕ} (θ : Fin n → Bool) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then selectionCoefficient θ σ else 0) ≤
      ((monomialDegree θ).choose r:ℝ) := by
  have hc : (Finset.univ.filter (fun σ : Fin n → Bool =>
      monomialDegree σ=r ∧ boolSupport σ ⊆ boolSupport θ)).card ≤
        ((boolSupport θ).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn boolSupport
    · intro σ hσ
      rcases (Finset.mem_filter.mp hσ).2 with ⟨hd,hs⟩
      exact Finset.mem_powersetCard.mpr ⟨hs,hd⟩
    · exact boolSupport_injective.injOn
  rw [Finset.card_powersetCard] at hc
  have he : (∑σ : Fin n → Bool, if monomialDegree σ=r then selectionCoefficient θ σ else 0) =
      ((Finset.univ.filter (fun σ : Fin n → Bool =>
        monomialDegree σ=r ∧ boolSupport σ ⊆ boolSupport θ)).card:ℝ) := by
    simp_rw [selectionCoefficient_eq_support,←ite_and]
    exact Finset.sum_boole _ _
  rw [he]
  exact_mod_cast hc

theorem averaged_sparse_degree {Ω : Type*} [Fintype Ω] {n A : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (hA : ∀ω, monomialDegree (θ ω) ≤ A) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then averagedCoefficient R θ σ^2 else 0) ≤
      (A.choose r:ℝ) := by
  calc
    _ ≤ ∑σ : Fin n → Bool, if monomialDegree σ=r then averagedCoefficient R θ σ else 0 := by
      apply Finset.sum_le_sum
      intro σ _
      split_ifs
      · have hc := coefficient_nonneg R θ σ
        have h1 := coefficient_le_one R θ σ
        nlinarith [mul_nonneg hc (sub_nonneg.mpr h1)]
      · rfl
    _ = ∑ω, R.mass ω * ∑σ : Fin n → Bool,
        if monomialDegree σ=r then selectionCoefficient (θ ω) σ else 0 := by
      unfold averagedCoefficient FiniteLaw.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : monomialDegree σ=r <;> simp [h]
    _ ≤ ∑ω, R.mass ω * (A.choose r:ℝ) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (R.nonneg ω)
      exact (selection_degree_sum_le (θ ω) r).trans (by
        exact_mod_cast Nat.choose_le_choose r (hA ω))
    _ = _ := by rw [←Finset.sum_mul,R.total,one_mul]

/-- Genuine sparse complete-tree leaf count in the exact Fin indexing used
by the independent-product reference law. -/
theorem windowFinType_degree (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (τ : ℝ) :
    monomialDegree (windowFinType T s X b τ) = windowMinusCount T s X b [] τ := by
  have h := Equiv.sum_comp (Fintype.equivFin (WindowLeaf T b)).symm
    (fun v => if windowLeafSign T s X b [] τ v= -1 then (1:ℕ) else 0)
  simpa only [monomialDegree,Finset.card_filter,windowFinType,windowLeafType,
    decide_eq_true_eq,windowMinusCount] using h

theorem degreeTail_degree {n r k : ℕ} (A : (Fin n → Bool) → ℝ) :
    (∑σ, if monomialDegree σ=r then degreeTail A k σ^2 else 0) =
      if k ≤ r then ∑σ, if monomialDegree σ=r then A σ^2 else 0 else 0 := by
  by_cases h : k ≤ r
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : monomialDegree σ=r <;> simp [degreeTail,he,h]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro σ _
    by_cases he : monomialDegree σ=r <;> simp [degreeTail,he,h]

/-- Geometric high-degree energy of an actual mixed sparse leaf law. -/
theorem averaged_sparse_tail_energy {Ω : Type*} [Fintype Ω] {n A₀ : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (hA : ∀ω, monomialDegree (θ ω) ≤ A₀) (k : ℕ) {w : ℝ}
    (hw : 0 ≤ w) (ha : w^2*A₀ < 1) :
    multilinearEnergy (degreeTail (averagedCoefficient R θ) k) w ≤
      (w^2*A₀)^k/(1-w^2*A₀) := by
  have H := multilinearEnergy_low_high (R:=k)
    (degreeTail (averagedCoefficient R θ) k) w (w^2*A₀) 1 hw (by positivity) ha
    (by norm_num) (fun _ => 0) ?_ ?_ (fun _ => le_rfl)
  · simpa using H
  · intro r hr
    rw [degreeTail_degree,ite_eq_right (by omega)]
  · intro r hr
    rw [degreeTail_degree,ite_eq_left hr,one_mul]
    have hc : (A₀.choose r:ℝ) ≤ (A₀:ℝ)^r := by exact_mod_cast Nat.choose_le_pow A₀ r
    calc
      _ ≤ w^(2*r)*(A₀:ℝ)^r := mul_le_mul_of_nonneg_left
        ((averaged_sparse_degree R θ hA r).trans hc) (by positivity)
      _ = _ := by rw [pow_mul,mul_pow]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem occupiedWindowShape_admissible (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    (occupiedWindowShape T s X b path S).Admissible := by
  induction b generalizing path with
  | zero => exact fun _ => prouhet_motif_value s _
  | succ b ih => exact ⟨fun _ => prouhet_motif_value s _, fun _ => ih _ _⟩

/-- The literal coefficient product equals the evaluation of its occupied
shape; this is before any averaging or parity cancellation. -/
theorem occupiedWindowShape_eval (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) (τ : ℝ) :
    (occupiedWindowShape T s X b path S).eval τ =
      ∏v∈S, (1-windowLeafSign T s X (b+1) path τ v)/2 := by
  induction b generalizing path τ with
  | zero =>
    change (∏i : Fin S.card, _) = _
    refine (selected_prod_index S (fun v : Fin (T 0) × Fin 1 =>
      (motifIndicator s ((v.1.val:ℤ)-X path) -
        (prouhetSeries s).coeff ((v.1.val:ℤ)-X path)*τ)/2)).trans ?_
    apply Finset.prod_congr rfl
    intro v hv
    simp only [windowLeafSign,motifChildSign]
    ring
  | succ b ih =>
    change (∏i : Fin (selectedChildren S).card, _) = _
    simp_rw [ih]
    refine (selected_prod_index (selectedChildren S) (fun h : Fin (T (b+1)) =>
      ∏v∈selectedChildLeaves S h,
        (1-windowLeafSign T s X (b+1) (path++[h.val])
          (motifChildSign s (X path) h.val τ) v)/2)).trans ?_
    exact selected_prod_children S (fun v =>
      (1-windowLeafSign T s X (b+1+1) path τ v)/2)

/-- Exact source parity formula for the actual selected leaves, using a
single role index independent of the latent map. No fit conditioning. -/
theorem occupiedWindow_difference (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    (∏v∈S, (1-windowLeafSign T s X (b+1) path 1 v)/2) -
      (∏v∈S, (1-windowLeafSign T s X (b+1) path (-1) v)/2) =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then occupiedWindowWeight T s X b path S a else 0 := by
  rw [←occupiedWindowShape_eval,←occupiedWindowShape_eval,
    CoefficientShape.difference_expansion _ (occupiedWindowShape_admissible T s X b path S)]
  congr 1
  rw [←(occupiedWindowChoiceEquiv T s X b path S).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [occupiedWindowTerm_eq]
  rfl

/-- Averaging the complete exact expansion keeps all correlations of the
common hidden map. The indicator of an odd root is deterministic. -/
theorem occupiedWindow_averaged_difference {Ω : Type*} [Fintype Ω]
    (R : FiniteLaw Ω) (T : ℕ → ℕ) (s : ℕ) (X : Ω → List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    R.expect (fun ω => ∏v∈S, (1-windowLeafSign T s (X ω) (b+1) path 1 v)/2) -
      R.expect (fun ω => ∏v∈S, (1-windowLeafSign T s (X ω) (b+1) path (-1) v)/2) =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then
          R.expect (fun ω => occupiedWindowWeight T s (X ω) b path S a) else 0 := by
  unfold expect
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub,occupiedWindow_difference,mul_left_comm (R.mass _) 2,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (occupiedWindowTerm T b S a).isOdd <;> simp [h]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The actual local signed motif averaged over posterior orientations is
exactly a translated smoothed Prouhet polynomial. -/
theorem posterior_signed_motif {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      (prouhetSeries s).coeff (z+∑i,(bitIndex (b i):ℤ))) =
      (prouhetSeries s * fairSeries (∑i,hiddenTrial (d i))).coeff
        (z+(∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i))) := by
  rw [posterior_count_average_reflected d (fun a => (prouhetSeries s).coeff (z+a)),
    fairSeries_sum,Finset.mul_sum,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_comm]
  congr 2
  omega

/-- Singleton smoothing for literal hidden orientation bits. Other mechanisms
can now be conditioned on without changing this bound. -/
theorem posterior_signed_motif_bound {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    |∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      (prouhetSeries s).coeff (z+∑i,(bitIndex (b i):ℤ))| ≤
      (2:ℝ)^(s*s)*((2*binomialBound ((∑i,hiddenTrial (d i))/(s+1)))^s *
        binomialBound ((∑i,hiddenTrial (d i))/(s+1))) := by
  rw [posterior_signed_motif]
  exact (signed_binomial_smoothing _ s).1 _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The literal unsigned window evaluated at an affine fair-binomial shift. -/
theorem windowKernel_binomial (n L : ℕ) (z : ℤ) :
    windowKernel n L z =
      ∑k∈Finset.range (n+1), fairBinomial n k *
        (if 0 ≤ z+(k:ℤ) ∧ z+(k:ℤ)<L then (1:ℝ) else 0) := by
  unfold windowKernel
  simp_rw [fairSeries_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [←geomSeries_coeff,geomSeries]
  simp only [AddMonoidAlgebra.single_pow,one_pow,nsmul_eq_mul,mul_one,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : (a:ℤ)=z+k
  · have h' : (k:ℤ)=(a:ℤ)-z := by omega
    simp only [ite_eq_left h,ite_eq_left h',mul_one]
  · have h' : (k:ℤ)≠(a:ℤ)-z := by omega
    simp only [ite_eq_right h,ite_eq_right h',mul_zero]

/-- Exact local anchor kernel for the actual posterior bits, with the known
visible contribution retained as a translation. -/
theorem posterior_unsigned_motif {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      motifIndicator s (z+∑i,(bitIndex (b i):ℤ))) =
      windowKernel (∑i,hiddenTrial (d i)) (2^s) (z+∑i,(visibleOnes (d i):ℤ)) := by
  rw [posterior_count_average d (fun a => motifIndicator s (z+a)),windowKernel_binomial]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [motifIndicator,add_assoc]

/-- The finite-series functional form of the posterior count identity. -/
theorem posterior_count_support {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i))*F (∑i,(bitIndex (b i):ℤ))) =
    ∑v∈(fairSeries (∑i,hiddenTrial (d i))).coeff.support,
      (fairSeries (∑i,hiddenTrial (d i))).coeff v * F ((∑i,(visibleOnes (d i):ℤ))+v) := by
  rw [posterior_count_average]
  have H := congrArg (fun p : IntSeries =>
    Finsupp.linearCombination ℝ (fun v => F ((∑i,(visibleOnes (d i):ℤ))+v)) p.coeff)
    (fairSeries_sum (∑i,hiddenTrial (d i)))
  simp only [AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H.symm

theorem posteriorJointAnchors_eq {ιg ι₁ ι₂ : Type*} [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (z₁ z₂ : ℤ) :
    posteriorJointAnchors dg d₁ d₂ s z₁ z₂ =
    jointWindowKernel (∑i,hiddenTrial (dg i)) (∑i,hiddenTrial (d₁ i))
      (∑i,hiddenTrial (d₂ i)) (2^s)
      (z₁+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₁ i):ℤ)))
      (z₂+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₂ i):ℤ))) := by
  unfold posteriorJointAnchors
  simp_rw [posterior_unsigned_motif,mul_assoc]
  rw [posterior_count_support dg (fun v =>
    windowKernel (∑i,hiddenTrial (d₁ i)) (2^s) (z₁+v+∑i,(visibleOnes (d₁ i):ℤ)) *
    windowKernel (∑i,hiddenTrial (d₂ i)) (2^s) (z₂+v+∑i,(visibleOnes (d₂ i):ℤ)))]
  unfold jointWindowKernel
  apply Finset.sum_congr rfl
  intro v hv
  have h₁ : z₁+((∑i,(visibleOnes (dg i):ℤ))+v)+(∑i,(visibleOnes (d₁ i):ℤ)) =
      z₁+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₁ i):ℤ))+v := by ring
  have h₂ : z₂+((∑i,(visibleOnes (dg i):ℤ))+v)+(∑i,(visibleOnes (d₂ i):ℤ)) =
      z₂+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₂ i):ℤ))+v := by ring
  rw [h₁,h₂,mul_assoc]

/-- Quantitative sibling summation now directly bounds genuine posterior
bits, not an independent-anchor surrogate. -/
theorem posterior_sibling_anchor_energy {ιg ι₁ ι₂ : Type*}
    [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (A B C D : Finset ℤ) (c₁ c₂ : ℤ) :
    (∑a∈A, ∑b∈B, ∑_c∈closeLabels C (2^s) a, ∑_d∈closeLabels D (2^s) b,
      (posteriorJointAnchors dg d₁ d₂ s (a-c₁) (b-c₂))^2) ≤
    4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (dg i))*
      binomialBound (∑i,hiddenTrial (d₂ i)) := by
  simp_rw [posteriorJointAnchors_eq]
  have he : ∀a c u v : ℤ, a-c+u+v = a-(c-u-v) := by intros; omega
  simp_rw [he]
  exact sibling_anchor_energy (∑i,hiddenTrial (dg i)) (∑i,hiddenTrial (d₁ i))
    (∑i,hiddenTrial (d₂ i)) (2^s) A B C D
    (c₁-(∑i,(visibleOnes (dg i):ℤ))-(∑i,(visibleOnes (d₁ i):ℤ)))
    (c₂-(∑i,(visibleOnes (dg i):ℤ))-(∑i,(visibleOnes (d₂ i):ℤ)))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_mul_const (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => f a*c) = P.expect f*c := by
  unfold expect
  simp only [←mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f := by
  unfold expect
  simp only [mul_left_comm (P.mass _) c,Finset.mul_sum]

theorem coordinateProduct_expect_product {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i,f i (x i)) = ∏i,(P i).expect (f i) := by
  unfold expect coordinateProduct
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : α) => (P i).mass a*f i a)).symm

end FiniteLaw

theorem sourceTreeAnchors_child (T n g : ℕ → ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (h : Fin (T b)) (tail : List ℕ) :
    sourceTreeAnchors T n g center globalShift (b+1) bits incoming (h.val::tail) =
      sourceTreeAnchors T n g center globalShift b (bits.2.2 h)
        (globalShift b bits.2.1 h) tail := by
  simp only [sourceTreeAnchors,dite_eq_left h.isLt]

/-- Moving the origin of a subtree preserves the literal type recursion. -/
theorem windowLeafSign_prefix (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (pre path : List ℕ) (τ : ℝ) (v : WindowLeaf T b) :
    windowLeafSign T s X b (pre++path) τ v =
      windowLeafSign T s (fun tail => X (pre++tail)) b path τ v := by
  induction b generalizing path τ with
  | zero => rfl
  | succ b ih =>
    change windowLeafSign T s X b _ _ v.2 = _
    rw [List.append_assoc,ih]
    rfl

theorem sourceTreeLeafSign_eq (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool b) (incoming : ℤ)
    (τ : ℝ) (v : WindowLeaf T b) :
    sourceTreeLeafSign T n g s center globalShift b bits incoming τ v =
      windowLeafSign T s (sourceTreeAnchors T n g center globalShift b bits incoming) b [] τ v := by
  induction b generalizing incoming τ with
  | zero => rfl
  | succ b ih =>
    change sourceTreeLeafSign T n g s center globalShift b _ _ _ v.2 =
      windowLeafSign T s _ b [v.1.val] _ v.2
    rw [ih]
    have hp := windowLeafSign_prefix T s
      (sourceTreeAnchors T n g center globalShift (b+1) bits incoming)
      b [v.1.val] []
      (motifChildSign s (center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) v.1.val τ) v.2
    simp only [List.append_nil,List.singleton_append,sourceTreeAnchors_child] at hp
    exact hp.symm

end TraceReconstruction

-- Actual subtree coefficient factorization and singleton cancellation.
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem occupiedWindowWeight_succ (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1+1)))
    (a : OccupiedWindowChoice T (b+1) S) :
    occupiedWindowWeight T s X (b+1) path S a =
      occupiedRootWeight T s (b+1) S a (X path) *
        ∏i : Fin (selectedChildren S).card,
          occupiedWindowWeight T s X b
            (path++[((selectedChildren S).equivFin.symm i).val.val])
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i) := by
  unfold occupiedWindowWeight
  change (∏i, _ * @internalRoleWeight
    ((occupiedWindowShape T s X b
      (path++[((selectedChildren S).equivFin.symm i).val.val])
      (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)).termTree
      (occupiedWindowChoiceEquiv T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))).isOdd
        (Classical.propDecidable _) _ _ _) = _
  simp_rw [occupiedWindowTerm_eq]
  rw [Finset.prod_mul_distrib,mul_comm]
  rfl

/-- Moving a subtree's path origin does not change any of its role factors. -/
theorem occupiedWindowWeight_prefix (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (pre path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) :
    occupiedWindowWeight T s X b (pre++path) S a =
      occupiedWindowWeight T s (fun tail => X (pre++tail)) b path S a := by
  induction b generalizing path with
  | zero => rfl
  | succ b ih =>
    rw [occupiedWindowWeight_succ,occupiedWindowWeight_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [List.append_assoc,ih]

theorem bottomRoleWeight_abs_le_one (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |bottomRoleWeight χ σ a| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> norm_num [bottomRoleWeight]

theorem internalRoleWeight_abs_le_one (odd : Prop) [Decidable odd]
    (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |internalRoleWeight odd χ σ a| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> by_cases ho : odd <;> norm_num [internalRoleWeight,roleWeight,ho]

theorem occupiedRootWeight_abs_le_one (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) (X : ℤ) :
    |occupiedRootWeight T s b S a X| ≤ 1 := by
  cases b with
  | zero =>
    rw [occupiedRootWeight,Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun i _ => bottomRoleWeight_abs_le_one _ _ (prouhet_motif_value s _) (a i))
  | succ b =>
    rw [occupiedRootWeight,Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun i _ => internalRoleWeight_abs_le_one _ _ _ (prouhet_motif_value s _) (a.2 i))

theorem occupiedWindowWeight_abs_le_one (T : ℕ → ℕ) (s : ℕ)
    (X : List ℕ → ℤ) (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) : |occupiedWindowWeight T s X b path S a| ≤ 1 := by
  induction b generalizing path with
  | zero => exact occupiedRootWeight_abs_le_one T s 0 S a _
  | succ b ih =>
    rw [occupiedWindowWeight_succ,abs_mul,Finset.abs_prod]
    exact (mul_le_of_le_one_left (by positivity)
      (occupiedRootWeight_abs_le_one T s (b+1) S a _)).trans
      (Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => ih _ _ _))

/-- A singleton signed role factors off its signed motif with a scalar
independent of all displacements. Bottom zero-role terms really vanish. -/
theorem bottom_singleton_factor {n : ℕ} (a : Fin n → Fin 3) (i : Fin n)
    (hi : a i=2) (hrest : ∀j,j≠i → a j=0) :
    ∃c : ℝ, |c|≤1 ∧ ∀χ σ : Fin n → ℝ,
      (∏j,bottomRoleWeight (χ j) (σ j) (a j)) = c*σ i := by
  let c : ℝ := -(∏j∈Finset.univ.erase i,(0:ℝ))/2
  refine ⟨c,?_,?_⟩
  · have hp : 0 ≤ ∏j∈Finset.univ.erase i,(0:ℝ) := Finset.prod_nonneg (fun _ _ => le_rfl)
    have hp' : (∏j∈Finset.univ.erase i,(0:ℝ)) ≤ 1 := Finset.prod_le_one
      (fun _ _ => le_rfl) (fun _ _ => by norm_num)
    dsimp [c]
    rw [abs_div,abs_neg,abs_of_nonneg hp]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  · intro χ σ
    rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have he : (∏j∈Finset.univ.erase i,bottomRoleWeight (χ j) (σ j) (a j)) =
        ∏j∈Finset.univ.erase i,(0:ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [hrest j (Finset.mem_erase.mp hj).1,bottomRoleWeight,↓reduceIte]
    rw [he,hi]
    simp only [bottomRoleWeight,show (2:Fin 3)≠0 by decide,
      show (2:Fin 3)≠1 by decide,↓reduceIte]
    dsimp [c]
    ring

theorem internal_singleton_factor {n : ℕ} (odd : Fin n → Prop)
    (a : Fin n → Fin 3) (i : Fin n) (hi : a i=2) (hrest : ∀j,j≠i → a j=0) :
    ∃c : ℝ, |c|≤1 ∧ ∀χ σ : Fin n → ℝ,
      (∏j,@internalRoleWeight (odd j) (Classical.propDecidable _) (χ j) (σ j) (a j)) = c*σ i := by
  refine ⟨if odd i then 1 else 0,?_,?_⟩
  · split_ifs <;> norm_num
  · intro χ σ
    rw [Finset.prod_eq_single i]
    · by_cases ho : odd i <;> simp [internalRoleWeight,roleWeight,hi,ho]
    · intro j hj hji
      by_cases ho : odd j <;> simp [internalRoleWeight,roleWeight,hrest j hji,ho]
    · simp

namespace FiniteLaw

/-- Unoccupied independent coordinates integrate to one. -/
theorem coordinateProduct_expect_subtype {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (S : Finset (Fin n)) (f : S → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i : S, f i (x i.val)) =
      ∏i : S, (P i.val).expect (f i) := by
  have scalar : ∀f : S → ℝ,
      (∏j : Fin n, if hj : j∈S then f ⟨j,hj⟩ else 1) = ∏i : S,f i := by
    intro f
    calc
      _ = ∏j∈S, if hj : j∈S then f ⟨j,hj⟩ else 1 :=
        (Finset.prod_subset S.subset_univ (fun j _ hj => dite_eq_right hj)).symm
      _ = ∏i : S, if hj : i.val∈S then f ⟨i.val,hj⟩ else 1 :=
        Finset.prod_subtype S (fun _ => Iff.rfl) _
      _ = _ := by simp only [dite_eq_left (Subtype.property _)]
  let F : Fin n → α → ℝ := fun j a => if hj : j∈S then f ⟨j,hj⟩ a else 1
  have hp : ∀x : Fin n → α, (∏j,F j (x j)) = ∏i : S,f i (x i.val) := by
    intro x
    exact scalar (fun i => f i (x i.val))
  rw [show (fun x : Fin n → α => ∏i : S,f i (x i.val)) = (fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm]
  rw [coordinateProduct_expect_product]
  have he : ∀j, (P j).expect (F j) = if hj : j∈S then (P j).expect (f ⟨j,hj⟩) else 1 := by
    intro j
    by_cases hj : j∈S
    · simp only [F,dite_eq_left hj]
    · simp only [F,dite_eq_right hj,expect_const]
  simp_rw [he]
  exact scalar (fun i => (P i.val).expect (f i))

theorem coordinateProduct_expect_selected {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (S : Finset (Fin n)) (f : Fin S.card → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i : Fin S.card, f i (x (S.equivFin.symm i).val)) =
      ∏i : Fin S.card, (P (S.equivFin.symm i).val).expect (f i) := by
  have hp : ∀x : Fin n → α,
      (∏i : Fin S.card,f i (x (S.equivFin.symm i).val)) =
        ∏i : S,f (S.equivFin i) (x i.val) := by
    intro x
    simpa only [Equiv.apply_symm_apply] using
      Equiv.prod_comp S.equivFin.symm (fun i : S => f (S.equivFin i) (x i.val))
  simp_rw [hp,coordinateProduct_expect_subtype]
  symm
  simpa only [Equiv.apply_symm_apply] using
    Equiv.prod_comp S.equivFin.symm (fun i : S => (P i.val).expect (f (S.equivFin i)))

theorem expect_prod_selected {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n : ℕ} (P : FiniteLaw α) (Q : FiniteLaw β) (R : Fin n → FiniteLaw γ)
    (S : Finset (Fin n)) (f : α → ℝ) (h : β → Fin S.card → γ → ℝ) :
    (P.prod (Q.prod (coordinateProduct R))).expect (fun x =>
      f x.1 * ∏i : Fin S.card, h x.2.1 i (x.2.2 (S.equivFin.symm i).val)) =
      P.expect f * Q.expect (fun z => ∏i : Fin S.card,
        (R (S.equivFin.symm i).val).expect (h z i)) := by
  simp_rw [expect_prod,expect_const_mul,coordinateProduct_expect_selected]
  rw [expect_mul_const]

theorem abs_expect_le_const {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (c : ℝ) (h : ∀a, |f a| ≤ c) : |P.expect f| ≤ c :=
  (P.abs_expect_le f).trans ((P.expect_mono h).trans_eq (P.expect_const c))

end FiniteLaw


theorem sourceRoleTerm_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (bits : WindowAssignments T n g Bool 1) (incoming : ℤ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) :
    sourceRoleTerm T n g s center globalShift 0 bits incoming S a =
      occupiedRootWeight T s 0 S a (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) := rfl

theorem sourceRoleTerm_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) :
    sourceRoleTerm T n g s center globalShift (b+1) bits incoming S a =
      occupiedRootWeight T s (b+1) S a (center (b+1)-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) *
        ∏i : Fin (selectedChildren S).card,
          sourceRoleTerm T n g s center globalShift b
            (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i) := by
  unfold sourceRoleTerm
  rw [occupiedWindowWeight_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hp := occupiedWindowWeight_prefix T s
    (sourceTreeAnchors T n g center globalShift (b+1+1) bits incoming) b
    [((selectedChildren S).equivFin.symm i).val.val] []
    (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)
  simpa only [List.append_nil,List.nil_append,List.singleton_append,sourceTreeAnchors_child] using hp

theorem sourceRoleAverage_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (d : WindowAssignments T n g (Option Bool) 1) (incoming : ℤ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) :
    sourceRoleAverage T n g s center globalShift 0 d incoming S a =
      (posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s 0 S a (center 0-(∑i,(bitIndex (loc i):ℤ))-incoming)) := by
  rw [sourceRoleAverage]
  simp_rw [sourceRoleTerm_zero]
  rcases d with ⟨dl,dg,dc⟩
  change ((posteriorArray dl).prod ((posteriorArray dg).prod
    (coordinateProduct (fun i => windowPosteriorLaw T n g 0 (dc i))))).expect
      (fun bits => occupiedRootWeight T s 0 S a
        (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) = _
  rw [expect_prod]
  simp only [expect_const]

theorem sourceRoleAverage_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) :
    sourceRoleAverage T n g s center globalShift (b+1) d incoming S a =
      (posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s (b+1) S a (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming)) *
      (posteriorArray d.2.1).expect (fun glob =>
        ∏i : Fin (selectedChildren S).card,
          sourceRoleAverage T n g s center globalShift b
            (d.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)) := by
  rw [sourceRoleAverage]
  simp_rw [sourceRoleTerm_succ]
  exact FiniteLaw.expect_prod_selected (posteriorArray d.1) (posteriorArray d.2.1)
    (fun i => windowPosteriorLaw T n g (b+1) (d.2.2 i)) (selectedChildren S)
    (fun loc => occupiedRootWeight T s (b+1) S a
      (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming))
    (fun glob i bits => sourceRoleTerm T n g s center globalShift b bits
      (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
      (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))

theorem sourceRoleAverage_abs_le_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤1 := by
  apply FiniteLaw.abs_expect_le_const
  intro bits
  exact occupiedWindowWeight_abs_le_one T s _ b [] S a

theorem occupiedRoot_singleton_factor (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : occupiedRootHasSingleton T b S a) :
    ∃c : ℝ, |c|≤1 ∧ ∃label : ℤ, ∀X,
      occupiedRootWeight T s b S a X = c*(prouhetSeries s).coeff (label-X) := by
  cases b with
  | zero =>
    obtain ⟨i,hi,hr⟩ := h
    obtain ⟨c,hc,hfac⟩ := bottom_singleton_factor a i hi hr
    refine ⟨c,hc,((S.equivFin.symm i).val.1.val:ℤ),fun X => ?_⟩
    exact hfac _ _
  | succ b =>
    obtain ⟨i,hi,hr⟩ := h
    obtain ⟨c,hc,hfac⟩ := internal_singleton_factor
      (fun j => (occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val) (a.1 j)).isOdd)
      a.2 i hi hr
    refine ⟨c,hc,(((selectedChildren S).equivFin.symm i).val.val:ℤ),fun X => ?_⟩
    exact hfac _ _

theorem occupiedRoot_singleton_average (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : occupiedRootHasSingleton T b S a) {m : ℕ} (d : Fin m → Option Bool)
    (center incoming : ℤ) :
    |(posteriorArray d).expect (fun loc => occupiedRootWeight T s b S a
      (center-(∑i,(bitIndex (loc i):ℤ))-incoming))| ≤ posteriorSmoothingCost s d := by
  obtain ⟨c,hc,label,hfac⟩ := occupiedRoot_singleton_factor T s b S a h
  simp_rw [hfac,expect_const_mul,abs_mul]
  have he : ∀loc : Fin m → Bool,
      label-(center-(∑i,(bitIndex (loc i):ℤ))-incoming) =
        (label-center+incoming)+(∑i,(bitIndex (loc i):ℤ)) := by intro loc; omega
  simp_rw [he]
  have hb : |(posteriorArray d).expect (fun loc =>
      (prouhetSeries s).coeff ((label-center+incoming)+(∑i,(bitIndex (loc i):ℤ))))| ≤
        posteriorSmoothingCost s d := by
    have hb := posterior_signed_motif_bound d s (label-center+incoming)
    unfold posteriorArray coordinateProduct expect posteriorSmoothingCost
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
    exact Subsingleton.elim _ _
  calc
    _ ≤ 1*|(posteriorArray d).expect (fun loc =>
        (prouhetSeries s).coeff ((label-center+incoming)+(∑i,(bitIndex (loc i):ℤ))))| :=
      mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hb

theorem abs_prod_le_coordinate {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι)
    (h : ∀j,j≠i → |f j|≤1) : |∏j,f j|≤|f i| := by
  rw [Finset.abs_prod,←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have he : (∏j∈Finset.univ.erase i,|f j|)≤1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j hj => h j (Finset.mem_erase.mp hj).1)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (f i))

/-- Literal singleton cancellation for the complete posterior bit tree.
No successful-fit event is conditioned on, and the common parent-global
jitter is retained until after the child factors have averaged. -/
theorem sourceRoleAverage_singleton (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d)
    (hsing : ¬(occupiedWindowTerm T b S a).noSingleton) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤η := by
  induction b generalizing incoming with
  | zero =>
    have hh : Odd (signedRoleCount a) ∧ activeRoleCount a=1 := by
      by_contra! h
      apply hsing
      exact ⟨fun ho he => h ho he,fun _ => trivial⟩
    have hr : occupiedRootHasSingleton T 0 S a :=
      (odd_roles_singleton_or_branch a hh.1).resolve_right (by omega)
    rw [sourceRoleAverage_zero]
    exact (occupiedRoot_singleton_average T s 0 S a hr d.1 _ _).trans hcap.1
  | succ b ih =>
    rw [sourceRoleAverage_succ,abs_mul]
    have hroot : |(posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s (b+1) S a
          (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming))|≤1 :=
      FiniteLaw.abs_expect_le_const _ _ 1 (fun _ => occupiedRootWeight_abs_le_one T s (b+1) S a _)
    have hglob : |(posteriorArray d.2.1).expect (fun glob =>
        ∏i : Fin (selectedChildren S).card,
          sourceRoleAverage T n g s center globalShift b
            (d.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))|≤1 := by
      apply FiniteLaw.abs_expect_le_const
      intro glob
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun i _ => sourceRoleAverage_abs_le_one T n g s center globalShift b _ _ _ _)
    by_cases hr : occupiedRootHasSingleton T (b+1) S a
    · have hh := (occupiedRoot_singleton_average T s (b+1) S a hr d.1
        (center (b+1)) incoming).trans hcap.1
      exact (mul_le_mul_of_nonneg_left hglob (abs_nonneg _)).trans (by simpa using hh)
    · have hex : ∃i, ¬(occupiedWindowTerm T b
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)).noSingleton := by
        by_contra! h
        apply hsing
        refine ⟨?_,h⟩
        intro ho he
        have hh := odd_roles_singleton_or_branch a.2 ho
        exact hr (hh.resolve_right (by omega))
      obtain ⟨i,hi⟩ := hex
      have hsmall : |(posteriorArray d.2.1).expect (fun glob =>
          ∏j : Fin (selectedChildren S).card,
            sourceRoleAverage T n g s center globalShift b
              (d.2.2 ((selectedChildren S).equivFin.symm j).val)
              (globalShift (b+1) glob ((selectedChildren S).equivFin.symm j).val)
              (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val) (a.1 j))|≤η := by
        apply FiniteLaw.abs_expect_le_const
        intro glob
        apply (abs_prod_le_coordinate _ i (fun j _ =>
          sourceRoleAverage_abs_le_one T n g s center globalShift b _ _ _ _)).trans
        exact ih _ _ _ _ (hcap.2 _) hi
      exact (mul_le_mul_of_nonneg_right hroot (abs_nonneg _)).trans (by simpa using hsmall)

end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Anchors
attribute [-instance] _root_.OAI.TraceReconstruction.OccupiedParityTree.edgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraInteriorLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.extraLeafEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraEdgeFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.forcedExtraLabelsFintype _root_.OAI.TraceReconstruction.OccupiedParityTree.labelsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Anchors

Forced anchors, extra-leaf closeness, and correlated group square-sum estimates.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
/-- Two distinct actual child coordinates are independent. This does not
assert independence of their shared parent-global jitter. -/
theorem coordinateProduct_expect_two {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (a c : Fin n) (hne : a≠c) (f h : α → ℝ) :
    (coordinateProduct P).expect (fun x => f (x a)*h (x c)) = (P a).expect f*(P c).expect h := by
  let F : Fin n → α → ℝ := fun j x => if j=a then f x else if j=c then h x else 1
  have hp : ∀x : Fin n → α, (∏j,F j (x j)) = f (x a)*h (x c) := by
    intro x
    rw [Finset.prod_eq_mul a c hne]
    · simp [F,hne.symm]
    · intro j hj hjs
      simp [F,hjs.1,hjs.2]
    · simp
    · simp
  rw [show (fun x : Fin n → α => f (x a)*h (x c)) = (fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm,coordinateProduct_expect_product]
  rw [Finset.prod_eq_mul a c hne]
  · simp [F,hne.symm]
  · intro j hj hjs
    simp [F,hjs.1,hjs.2,expect_const]
  · simp
  · simp

/-- Exact local/global/children factorization with the parent-global draw
outside the product of child expectations. -/
theorem expect_prod_two {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n : ℕ} (P : FiniteLaw α) (Q : FiniteLaw β) (R : Fin n → FiniteLaw γ)
    (a c : Fin n) (hne : a≠c) (f : α → ℝ) (h k : β → γ → ℝ) :
    (P.prod (Q.prod (coordinateProduct R))).expect (fun x =>
      f x.1 * (h x.2.1 (x.2.2 a)*k x.2.1 (x.2.2 c))) =
      P.expect f * Q.expect (fun z => (R a).expect (h z)*(R c).expect (k z)) := by
  simp_rw [expect_prod,expect_const_mul,coordinateProduct_expect_two R a c hne]
  rw [expect_mul_const]
end FiniteLaw

theorem binaryAnchorAverage_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (p : BinaryWindowLabels T 0) (d : WindowAssignments T n g (Option Bool) 0) (incoming : ℤ) :
    binaryAnchorAverage T n g s center globalShift 0 p d incoming = 1 := by
  apply expect_const

theorem binaryAnchorAverage_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T (b+1)) (d : WindowAssignments T n g (Option Bool) (b+1))
    (incoming : ℤ) (hd : p.1≠p.2.1) :
    binaryAnchorAverage T n g s center globalShift (b+1) p d incoming =
      (posteriorArray d.1).expect (fun loc =>
        motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (loc i):ℤ))+incoming)) *
      (posteriorArray d.2.1).expect (fun glob =>
        binaryAnchorAverage T n g s center globalShift b p.2.2.1 (d.2.2 p.1)
          (globalShift b glob p.1) *
        binaryAnchorAverage T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1)
          (globalShift b glob p.2.1)) := by
  exact FiniteLaw.expect_prod_two (posteriorArray d.1) (posteriorArray d.2.1)
    (fun i => windowPosteriorLaw T n g b (d.2.2 i)) p.1 p.2.1 hd
    (fun loc => motifIndicator s ((p.1.val:ℤ)-center b+(∑i,(bitIndex (loc i):ℤ))+incoming))
    (fun glob bits => binaryAnchorKernel T n g s center globalShift b p.2.2.1 bits
      (globalShift b glob p.1))
    (fun glob bits => binaryAnchorKernel T n g s center globalShift b p.2.2.2 bits
      (globalShift b glob p.2.1))

theorem localAnchorAverage_kernel {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (z : ℤ) :
    localAnchorAverage d s z = windowKernel (∑i,hiddenTrial (d i)) (2^s)
      (z+∑i,(visibleOnes (d i):ℤ)) := by
  have h := posterior_unsigned_motif d s z
  unfold localAnchorAverage posteriorArray coordinateProduct expect
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  exact Subsingleton.elim _ _

/-- Exact factorization of the forced anchor expectation into its root
kernel and all correlated sibling groups, at the real metadata/labels. -/
theorem binaryAnchorAverage_factor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T (b+1)) (d : WindowAssignments T n g (Option Bool) (b+1))
    (incoming : ℤ) (hd : BinaryWindowLabels.distinct T (b+1) p) :
    binaryAnchorAverage T n g s center globalShift (b+1) p d incoming =
      localAnchorAverage d.1 s ((p.1.val:ℤ)-center b+incoming) *
        binaryAnchorBelow T n g s center globalShift b p d := by
  induction b generalizing incoming with
  | zero =>
    rw [binaryAnchorAverage_succ T n g s center globalShift _ p d incoming hd.1]
    simp only [binaryAnchorAverage_zero,expect_const,binaryAnchorBelow,mul_one]
    unfold localAnchorAverage
    congr 1
    funext loc
    congr 1
    omega
  | succ b ih =>
    have hl := fun incoming => ih p.2.2.1 (d.2.2 p.1) incoming hd.2.1
    have hr := fun incoming => ih p.2.2.2 (d.2.2 p.2.1) incoming hd.2.2
    have hroot : (posteriorArray d.1).expect (fun loc =>
        motifIndicator s ((p.1.val:ℤ)-center (b+1)+(∑i,(bitIndex (loc i):ℤ))+incoming)) =
        localAnchorAverage d.1 s ((p.1.val:ℤ)-center (b+1)+incoming) := by
      apply congrArg (FiniteLaw.expect (posteriorArray d.1))
      funext loc
      congr 1
      omega
    have hh : (posteriorArray d.2.1).expect (fun glob =>
        binaryAnchorAverage T n g s center globalShift (b+1) p.2.2.1 (d.2.2 p.1)
          (globalShift (b+1) glob p.1) *
        binaryAnchorAverage T n g s center globalShift (b+1) p.2.2.2 (d.2.2 p.2.1)
          (globalShift (b+1) glob p.2.1)) =
        binaryAnchorBelow T n g s center globalShift (b+1) p d := by
      calc
        _ = (posteriorArray d.2.1).expect (fun glob =>
          (localAnchorAverage (d.2.2 p.1).1 s
            ((p.2.2.1.1.val:ℤ)-center b+globalShift (b+1) glob p.1) *
          localAnchorAverage (d.2.2 p.2.1).1 s
            ((p.2.2.2.1.val:ℤ)-center b+globalShift (b+1) glob p.2.1)) *
          (binaryAnchorBelow T n g s center globalShift b p.2.2.1 (d.2.2 p.1) *
           binaryAnchorBelow T n g s center globalShift b p.2.2.2 (d.2.2 p.2.1))) := by
            apply congrArg (FiniteLaw.expect (posteriorArray d.2.1))
            funext glob
            exact (congrArg₂ (·*·) (hl _) (hr _)).trans (by ring)
        _ = _ := expect_mul_const _ _ _
    exact (binaryAnchorAverage_succ T n g s center globalShift _ p d incoming hd.1).trans
      (congrArg₂ (·*·) hroot hh)

/-- One plateau group's local means are the genuine shared-global joint
anchor, with exactly the affine shift appearing in the layout. -/
theorem localAnchor_pair_plateau {mg m₁ m₂ : ℕ}
    (dg : Fin mg → Option Bool) (d₁ : Fin m₁ → Option Bool) (d₂ : Fin m₂ → Option Bool)
    (s : ℕ) (z₁ z₂ shift : ℤ) :
    (posteriorArray dg).expect (fun glob =>
      localAnchorAverage d₁ s (z₁+(∑i,(bitIndex (glob i):ℤ))-shift) *
      localAnchorAverage d₂ s (z₂+(∑i,(bitIndex (glob i):ℤ))-shift)) =
    posteriorJointAnchors dg d₁ d₂ s (z₁-shift) (z₂-shift) := by
  unfold localAnchorAverage posteriorArray coordinateProduct expect posteriorJointAnchors
  have he : ∀a b c d : ℤ,(a+b-c)+d = (a-c)+b+d := by intros; omega
  simp_rw [he,mul_assoc]
  congr 2
  · exact Subsingleton.elim _ _
  · funext bg
    congr 1
    congr 1
    · congr 2 ; exact Subsingleton.elim _ _
    · congr 2 ; exact Subsingleton.elim _ _

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem forcedWindowLabels_distinct (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    BinaryWindowLabels.distinct T (b+1) (forcedWindowLabels T b S a F) := by
  induction b with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      refine ⟨?_,trivial,trivial⟩
      intro he
      apply hne
      apply S.equivFin.symm.injective
      apply Subtype.ext
      exact Prod.ext he (Subsingleton.elim (α := Fin 1) _ _)
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      refine ⟨?_,ih _ _ left,ih _ _ right⟩
      intro he
      exact hne ((selectedChildren S).equivFin.symm.injective (Subtype.ext he))

theorem motifIndicator_nonneg (s : ℕ) (z : ℤ) : 0 ≤ motifIndicator s z := by
  unfold motifIndicator
  split_ifs <;> norm_num

theorem binaryAnchorKernel_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (bits : WindowAssignments T n g Bool b)
    (incoming : ℤ) : 0≤binaryAnchorKernel T n g s center globalShift b p bits incoming := by
  induction b generalizing incoming with
  | zero => exact zero_le_one
  | succ b ih =>
    exact mul_nonneg (motifIndicator_nonneg _ _) (mul_nonneg (ih _ _ _) (ih _ _ _))

theorem bottomRoleWeight_abs_le_indicator (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |bottomRoleWeight χ σ a|≤χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> norm_num [bottomRoleWeight]

theorem internalRoleWeight_active_abs_le_indicator (odd : Prop) [Decidable odd]
    (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) (ha : a≠0) :
    |internalRoleWeight odd χ σ a|≤χ := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> by_cases ho : odd <;> norm_num [internalRoleWeight,roleWeight,ho] at *

theorem occupiedRootWeight_bottom_anchor (T : ℕ → ℕ) (s : ℕ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) (X : ℤ) (i : Fin S.card) :
    |occupiedRootWeight T s 0 S a X|≤
      motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X) := by
  exact (abs_prod_le_coordinate _ i (fun j _ =>
    bottomRoleWeight_abs_le_one _ _ (prouhet_motif_value _ _) _)).trans
      (bottomRoleWeight_abs_le_indicator _ _ (prouhet_motif_value _ _) _)

theorem occupiedRootWeight_internal_anchor (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) (X : ℤ)
    (i : Fin (selectedChildren S).card) (hi : a.2 i≠0) :
    |occupiedRootWeight T s (b+1) S a X|≤
      motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X) := by
  exact (abs_prod_le_coordinate _ i (fun j _ =>
    internalRoleWeight_abs_le_one _ _ _ (prouhet_motif_value _ _) _)).trans
      (internalRoleWeight_active_abs_le_indicator _ _ _ (prouhet_motif_value _ _) _ hi)

theorem abs_prod_le_two {ι : Type*} [Fintype ι] (f : ι → ℝ) (a c : ι) (hne : a≠c)
    (h : ∀j,j≠a → j≠c → |f j|≤1) : |∏j,f j|≤|f a| * |f c| := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏j, if j=a then |f a| else if j=c then |f c| else 1 := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j hj
      by_cases hja : j=a
      · simp [hja]
      · by_cases hjc : j=c
        · simp [hjc,hne.symm]
        · simpa only [ite_eq_right hja,ite_eq_right hjc] using h j hja hjc
    _ = _ := by
      rw [Finset.prod_eq_mul a c hne]
      · simp [hne.symm]
      · intro j hj hjs
        simp [hjs.1,hjs.2]
      · simp
      · simp

/-- The real role term is pointwise dominated by its selected unsigned
anchors. No independence assumption is used in this domination. -/
theorem sourceRoleTerm_forced_anchor (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      binaryAnchorKernel T n g s center globalShift (b+1) (forcedWindowLabels T b S a F) bits incoming := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero]
      change _ ≤ motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-center 0+
        (∑i,(bitIndex (bits.1 i):ℤ))+incoming)*(1*1)
      rw [mul_one,mul_one]
      convert occupiedRootWeight_bottom_anchor T s S a
        (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) i using 1 ; congr 1 ; omega
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ,abs_mul]
      have hroot := occupiedRootWeight_internal_anchor T s b S a
        (center (b+1)-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) i hi
      have hprod := abs_prod_le_two (fun k : Fin (selectedChildren S).card =>
        sourceRoleTerm T n g s center globalShift b
          (bits.2.2 ((selectedChildren S).equivFin.symm k).val)
          (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm k).val)
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm k).val) (a.1 k)) i j hne
          (fun k _ _ => occupiedWindowWeight_abs_le_one T s _ b [] _ _)
      have hl := ih (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
        (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val) _ _ left
      have hr := ih (bits.2.2 ((selectedChildren S).equivFin.symm j).val)
        (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm j).val) _ _ right
      have hp := mul_le_mul hl hr (abs_nonneg _) (binaryAnchorKernel_nonneg T n g s center globalShift _ _ _ _)
      have hh := mul_le_mul hroot (hprod.trans hp) (abs_nonneg _) (motifIndicator_nonneg _ _)
      apply hh.trans_eq
      change motifIndicator s _ * _ = motifIndicator s
        ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-center (b+1)+
          (∑k,(bitIndex (bits.1 k):ℤ))+incoming) * _
      congr 2
      omega

theorem sourceRoleTerm_valid (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : sourceRoleTerm T n g s center globalShift b bits incoming S a ≠ 0) :
    (occupiedWindowTerm T b S a).valid := by
  have hh := (occupiedWindowShape T s
    (sourceTreeAnchors T n g center globalShift (b+1) bits incoming) b [] S).term_valid
    (occupiedWindowChoiceEquiv T s
      (sourceTreeAnchors T n g center globalShift (b+1) bits incoming) b [] S a) h
  simpa only [occupiedWindowTerm_eq] using hh

theorem sourceRoleAverage_valid (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : sourceRoleAverage T n g s center globalShift b d incoming S a ≠ 0) :
    (occupiedWindowTerm T b S a).valid := by
  by_contra hn
  have hh : ∀bits, sourceRoleTerm T n g s center globalShift b bits incoming S a=0 := by
    intro bits
    by_contra hz
    exact hn (sourceRoleTerm_valid T n g s center globalShift b bits incoming S a hz)
  apply h
  change (windowPosteriorLaw T n g (b+1) d).expect _ = 0
  rw [show (fun bits => sourceRoleTerm T n g s center globalShift b bits incoming S a) =
    (fun _ => 0) from funext hh,expect_const]

end TraceReconstruction


namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem sourceBottomIndicator_zero_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (v : WindowLeaf T (b+1)) :
    sourceBottomIndicator T n g s center globalShift b bits incoming v=0 ∨
    sourceBottomIndicator T n g s center globalShift b bits incoming v=1 := by
  induction b generalizing incoming with
  | zero => unfold sourceBottomIndicator motifIndicator; split_ifs <;> simp
  | succ b ih => exact ih _ _ _

theorem prod_zero_one {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (h : ∀i∈S,f i=0 ∨ f i=1) : (∏i∈S,f i)=0 ∨ (∏i∈S,f i)=1 := by
  by_cases hz : ∃i∈S,f i=0
  · obtain ⟨i,hi,hz⟩ := hz
    exact Or.inl (Finset.prod_eq_zero hi hz)
  · right
    apply Finset.prod_eq_one
    intro i hi
    exact (h i hi).resolve_left (fun he => hz ⟨i,hi,he⟩)

theorem binaryAnchorKernel_zero_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (p : BinaryWindowLabels T b) (bits : WindowAssignments T n g Bool b)
    (incoming : ℤ) :
    binaryAnchorKernel T n g s center globalShift b p bits incoming=0 ∨
    binaryAnchorKernel T n g s center globalShift b p bits incoming=1 := by
  induction b generalizing incoming with
  | zero => exact Or.inr rfl
  | succ b ih =>
    have hl := ih p.2.2.1 (bits.2.2 p.1) (globalShift b bits.2.1 p.1)
    have hr := ih p.2.2.2 (bits.2.2 p.2.1) (globalShift b bits.2.1 p.2.1)
    change (_*(_*_)=0) ∨ (_*(_*_)=1)
    rcases hl with hl|hl <;> rcases hr with hr|hr <;> rw [hl,hr] <;>
      unfold motifIndicator <;> split_ifs <;> norm_num

theorem sourceLeafProduct_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) :
    sourceLeafProduct T n g s center globalShift (b+1) bits incoming S =
      ∏i : Fin (selectedChildren S).card,
        sourceLeafProduct T n g s center globalShift b
          (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
          (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val)
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) := by
  symm
  exact (selected_prod_index (selectedChildren S) (fun h =>
    ∏v∈selectedChildLeaves S h,
      sourceBottomIndicator T n g s center globalShift b (bits.2.2 h)
        (globalShift (b+1) bits.2.1 h) v)).trans
      (selected_prod_children S (fun v =>
        sourceBottomIndicator T n g s center globalShift (b+1) bits incoming v))

/-- Every selected leaf is active in the bottom expansion, including those
outside the forced tree. Their absolute constraints are not lost. -/
theorem sourceRoleTerm_all_leaf_constraints (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      sourceLeafProduct T n g s center globalShift b bits incoming S := by
  induction b generalizing incoming with
  | zero =>
    rw [sourceRoleTerm_zero]
    change |∏i : Fin S.card, _|≤_
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏i : Fin S.card, motifIndicator s
          (((S.equivFin.symm i).val.1.val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun i _ => bottomRoleWeight_abs_le_indicator _ _ (prouhet_motif_value _ _) _)
      _ = ∏v∈S, motifIndicator s ((v.1.val:ℤ)-
          (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) :=
        selected_prod_index S (fun v : WindowLeaf T 1 => motifIndicator s
          ((v.1.val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v hv
        change motifIndicator s _ = motifIndicator s _
        congr 1
        omega
  | succ b ih =>
    rw [sourceRoleTerm_succ,abs_mul,sourceLeafProduct_succ]
    apply (mul_le_mul_of_nonneg_right
      (occupiedRootWeight_abs_le_one T s (b+1) S a _) (abs_nonneg _)).trans
    rw [one_mul,Finset.abs_prod]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro i hi
    exact ih _ _ _ _

theorem le_mul_of_zero_one {x a b : ℝ} (ha : a=0 ∨ a=1) (hb : b=0 ∨ b=1)
    (hxa : x≤a) (hxb : x≤b) : x≤a*b := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num at * <;> assumption

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem motifIndicator_pair_close (s : ℕ) (a c X : ℤ)
    (ha : motifIndicator s (a-X)≠0) (hc : motifIndicator s (c-X)≠0) :
    |a-c|<(2^s:ℕ) := by
  have hsa : 0≤a-X ∧ a-X<(2^s:ℕ) := by
    by_contra h
    exact ha (by simp only [motifIndicator,ite_eq_right h])
  have hsc : 0 ≤ c-X ∧ c-X<(2^s:ℕ) := by
    by_contra h
    exact hc (by simp only [motifIndicator,ite_eq_right h])
  exact abs_lt.mpr ⟨by omega,by omega⟩

theorem nonzero_of_abs_le {x y : ℝ} (h : x≠0) (hle : |x|≤y) : y≠0 := by
  intro hy
  rw [hy] at hle
  exact h (abs_eq_zero.mp (le_antisymm hle (abs_nonneg x)))

/-- A nonzero literal role multiplier enforces all close-child restrictions
of every forced subtree chosen from its fixed role pattern. -/
theorem sourceRoleTerm_forced_close (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (h : sourceRoleTerm T n g s center globalShift b bits incoming S a≠0) :
    BinaryWindowLabels.close T s (b+1) (forcedWindowLabels T b S a F) := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero] at h
      change |((S.equivFin.symm i).val.1.val:ℤ)-(S.equivFin.symm j).val.1.val|<(2^s:ℕ) ∧ True ∧ True
      refine ⟨?_,trivial,trivial⟩
      exact motifIndicator_pair_close s _ _ _
        (nonzero_of_abs_le h (occupiedRootWeight_bottom_anchor T s S a _ i))
        (nonzero_of_abs_le h (occupiedRootWeight_bottom_anchor T s S a _ j))
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ] at h
      have hm := mul_ne_zero_iff.mp h
      have hc := Finset.prod_ne_zero_iff.mp hm.2
      change |(((selectedChildren S).equivFin.symm i).val.val:ℤ)-
        ((selectedChildren S).equivFin.symm j).val.val|<(2^s:ℕ) ∧
        BinaryWindowLabels.close T s (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
            (a.1 i) left) ∧
        BinaryWindowLabels.close T s (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
            (a.1 j) right)
      refine ⟨?_,ih _ _ _ _ left (hc i (Finset.mem_univ i)),
        ih _ _ _ _ right (hc j (Finset.mem_univ j))⟩
      exact motifIndicator_pair_close s _ _ _
        (nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ i hi))
        (nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ j hj))

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem sum_finIntegerLabels (N : ℕ) (f : ℤ → ℝ) :
    (∑a∈finIntegerLabels N,f a)=∑i : Fin N,f i.val := by
  rw [finIntegerLabels,Finset.sum_image]
  intro a ha b hb he
  apply Fin.ext
  change (a.val:ℤ)=(b.val:ℤ) at he
  exact_mod_cast he

theorem sum_close_finIntegerLabels (N L : ℕ) (a : ℤ) (f : ℤ → ℝ) :
    (∑c∈closeLabels (finIntegerLabels N) L a,f c) =
      ∑i : Fin N, if |(i.val:ℤ)-a|<(L:ℤ) then f i.val else 0 := by
  rw [closeLabels,Finset.sum_filter,sum_finIntegerLabels]

/-- Any deterministic plateau/distinctness restriction can be retained in
child-pair summation. Only closeness is used to upper bound its cost. -/
theorem localAnchor_finite_energy {m N : ℕ} (d : Fin m → Option Bool) (s : ℕ)
    (c : ℤ) (R : Fin N → Fin N → Prop) [DecidableRel R]
    (hR : ∀a b,R a b → |(b.val:ℤ)-a.val|<(2^s:ℕ)) :
    (∑a : Fin N, ∑b : Fin N, if R a b then localAnchorAverage d s ((a.val:ℤ)-c)^2 else 0) ≤
      2*((2^s:ℕ):ℝ)^3*binomialBound (∑i,hiddenTrial (d i)) := by
  have H := root_anchor_energy (∑i,hiddenTrial (d i)) (2^s)
    (finIntegerLabels N) (finIntegerLabels N) (c-(∑i,(visibleOnes (d i):ℤ)))
  rw [sum_finIntegerLabels] at H
  simp_rw [sum_close_finIntegerLabels] at H
  calc
    _ ≤ ∑a : Fin N, ∑b : Fin N,
        if |(b.val:ℤ)-a.val|<(2^s:ℕ) then
          windowKernel (∑i,hiddenTrial (d i)) (2^s)
            ((a.val:ℤ)-(c-∑i,(visibleOnes (d i):ℤ)))^2 else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases h : R a b
      · rw [ite_eq_left h,ite_eq_left (hR a b h),localAnchorAverage_kernel]
        convert le_refl _ using 1 ; congr 2 ; omega
      · rw [ite_eq_right h]
        split_ifs <;> positivity
    _ ≤ _ := H

/-- Actual shared-jitter energy over two finite sibling pairs. Parent-label
plateau restrictions are discharged before applying this lemma; arbitrary
restrictions on these child pairs are kept, not conditioned on. -/
theorem posteriorJoint_finite_energy {mg m₁ m₂ N : ℕ}
    (dg : Fin mg → Option Bool) (d₁ : Fin m₁ → Option Bool) (d₂ : Fin m₂ → Option Bool)
    (s : ℕ) (c₁ c₂ : ℤ) (R : Fin N → Fin N → Prop) [DecidableRel R]
    (hR : ∀a b,R a b → |(b.val:ℤ)-a.val|<(2^s:ℕ)) :
    (∑a : Fin N, ∑c : Fin N, ∑b : Fin N, ∑d : Fin N,
      if R a c ∧ R b d then
        posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0) ≤
       4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (dg i))*binomialBound (∑i,hiddenTrial (d₂ i)) := by
  have H := posterior_sibling_anchor_energy dg d₁ d₂ s
    (finIntegerLabels N) (finIntegerLabels N) (finIntegerLabels N) (finIntegerLabels N) c₁ c₂
  simp_rw [sum_finIntegerLabels,sum_close_finIntegerLabels] at H
  calc
    _ = ∑a : Fin N, ∑b : Fin N, ∑c : Fin N, ∑d : Fin N,
      if R a c ∧ R b d then
        posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ ≤ ∑a : Fin N, ∑b : Fin N, ∑c : Fin N,
      if |(c.val:ℤ)-a.val|<(2^s:ℕ) then
        ∑d : Fin N, if |(d.val:ℤ)-b.val|<(2^s:ℕ) then
          posteriorJointAnchors dg d₁ d₂ s ((a.val:ℤ)-c₁) ((b.val:ℤ)-c₂)^2 else 0
      else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      by_cases h : |(c.val:ℤ)-a.val|<(2^s:ℕ)
      · rw [ite_eq_left h]
        apply Finset.sum_le_sum
        intro d hd
        by_cases hr : R a c ∧ R b d
        · rw [ite_eq_left hr,ite_eq_left (hR b d hr.2)]
        · rw [ite_eq_right hr]
          split_ifs <;> positivity
      · rw [ite_eq_right h]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro d hd
        exact ite_eq_right (fun hr => h (hR a c hr.1))
    _ ≤ _ := H

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem binarySiblingAnchor_plateau (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (hu : u∈A (b+1)) (hv : v∈A (b+1)) (a c : Fin (T b)) :
    binarySiblingAnchor T n g s center globalShift b d u v a c =
      posteriorJointAnchors d.2.1 (d.2.2 u).1 (d.2.2 v).1 s
        ((a.val:ℤ)-(center b+shift (b+1))) ((c.val:ℤ)-(center b+shift (b+1))) := by
  calc
    _ = (posteriorArray d.2.1).expect (fun glob =>
        localAnchorAverage (d.2.2 u).1 s ((a.val:ℤ)-center b+(∑i,(bitIndex (glob i):ℤ))-shift (b+1)) *
        localAnchorAverage (d.2.2 v).1 s ((c.val:ℤ)-center b+(∑i,(bitIndex (glob i):ℤ))-shift (b+1))) := by
      apply congrArg (FiniteLaw.expect (posteriorArray d.2.1))
      funext glob
      have hu' := hplat (b+1) glob u hu
      have hv' := hplat (b+1) glob v hv
      rw [hu',hv']
      congr 2 <;> omega
    _ = _ := by
      rw [localAnchor_pair_plateau]
      congr 1 <;> omega

theorem binaryDescendantEnergy_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u v : Fin (T b)) :
    0≤binaryDescendantEnergy T n g s center globalShift A b d u v := by
  induction b with
  | zero => exact zero_le_one
  | succ b ih =>
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro f hf
    split_ifs
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (ih _ _ _)) (ih _ _ _)
    · exact le_refl _

/-- True common-jitter energy at one group, with its exact finite domains. -/
theorem binarySiblingAnchor_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1))
    (u v : Fin (T (b+1))) (hu : u∈A (b+1)) (hv : v∈A (b+1)) :
    (∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 else 0) ≤
      4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (d.2.1 i))*
        binomialBound (∑i,hiddenTrial ((d.2.2 v).1 i)) := by
  simp_rw [binarySiblingAnchor_plateau T n g s center globalShift A shift hplat b d u v hu hv]
  exact posteriorJoint_finite_energy d.2.1 (d.2.2 u).1 (d.2.2 v).1 s
    (center b+shift (b+1)) (center b+shift (b+1)) (anchorPairAllowed T A s b)
    (fun a c h => h.2.2.2)

/-- The complete bottom-up forced-label energy estimate. Its only numerical
inputs are actual metadata hidden-count binomial caps. The group bound
keeps one shared global kernel until AFTER squaring. -/
theorem binaryDescendantEnergy_le (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d)
    (u v : Fin (T b)) (hu : u∈A b) (hv : v∈A b) :
    binaryDescendantEnergy T n g s center globalShift A b d u v ≤
      binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
  let K : ℕ → ℝ := fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j
  have hK : ∀j,0≤K j := fun j => mul_nonneg (mul_nonneg (by positivity) (hC _)) (hB _)
  induction b with
  | zero => exact le_refl _
  | succ b ih =>
    have hbudget := binaryTreeBudget_nonneg K hK b
    have hgroup := binarySiblingAnchor_energy T n g s center globalShift A shift hplat b d u v hu hv
    have hnum : 4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (d.2.1 i))*
        binomialBound (∑i,hiddenTrial ((d.2.2 v).1 i)) ≤ K b := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hcap.2.1 (by positivity))
        (hcap.2.2 v).1 (by unfold binomialBound; positivity)
        (mul_nonneg (by positivity) (hC _))
    calc
      _ ≤ (∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b),
        if anchorPairAllowed T A s b a c ∧ anchorPairAllowed T A s b e f then
          binarySiblingAnchor T n g s center globalShift b d u v a e ^ 2 else 0) *
          (binaryTreeBudget K b)^2 := by
        simp only [binaryDescendantEnergy,Finset.sum_mul]
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro c hc
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro f hf
        split_ifs with hr
        · have hl := ih (d.2.2 u) (hcap.2.2 u) a c hr.1.1 hr.1.2.1
          have hh := ih (d.2.2 v) (hcap.2.2 v) e f hr.2.1 hr.2.2.1
          have hm := mul_le_mul hl hh
            (binaryDescendantEnergy_nonneg T n g s center globalShift A b (d.2.2 v) e f) hbudget
          have hf := mul_le_mul_of_nonneg_left hm
            (sq_nonneg (binarySiblingAnchor T n g s center globalShift b d u v a e))
          simpa only [K,pow_two,mul_assoc] using hf
        · simp only [zero_mul,le_refl]
      _ ≤ K b*(binaryTreeBudget K b)^2 :=
        mul_le_mul_of_nonneg_right (hgroup.trans hnum) (sq_nonneg _)
      _ = _ := rfl

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem BinaryWindowLabels.allowed_distinct (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b)))
    (s b : ℕ) (p : BinaryWindowLabels T b) (hp : allowed T A s b p) : distinct T b p := by
  induction b with
  | zero => trivial
  | succ b ih => exact ⟨hp.1.2.2.1,ih _ hp.2.1,ih _ hp.2.2⟩

theorem sum_binary_labels (T : ℕ → ℕ) (b : ℕ) (f : BinaryWindowLabels T (b+1) → ℝ) :
    (∑p, f p) = ∑a : Fin (T b) × Fin (T b),
      ∑p : BinaryWindowLabels T b × BinaryWindowLabels T b, f (joinBinaryLabels a p) := by
  let e : BinaryWindowLabels T (b+1) ≃
      (Fin (T b) × Fin (T b)) × (BinaryWindowLabels T b × BinaryWindowLabels T b) :=
    { toFun := fun p => ((p.1,p.2.1),(p.2.2.1,p.2.2.2))
      invFun := fun z => joinBinaryLabels z.1 z.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.sum_equiv e f (fun z => f (joinBinaryLabels z.1 z.2)) (fun _ => rfl)).trans
    (Fintype.sum_prod_type _)

/-- Exact finite tensor summation after preserving both deterministically
allowed label domains. No probabilistic independence is asserted here. -/
theorem sum_pair_tensor {α β σ τ : Type*} [Fintype α] [Fintype β] [Fintype σ] [Fintype τ]
    (R : α → Prop) (S : β → Prop) (P : σ → Prop) (Q : τ → Prop)
    [DecidablePred R] [DecidablePred S] [DecidablePred P] [DecidablePred Q]
    (K : α → β → ℝ) (f : α → σ → ℝ) (h : β → τ → ℝ) :
    (∑a,∑x,∑b,∑y, if R a ∧ P x ∧ S b ∧ Q y then K a b*f a x*h b y else 0) =
      ∑a,∑b,if R a ∧ S b then K a b*(∑x,if P x then f a x else 0)*
        (∑y,if Q y then h b y else 0) else 0 := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hr : R a
  · by_cases hs : S b
    · rw [ite_eq_left ⟨hr,hs⟩]
      simp only [Finset.sum_mul,Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hp : P x <;> by_cases hq : Q y <;> simp only [hr,hs,hp,hq,and_self,
        false_and,and_false,ite_true,ite_false,mul_zero,zero_mul]
    · simp only [hs,and_false,false_and,ite_false,Finset.sum_const_zero]
  · simp only [hr,false_and,ite_false,Finset.sum_const_zero]

/-- Literal sum over all descendant labels is the recursively compiled
sibling-group energy. This is the bridge from the actual anchor average to
bottom-up summation; no coefficient estimate is supplied as a hypothesis. -/
theorem binaryAnchorBelow_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u v : Fin (T b)) :
    (∑p : BinaryWindowLabels T b × BinaryWindowLabels T b,
      if BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2 then
        binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels (u,v) p) d ^ 2 else 0) =
      binaryDescendantEnergy T n g s center globalShift A b d u v := by
  induction b with
  | zero =>
    have hcard : Fintype.card (BinaryWindowLabels T 0) = 1 := rfl
    simp only [BinaryWindowLabels.allowed,binaryAnchorBelow,binaryDescendantEnergy,
      and_self,ite_true,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_prod,hcard,nsmul_eq_mul,
      mul_one,Nat.cast_one]
  | succ b ih =>
    rw [Fintype.sum_prod_type,sum_binary_labels]
    simp_rw [sum_binary_labels]
    have hpoint (a c : Fin (T b) × Fin (T b))
        (p q : BinaryWindowLabels T b × BinaryWindowLabels T b) :
        (if BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels a p) ∧
          BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels c q) then
          binaryAnchorBelow T n g s center globalShift (b+1)
            (joinBinaryLabels (u,v) (joinBinaryLabels a p,joinBinaryLabels c q)) d ^ 2 else 0) =
        (if anchorPairAllowed T A s b a.1 a.2 ∧
          (BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2) ∧
          anchorPairAllowed T A s b c.1 c.2 ∧
          (BinaryWindowLabels.allowed T A s b q.1 ∧ BinaryWindowLabels.allowed T A s b q.2) then
          binarySiblingAnchor T n g s center globalShift b d u v a.1 c.1 ^ 2 *
            binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels a p) (d.2.2 u) ^ 2 *
            binaryAnchorBelow T n g s center globalShift b (joinBinaryLabels c q) (d.2.2 v) ^ 2 else 0) := by
      simp only [BinaryWindowLabels.allowed,joinBinaryLabels,and_assoc,binaryAnchorBelow,binarySiblingAnchor]
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [sum_pair_tensor]
    simp_rw [ih]
    change _ = ∑a : Fin (T b),∑c : Fin (T b),∑e : Fin (T b),∑f : Fin (T b), _
    simp only [Fintype.sum_prod_type]

/-- The square-sum of actual anchor averages over all admissible forced
indices, including the root local smoothing cost exactly once. -/
theorem binaryAnchorAverage_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑p : BinaryWindowLabels T (b+1), if BinaryWindowLabels.allowed T A s (b+1) p then
      binaryAnchorAverage T n g s center globalShift (b+1) p d incoming ^ 2 else 0) =
      ∑u : Fin (T b),∑v : Fin (T b), if anchorPairAllowed T A s b u v then
        localAnchorAverage d.1 s ((u.val:ℤ)-center b+incoming)^2 *
          binaryDescendantEnergy T n g s center globalShift A b d u v else 0 := by
  rw [sum_binary_labels,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hr : anchorPairAllowed T A s b u v
  · rw [ite_eq_left hr,←binaryAnchorBelow_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hsub : BinaryWindowLabels.allowed T A s b p.1 ∧ BinaryWindowLabels.allowed T A s b p.2
    · have ha : BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels (u,v) p) := ⟨hr,hsub⟩
      rw [ite_eq_left ha,ite_eq_left hsub,binaryAnchorAverage_factor T n g s center globalShift _ _ _ _
        (BinaryWindowLabels.allowed_distinct T A s _ _ ha),mul_pow]
      rfl
    · have ha : ¬BinaryWindowLabels.allowed T A s (b+1) (joinBinaryLabels (u,v) p) := fun h => hsub h.2
      rw [ite_eq_right ha,ite_eq_right hsub,mul_zero]
  · rw [ite_eq_right hr]
    apply Finset.sum_eq_zero
    intro p hp
    exact ite_eq_right (fun h => hr h.1)

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Full finite forced-anchor squared coefficient budget, with the source
power of one local root cost and one correlated global/local cost per group.
This conclusion is about literal posterior averages and actual labels. -/
theorem binaryAnchorAverage_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    (∑p : BinaryWindowLabels T (b+1), if BinaryWindowLabels.allowed T A s (b+1) p then
      binaryAnchorAverage T n g s center globalShift (b+1) p d incoming ^ 2 else 0) ≤
        (2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
  let K : ℕ → ℝ := fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j
  have hK : ∀j,0≤K j := fun j => mul_nonneg (mul_nonneg (by positivity) (hC _)) (hB _)
  have hbudget := binaryTreeBudget_nonneg K hK b
  have hroot := localAnchor_finite_energy d.1 s (center b-incoming)
    (anchorPairAllowed T A s b) (fun a c h => h.2.2.2)
  have he (u : Fin (T b)) : (u.val:ℤ)-(center b-incoming)=(u.val:ℤ)-center b+incoming := by omega
  simp_rw [he] at hroot
  rw [binaryAnchorAverage_sum]
  calc
    _ ≤ (∑u : Fin (T b),∑v : Fin (T b),if anchorPairAllowed T A s b u v then
        localAnchorAverage d.1 s ((u.val:ℤ)-center b+incoming)^2 else 0) * binaryTreeBudget K b := by
      simp only [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      split_ifs with hr
      · exact mul_le_mul_of_nonneg_left
          (binaryDescendantEnergy_le T n g s center globalShift A shift hplat B C hB hC b d hcap
            u v hr.1 hr.2.1) (sq_nonneg _)
      · simp only [zero_mul,le_refl]
    _ ≤ (2*((2^s:ℕ):ℝ)^3*B b)*binaryTreeBudget K b := by
      apply mul_le_mul_of_nonneg_right _ hbudget
      exact hroot.trans (mul_le_mul_of_nonneg_left hcap.1 (by positivity))

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- A literal unsigned length-L translated motif admits at most L child
labels in any finite window, even when the intended motif does not fit. -/
theorem motifIndicator_finite_sum (s N : ℕ) (X : ℤ) :
    (∑h : Fin N,motifIndicator s ((h.val:ℤ)-X)) ≤ (2^s:ℕ) := by
  let A := Finset.univ.filter (fun h : Fin N => 0≤(h.val:ℤ)-X ∧ (h.val:ℤ)-X<(2^s:ℕ))
  have hc : A.card≤2^s := by
    have H := Finset.card_le_card_of_injOn (s:=A) (t:=Finset.range (2^s))
      (fun h : Fin N => ((h.val:ℤ)-X).toNat) ?_ ?_
    · simpa only [Finset.card_range] using H
    · intro h hh
      have h' := (Finset.mem_filter.mp hh).2
      apply Finset.mem_range.mpr
      dsimp only
      omega
    · intro h hh j hj he
      have h' := (Finset.mem_filter.mp hh).2
      have j' := (Finset.mem_filter.mp hj).2
      apply Fin.ext
      dsimp only at he
      omega
  have he : (∑h : Fin N,motifIndicator s ((h.val:ℤ)-X)) = (A.card:ℝ) := by
    simp only [motifIndicator,A,Finset.sum_ite,Finset.sum_const_zero,add_zero,
      Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  exact_mod_cast hc

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Shapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shapes

Global schedules, edge labels, forced/extra coordinate splitting, finite shape codes, and occupied-label counts.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem centralThird_active (N : ℕ) (u : Fin N) (hu : u∈centralThird N)
    (v : Fin (N/4)) : v.val≤u.val ∧ u.val+v.val<N := by
  have huu := (Finset.mem_filter.mp hu).2
  have hv := v.isLt
  have hd := Nat.mod_add_div N 4
  have hm := Nat.mod_lt N (by omega : 0<4)
  omega

theorem globalTrial_sum (N t : ℕ) (f : Fin ((N/4)*t) → ℤ) :
    (∑v : Fin (N/4),∑a : Fin t,f (globalTrialIndex N t v a)) = ∑i,f i := by
  let e := Equiv.ofBijective _ (globalTrialIndex_bijective N t)
  have h := e.sum_comp f
  simpa only [e,Fintype.sum_prod_type,Equiv.ofBijective_apply] using h

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

theorem edgeCount_leaf (h : ℕ) : edgeCount OccupiedParityTree.leaf h=0 := by
  unfold edgeCount
  exact Fintype.card_eq_zero_iff.mpr ⟨fun e => e.val.elim⟩

theorem edgeCount_node {b n : ℕ} (children : Fin n → OccupiedParityTree b)
    (roles : Fin n → Fin 3) (h : ℕ) :
    edgeCount (.node n children roles) h = (if b=h then n else 0)+∑i,edgeCount (children i) h := by
  unfold edgeCount
  simp only [Fintype.card_subtype, Finset.card_filter]
  change (∑e : Fin n ⊕ ((i : Fin n) × (children i).Edge),if Edge.height (t := .node n children roles) e=h then 1 else 0)=_
  rw [Fintype.sum_sum_type]
  simp only [Edge.height,Fintype.sum_sigma]

  split_ifs <;> simp_all <;> simp only [Finset.card_filter] <;> rfl

theorem edgeCount_outside {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) (hh : b≤h) :
    t.edgeCount h=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun e => ?_⟩
  have hc := e.val.height_lt
  rw [e.property] at hc
  omega

theorem edgeCount_level {b : ℕ} (t : OccupiedParityTree b) (h : ℕ) (hh : h<b) :
    t.edgeCount h=t.levelCount (b-h) := by
  induction t with
  | leaf => omega
  | @node b n children roles ih =>
    rw [edgeCount_node]
    by_cases he : h=b
    · subst h
      have hz (i : Fin n) := edgeCount_outside (children i) b le_rfl
      simp only [hz,Finset.sum_const_zero,add_zero,Nat.add_sub_cancel_left,
        levelCount,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
      rfl
    · have hh' : h<b := by omega
      have hd : b+1-h=(b-h)+1 := by omega
      rw [ite_eq_right (Ne.symm he),zero_add,hd]
      exact Finset.sum_congr rfl (fun i _ => ih i hh')

theorem Forced.restrict_labels (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : binaryLabelsEquiv T b (F.restrict T x)=F.labels T x := by
  induction F with
  | leaf => rfl
  | @node b n children roles a c hne ha hc left right ihl ihr =>
    change (x (Sum.inl a),x (Sum.inl c),_,_) = (x (Sum.inl a),x (Sum.inl c),_,_)
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
    · exact ihl (x.child T a)
    · exact ihr (x.child T c)

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

theorem Forced.labelsEquiv_fst (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (x : t.Labels T) : (F.labelsEquiv T x).1=F.labels T x := by
  exact F.restrict_labels T x

end OccupiedParityTree
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- Every ancestor label of an extra selected leaf is an interior label. -/
theorem Edge.parentPath_congr (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (x y : t.Labels T) (h : ∀e : t.Edge, e.height≠0 → (x e).val=(y e).val)
    (e : t.Edge) : e.parentPath T x=e.parentPath T y := by
  induction t with
  | leaf => exact e.elim
  | @node b n children roles ih =>
    cases e with
    | inl i => rfl
    | inr z =>
      have hb : b≠0 := by have := z.2.height_lt; omega
      change (x (Sum.inl z.1)).val :: _ = (y (Sum.inl z.1)).val :: _
      congr 1
      · exact h (Sum.inl z.1) hb
      · exact ih z.1 (x.child T z.1) (y.child T z.1)
          (fun e he => h (Sum.inr ⟨z.1,e⟩) he) z.2

theorem Forced.labels_value_eq (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x y : t.Labels T) (h : F.labels T x=F.labels T y) (j : BinaryEdge b) :
    (x (F.edge j)).val=(y (F.edge j)).val := by
  have hh := (binaryLabelsEquiv T b).injective
    ((F.restrict_labels T x).trans (h.trans (F.restrict_labels T y).symm))
  exact congrArg (fun z : BinaryEdgeLabels T b => (z j).val) hh

theorem Forced.fullLabelsEquiv_fst (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) : (F.fullLabelsEquiv T x).1=F.labels T x :=
  F.labelsEquiv_fst T x

theorem Forced.fullLabelsEquiv_leaf_value (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) (e : F.ExtraLeafEdge) :
    ((F.fullLabelsEquiv T x).2.1 e).val=(x e.val.val).val := rfl

theorem Forced.fullLabelsEquiv_interior_value (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (x : t.Labels T) (e : F.ExtraInteriorEdge) :
    ((F.fullLabelsEquiv T x).2.2 e).val=(x e.val.val).val := rfl

/-- Changing only extra leaf labels changes no ancestor address, even when
all the complete-tree mechanisms share their source global bits. -/
theorem Forced.parentPath_extraLeaf_invariant (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (F : t.Forced) (p : BinaryWindowLabels T b) (h k : F.ExtraLeafEdge → Fin (T 0))
    (z : F.InteriorLabels T) (e : t.Edge) :
    e.parentPath T ((F.fullLabelsEquiv T).symm (p,h,z)) =
      e.parentPath T ((F.fullLabelsEquiv T).symm (p,k,z)) := by
  let x := (F.fullLabelsEquiv T).symm (p,h,z)
  let y := (F.fullLabelsEquiv T).symm (p,k,z)
  have hx : F.fullLabelsEquiv T x=(p,h,z) := Equiv.apply_symm_apply _ _
  have hy : F.fullLabelsEquiv T y=(p,k,z) := Equiv.apply_symm_apply _ _
  have hp : F.labels T x=F.labels T y := by
    rw [←F.fullLabelsEquiv_fst,←F.fullLabelsEquiv_fst,hx,hy]
  apply Edge.parentPath_congr T x y
  intro i hi
  by_cases hr : i∈Set.range F.edge
  · obtain ⟨j,rfl⟩ := hr
    exact F.labels_value_eq T x y hp j
  · let j : F.ExtraInteriorEdge := ⟨⟨i,hr⟩,hi⟩
    have hvx := congrArg (fun a => (a.2.2 j).val) hx
    have hvy := congrArg (fun a => (a.2.2 j).val) hy
    have hv := hvx.trans hvy.symm
    simpa only [Forced.fullLabelsEquiv_interior_value] using hv

end OccupiedParityTree
end TraceReconstruction

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem indexedExtraAverage_nonneg {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ)
    (h : E → Fin N) : 0 ≤ indexedExtraAverage P s N f X h := by
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg (P.nonneg ω)
  exact mul_nonneg (hf ω) (Finset.prod_nonneg (fun j _ => motifIndicator_nonneg _ _))

theorem indexedExtraAverage_sum {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ) :
    (∑h : E → Fin N,indexedExtraAverage P s N f X h) ≤
      ((2^s:ℕ):ℝ)^(Fintype.card E)*P.expect f := by
  unfold indexedExtraAverage expect
  rw [Finset.sum_comm]
  simp_rw [←mul_assoc,←Finset.mul_sum]
  calc
    _ ≤ ∑ω,P.mass ω*f ω*(((2^s:ℕ):ℝ)^(Fintype.card E)) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (P.nonneg _) (hf ω))
      have he := Fintype.prod_sum (fun (j : E) (h : Fin N) => motifIndicator s ((h.val:ℤ)-X ω j))
      rw [←he]
      calc
        _ ≤ ∏_j : E,((2^s:ℕ):ℝ) := by
          apply Finset.prod_le_prod
          · intro j hj
            exact Finset.sum_nonneg (fun h hh => motifIndicator_nonneg _ _)
          · intro j hj
            exact motifIndicator_finite_sum s N (X ω j)
        _ = _ := by simp
    _ = _ := by rw [←Finset.sum_mul]; ring

theorem indexedExtraAverage_energy {Ω E : Type*} [Fintype Ω] [Fintype E] (P : FiniteLaw Ω)
    (s N : ℕ) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (X : Ω → E → ℤ) :
    (∑h : E → Fin N,indexedExtraAverage P s N f X h ^ 2) ≤
      ((2^s:ℕ):ℝ)^(2*Fintype.card E)*(P.expect f)^2 := by
  have hn (h : E → Fin N) := indexedExtraAverage_nonneg P s N f hf X h
  calc
    _ ≤ (∑h : E → Fin N,indexedExtraAverage P s N f X h)^2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun h _ => hn h)
    _ ≤ (((2^s:ℕ):ℝ)^(Fintype.card E)*P.expect f)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun h _ => hn h))
      exact indexedExtraAverage_sum P s N f hf X
    _ = _ := by rw [mul_pow,←pow_mul]; congr 2; omega
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open OccupiedParityTree

theorem occupiedTermLabels_forced (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    F.labels T (occupiedTermLabels T b S a)=forcedWindowLabels T b S a F := by
  induction b with
  | zero =>
    cases F with
    | node i j hne hi hj left right => cases left; cases right; rfl
  | succ b ih =>
    rcases a with ⟨u,r⟩
    cases F with
    | node i j hne hi hj left right =>
      change
        (((selectedChildren S).equivFin.symm i).val,
         ((selectedChildren S).equivFin.symm j).val,
         left.labels T (occupiedTermLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm i).val) (u i)),
         right.labels T (occupiedTermLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm j).val) (u j))) =
        (((selectedChildren S).equivFin.symm i).val,
         ((selectedChildren S).equivFin.symm j).val,
         forcedWindowLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm i).val) (u i) left,
         forcedWindowLabels T b (selectedChildLeaves S
           ((selectedChildren S).equivFin.symm j).val) (u j) right)
      exact congrArg (fun z => (((selectedChildren S).equivFin.symm i).val,
        ((selectedChildren S).equivFin.symm j).val,z)) (Prod.ext (ih _ _ left) (ih _ _ right))

theorem mem_selectedChildLeaves {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α×β)) (h : α) (v : β) : v∈selectedChildLeaves S h ↔ (h,v)∈S := by
  constructor
  · intro hm
    obtain ⟨w,hw,hv⟩ := Finset.mem_image.mp hm
    have he : w=(h,v) := Prod.ext (Finset.mem_filter.mp hw).2 hv
    exact he ▸ (Finset.mem_filter.mp hw).1
  · intro hm
    exact Finset.mem_image.mpr ⟨(h,v),Finset.mem_filter.mpr ⟨hm,rfl⟩,rfl⟩

theorem occupiedTermLabels_leaves (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    (occupiedWindowTerm T b S a).labelledLeaves T (occupiedTermLabels T b S a)=S := by
  induction b with
  | zero =>
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨w,hw,hvw⟩ := Finset.mem_image.mp hv
      have he : (S.equivFin.symm i).val=v := by
        apply Prod.ext
        · change (occupiedTermLabels T 0 S a (Sum.inl i)) = v.1
          have hfst := congrArg (Prod.fst : Fin (T 0) × Fin 1 → Fin (T 0)) hvw
          exact hfst
        · exact Subsingleton.elim (α := Fin 1) _ _
      exact he ▸ (S.equivFin.symm i).property
    · intro hv
      let i := S.equivFin ⟨v,hv⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(⟨0,by decide⟩ : Fin 1),Finset.mem_singleton_self _,?_⟩
      change ((S.equivFin.symm i).val.1,(⟨0,by decide⟩ : Fin 1))=v
      have he : (S.equivFin.symm i).val=v := congrArg Subtype.val (S.equivFin.symm_apply_apply _)
      apply Prod.ext
      · change (S.equivFin.symm i).val.1=v.1
        exact congrArg (Prod.fst : Fin (T 0) × Fin 1 → Fin (T 0)) he
      · exact Subsingleton.elim (α := Fin 1) _ _
  | succ b ih =>
    rcases a with ⟨u,r⟩
    simp only [occupiedWindowTerm, labelledLeaves, occupiedTermLabels, Labels.node]
    have hc (i : Fin (selectedChildren S).card) :
        (Labels.node T (roles := r) (fun i => ((selectedChildren S).equivFin.symm i).val)
          (fun i => occupiedTermLabels T b (selectedChildLeaves S
            ((selectedChildren S).equivFin.symm i).val) (u i))).child T i =
        occupiedTermLabels T b (selectedChildLeaves S
            ((selectedChildren S).equivFin.symm i).val) (u i) := by rfl
    simp_rw [hc,ih]
    ext v
    constructor
    · intro hv
      obtain ⟨i,hi,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (mem_selectedChildLeaves _ _ _).mp hw
    · intro hv
      have hc : v.1∈selectedChildren S := Finset.mem_image.mpr ⟨v,hv,rfl⟩
      let i := (selectedChildren S).equivFin ⟨v.1,hc⟩
      have he : ((selectedChildren S).equivFin.symm i).val=v.1 :=
        congrArg Subtype.val ((selectedChildren S).equivFin.symm_apply_apply _)
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨v.2,?_,?_⟩
      · rw [he]
        exact (mem_selectedChildLeaves _ _ _).mpr hv
      · exact Prod.ext he rfl

/-- The shape remembers all the role choices once the actual selected set
is fixed. -/
theorem occupiedWindowTerm_injective (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) : Function.Injective (occupiedWindowTerm T b S) := by
  induction b with
  | zero =>
    intro a c h
    exact eq_of_heq (OccupiedParityTree.node.inj h).2.2
  | succ b ih =>
    intro a c h
    apply Prod.ext
    · funext i
      exact ih _ ((congrFun (eq_of_heq (OccupiedParityTree.node.inj h).2.1) i))
    · exact eq_of_heq (OccupiedParityTree.node.inj h).2.2

theorem occupiedTermEncoding_injective (T : ℕ → ℕ) (b : ℕ) :
    Function.Injective (occupiedTermEncoding T b) := by
  intro w v he
  have hS := congrArg (fun z : (t : OccupiedParityTree (b+1)) × t.Labels T =>
    z.1.labelledLeaves T z.2) he
  change (occupiedWindowTerm T b w.1 w.2).labelledLeaves T (occupiedTermLabels T b w.1 w.2)=
    (occupiedWindowTerm T b v.1 v.2).labelledLeaves T (occupiedTermLabels T b v.1 v.2) at hS
  simp only [occupiedTermLabels_leaves] at hS
  cases w with
  | mk S a =>
    cases v with
    | mk V c =>
      dsimp only at hS
      subst V
      have ht := congrArg Sigma.fst he
      have ha := occupiedWindowTerm_injective T b S ht
      change a=c at ha
      subst c
      rfl
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

theorem BinaryEdge.height_lt {b : ℕ} (e : BinaryEdge b) : e.height<b := by
  induction b with
  | zero => exact e.elim
  | succ b ih =>
    cases e with
    | inl i => exact Nat.lt_succ_self _
    | inr z => exact Nat.lt_succ_of_lt (ih z.2)

theorem binaryEdgeCount_outside (b h : ℕ) (hh : b≤h) : binaryEdgeCount b h=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun e => ?_⟩
  have hc := e.val.height_lt
  rw [e.property] at hc
  omega

theorem binaryEdgeCount_succ (b h : ℕ) :
    binaryEdgeCount (b+1) h = (if b=h then 2 else 0)+2*binaryEdgeCount b h := by
  unfold binaryEdgeCount
  simp only [Fintype.card_subtype,Finset.card_filter]
  change (∑e : Bool ⊕ (Bool × BinaryEdge b), if BinaryEdge.height (b:=b+1) e=h then 1 else 0)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  by_cases hb : b=h <;> simp [BinaryEdge.height,hb,two_mul] <;> simp only [Finset.card_filter] <;> rfl

theorem binaryEdgeCount_eq (b h : ℕ) (hh : h<b) : binaryEdgeCount b h=2^(b-h) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rw [binaryEdgeCount_succ]
    by_cases he : b=h
    · subst h
      rw [ite_eq_left rfl,binaryEdgeCount_outside b b le_rfl]
      simp
    · rw [ite_eq_right he,zero_add,ih (by omega)]
      have hsub : b+1-h=(b-h)+1 := by omega
      rw [hsub,pow_succ,Nat.mul_comm]

theorem Forced.count_partition {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (h : ℕ) :
    F.extraCount h+binaryEdgeCount b h=t.edgeCount h := by
  have he := F.edgeEquiv.sum_comp (fun e : t.Edge => if e.height=h then (1:ℕ) else 0)
  rw [Fintype.sum_sum_type] at he
  change (∑e : BinaryEdge b, if (F.edge e).height=h then 1 else 0)+
    (∑e : F.ExtraEdge, if e.val.height=h then 1 else 0) =
      (∑e : t.Edge, if e.height=h then 1 else 0) at he
  simp_rw [F.edge_height] at he
  unfold Forced.extraCount binaryEdgeCount edgeCount
  simp only [Fintype.card_subtype,Finset.card_filter]
  omega

theorem levelCount_bottom {b : ℕ} (t : OccupiedParityTree b) : t.levelCount b=t.leafCount := by
  induction t with
  | leaf => rfl
  | node n children roles ih => exact Finset.sum_congr rfl (fun i _ => ih i)

/-- The extra bottom coordinates are precisely r-2^b, including the empty
height-zero case. -/
theorem Forced.card_extraLeafEdge {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) :
    Fintype.card F.ExtraLeafEdge=t.leafCount-2^b := by
  cases b with
  | zero =>
    cases t
    change F.extraCount 0 = _
    have h := F.count_partition 0
    rw [edgeCount_leaf] at h
    simp only [leafCount,pow_zero,Nat.sub_self]
    omega
  | succ b =>
    change F.extraCount 0 = _
    have h := F.count_partition 0
    rw [binaryEdgeCount_eq (b+1) 0 (by omega),edgeCount_level t 0 (by omega)] at h
    simp only [Nat.sub_zero,levelCount_bottom] at h
    omega

/-- Exact source nonforced vertex bound, now for genuine extra edge-label
coordinates rather than an abstract level-count surrogate. -/
theorem Forced.extraCount_le {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (h : ℕ) : F.extraCount h≤t.leafCount-2^b := by
  by_cases hh : h<b
  · have hp := F.count_partition h
    rw [binaryEdgeCount_eq b h hh,edgeCount_level t h hh] at hp
    have Hb := F.nonforced_vertices_le_extra_leaves ht (b-h)
    omega
  · have hp := F.count_partition h
    rw [edgeCount_outside t h (by omega)] at hp
    omega

theorem Forced.interiorFiber_le {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (ht : t.occupied) (h : Fin b) :
    Fintype.card {e : F.ExtraInteriorEdge // F.interiorHeight e=h} ≤ t.leafCount-2^b := by
  apply le_trans _ (F.extraCount_le ht h.val)
  let f : {e : F.ExtraInteriorEdge // F.interiorHeight e=h} →
      {e : F.ExtraEdge // e.val.height=h.val} := fun e =>
    ⟨e.val.val,congrArg Fin.val e.property⟩
  apply Fintype.card_le_of_injective f
  intro u v he
  have he' : u.val.val=v.val.val := congrArg
    (fun q : {e : F.ExtraEdge // e.val.height=h.val} => q.val) he
  exact Subtype.ext (Subtype.ext he')

theorem Forced.card_interiorLabels_le (T : ℕ → ℕ) (hT : ∀j,0<T j)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (ht : t.occupied) :
    Fintype.card (F.InteriorLabels T) ≤
      (∏j : Fin b,if j.val=0 then 1 else T j.val)^(t.leafCount-2^b) := by
  change Fintype.card ((e : F.ExtraInteriorEdge) → Fin (T e.val.val.height)) ≤ _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  have hp := Fintype.prod_fiberwise' F.interiorHeight (fun j : Fin b => T j.val)
  change (∏j : Fin b, ∏_e : {e : F.ExtraInteriorEdge // F.interiorHeight e=j}, T j.val) =
    ∏e : F.ExtraInteriorEdge,T e.val.val.height at hp
  rw [←hp]
  simp only [Finset.prod_const,Finset.card_univ]
  rw [←Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro j hj
  by_cases hz : j.val=0
  · have he : Fintype.card {e : F.ExtraInteriorEdge // F.interiorHeight e=j}=0 := by
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun e => ?_⟩
      exact e.val.property ((congrArg Fin.val e.property).trans hz)
    rw [he,ite_eq_left hz,pow_zero,one_pow]
  · rw [ite_eq_right hz]
    exact Nat.pow_le_pow_right (hT j.val) (F.interiorFiber_le ht j)

end OccupiedParityTree
end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy

Shaped envelopes, actual coefficient aggregation, role counts, central contributions, and full coefficient energy.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
namespace OccupiedParityTree

theorem Forced.averagedEnvelope_split (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (p : BinaryWindowLabels T b) (h : F.ExtraLeafEdge → Fin (T 0)) (z : F.InteriorLabels T)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    F.averagedEnvelope T n g s center globalShift ((F.fullLabelsEquiv T).symm (p,h,z)) d incoming =
      indexedExtraAverage (windowPosteriorLaw T n g b d) s (T 0)
        (fun bits => binaryAnchorKernel T n g s center globalShift b p bits incoming)
        (fun bits e => F.extraOffsets T n g hT center globalShift p z bits incoming e) h := by
  let x := (F.fullLabelsEquiv T).symm (p,h,z)
  have hx : F.fullLabelsEquiv T x=(p,h,z) := Equiv.apply_symm_apply _ _
  have hp : F.labels T x=p := by rw [←F.fullLabelsEquiv_fst,hx]
  apply congrArg (FiniteLaw.expect (windowPosteriorLaw T n g b d))
  funext bits
  change F.envelope T n g s center globalShift x bits incoming = _
  unfold Forced.envelope
  rw [hp]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hv := congrArg (fun a => (a.2.1 e).val) hx
  simp only [Forced.fullLabelsEquiv_leaf_value] at hv
  rw [hv]
  unfold Forced.extraOffsets
  congr 2
  exact congrArg (sourceTreeAnchors T n g center globalShift b bits incoming)
    (F.parentPath_extraLeaf_invariant T p h (fun _ => ⟨0,hT⟩) z e.val.val)

/-- Summing every actual numeric labeling of a fixed shape costs exactly
one l1-squared factor per extra leaf and one factor per extra interior label.
The forced-anchor energy remains a single genuine correlated posterior. -/
theorem Forced.envelope_energy (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (R : BinaryWindowLabels T b → Prop) [DecidablePred R]
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    (∑x : t.Labels T, if R (F.labels T x) then
      (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0) ≤
      (Fintype.card (F.InteriorLabels T):ℝ) * ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge) *
        ∑p : BinaryWindowLabels T b, if R p then
          (binaryAnchorAverage T n g s center globalShift b p d incoming)^2 else 0 := by
  let L := ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge)
  have hs := (F.fullLabelsEquiv T).symm.sum_comp (fun x : t.Labels T =>
    if R (F.labels T x) then (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0)
  rw [←hs]
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑p : BinaryWindowLabels T b, ∑z : F.InteriorLabels T,
        if R p then L*(binaryAnchorAverage T n g s center globalShift b p d incoming)^2 else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro z hz
      have he (h : F.ExtraLeafEdge → Fin (T 0)) :
          F.labels T ((F.fullLabelsEquiv T).symm (p,h,z))=p := by
        rw [←F.fullLabelsEquiv_fst,Equiv.apply_symm_apply]
      simp_rw [he]
      by_cases hR : R p
      · simp only [ite_eq_left hR]
        simp_rw [F.averagedEnvelope_split T n g hT s center globalShift]
        exact indexedExtraAverage_energy (windowPosteriorLaw T n g b d) s (T 0)
          (fun bits => binaryAnchorKernel T n g s center globalShift b p bits incoming)
          (fun bits => binaryAnchorKernel_nonneg T n g s center globalShift b p bits incoming)
          (fun bits e => F.extraOffsets T n g hT center globalShift p z bits incoming e)
      · simp only [ite_eq_right hR,Finset.sum_const_zero,le_refl]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hr : R p <;> simp [hr,L,mul_assoc]
/-- Connected forced-shape coefficient-envelope estimate with the true
common-global/local sibling energy, and no independent-sibling substitute. -/
theorem Forced.envelope_energy_root (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ)
    (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (t : OccupiedParityTree (b+1)) (F : t.Forced)
    (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    (∑x : t.Labels T, if BinaryWindowLabels.allowed T A s (b+1) (F.labels T x) then
      (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0) ≤
      ((Fintype.card (F.InteriorLabels T):ℝ) * ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge)) *
        ((2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b) := by
  apply (F.envelope_energy T n g hT s center globalShift
    (BinaryWindowLabels.allowed T A s (b+1)) d incoming).trans
  exact mul_le_mul_of_nonneg_left
    (binaryAnchorAverage_energy T n g s center globalShift A shift hplat B C hB hC b d hcap incoming)
    (by positivity)

end OccupiedParityTree
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

theorem Edge.bottomAddress_mem (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (x : t.Labels T) (e : t.Edge) (he : e.height=0) :
    e.bottomAddress T x he ∈ t.labelledLeaves T x := by
  induction t with
  | leaf => exact e.elim
  | @node b k children roles ih =>
    cases e with
    | inl i =>
      change b=0 at he
      subst b
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ i,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(⟨0,by decide⟩ : Fin 1),?_,rfl⟩
      have hz (u : OccupiedParityTree 0) (y : u.Labels T) :
          u.labelledLeaves T y = {(⟨0,by decide⟩ : Fin 1)} := by cases u; rfl
      rw [hz]
      exact Finset.mem_singleton_self _
    | inr z =>
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1,Finset.mem_univ _,?_⟩
      exact Finset.mem_image.mpr ⟨z.2.bottomAddress T (x.child T z.1) he, ih z.1 _ _ he,rfl⟩

/-- Leaf constraints read from the real shape label address are exactly the
ones in the genuine complete-tree latent law. -/
theorem Edge.bottomIndicator_eq (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (t : OccupiedParityTree (b+1)) (x : t.Labels T)
    (e : t.Edge) (he : e.height=0)
    (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ) :
    sourceBottomIndicator T n g s center globalShift b bits incoming (e.bottomAddress T x he) =
      motifIndicator s ((x e).val-sourceTreeAnchors T n g center globalShift (b+1) bits incoming
        (e.parentPath T x)) := by
  induction b generalizing incoming with
  | zero =>
    cases t with
    | node k children roles =>
      cases e with
      | inl i =>
        change motifIndicator s _ = motifIndicator s _
        congr 1
        change ((x (Sum.inl i)).val:ℤ)-center 0+(∑i,(bitIndex (bits.1 i):ℤ))+incoming =
          ((x (Sum.inl i)).val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)
        omega
      | inr z => have hh := z.2.height_lt; omega
  | succ b ih =>
    cases t with
    | node k children roles =>
      cases e with
      | inl i => change b+1=0 at he; omega
      | inr z =>
        change sourceBottomIndicator T n g s center globalShift b
          (bits.2.2 (x (Sum.inl z.1))) (globalShift (b+1) bits.2.1 (x (Sum.inl z.1)))
          (z.2.bottomAddress T (x.child T z.1) he) = motifIndicator s ((x.child T z.1 z.2).val-
          sourceTreeAnchors T n g center globalShift (b+1+1) bits incoming
            ((x (Sum.inl z.1)).val::z.2.parentPath T (x.child T z.1)))
        rw [sourceTreeAnchors_child T n g center globalShift (b+1) bits incoming
          (x (Sum.inl z.1)) (z.2.parentPath T (x.child T z.1))]
        exact ih _ _ _ he _ _

end OccupiedParityTree
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Taking repeated constraints from a zero-one product can only enlarge it.
The map need not be injective. This keeps the real leaf addresses, including
coincident labels in the ambient enlarged summation. -/
theorem product_zero_one_pull_le {α β : Type*} [Fintype β]
    (S : Finset α) (f : α → ℝ) (hf : ∀a∈S,f a=0 ∨ f a=1)
    (g : β → α) (hg : ∀b,g b∈S) : (∏a∈S,f a)≤∏b,f (g b) := by
  rcases prod_zero_one S f hf with hz | ho
  · rw [hz]
    exact Finset.prod_nonneg (fun b _ => by rcases hf (g b) (hg b) with h|h <;> simp [h])
  · have h (b : β) : f (g b)=1 := by
      rcases hf (g b) (hg b) with h|h
      · have hz := Finset.prod_eq_zero (hg b) h
        rw [ho] at hz
        norm_num at hz
      · exact h
    rw [ho]
    simp only [h,Finset.prod_const_one,le_refl]

/-- Every actual role coefficient is bounded by its actual forced shape
and extra-leaf envelope before averaging over the single whole latent law. -/
theorem sourceRoleTerm_envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      F.envelope T n g s center globalShift (occupiedTermLabels T b S a) bits incoming := by
  let x := occupiedTermLabels T b S a
  let f := sourceBottomIndicator T n g s center globalShift b bits incoming
  let addr : F.ExtraLeafEdge → WindowLeaf T (b+1) :=
    fun e => e.val.val.bottomAddress T x e.property
  have hm (e : F.ExtraLeafEdge) : addr e∈S := by
    rw [←occupiedTermLabels_leaves T b S a]
    exact e.val.val.bottomAddress_mem T x e.property
  have he (e : F.ExtraLeafEdge) : f (addr e)=motifIndicator s ((x e.val.val).val-
      sourceTreeAnchors T n g center globalShift (b+1) bits incoming (e.val.val.parentPath T x)) :=
    e.val.val.bottomIndicator_eq T n g s center globalShift b _ x e.property bits incoming
  have hle := product_zero_one_pull_le S f (fun v hv =>
    sourceBottomIndicator_zero_one T n g s center globalShift b bits incoming v) addr hm
  simp_rw [he] at hle
  apply le_mul_of_zero_one
    (binaryAnchorKernel_zero_one T n g s center globalShift _ _ bits incoming)
    (prod_zero_one Finset.univ _ (fun e _ => by unfold motifIndicator; split_ifs <;> simp))
  · simpa only [occupiedTermLabels_forced] using
      sourceRoleTerm_forced_anchor T n g s center globalShift b bits incoming S a F
  · exact (sourceRoleTerm_all_leaf_constraints T n g s center globalShift b bits incoming S a).trans hle

/-- The averaged coefficient uses one exact metadata fiber. No fit event,
plateau event or leaf-emission observation is conditioned on here. -/
theorem sourceRoleAverage_envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      F.averagedEnvelope T n g s center globalShift (occupiedTermLabels T b S a) d incoming := by
  apply ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
  exact FiniteLaw.expect_mono _ (fun bits =>
    sourceRoleTerm_envelope T n g s center globalShift b bits incoming S a F)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

theorem card_degreeForcedShape_le (b r : ℕ) :
    Fintype.card (DegreeForcedShape b r) ≤ shapeRoleConstant r b := by
  let f : DegreeForcedShape b r → FiniteRoleShape r b := fun t =>
    Classical.choose (exists_finiteRoleShape t.val r t.property.1 t.property.2.1.le)
  apply Fintype.card_le_of_injective f
  intro t u he
  apply Subtype.ext
  have ht := Classical.choose_spec (exists_finiteRoleShape t.val r t.property.1 t.property.2.1.le)
  have hu := Classical.choose_spec (exists_finiteRoleShape u.val r u.property.1 u.property.2.1.le)
  exact ht.symm.trans ((congrArg (FiniteRoleShape.toTree r b) he).trans hu)

theorem DegreeForcedRole.encoding_injective (T : ℕ → ℕ) (b r : ℕ) :
    Function.Injective (DegreeForcedRole.encoding T b r) := by
  intro w v he
  apply Subtype.ext
  apply occupiedTermEncoding_injective T b
  exact congrArg (fun z : (t : DegreeForcedShape (b+1) r) × t.val.Labels T =>
    (⟨z.1.val,z.2⟩ : (t : OccupiedParityTree (b+1)) × t.Labels T)) he

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

/-- The actual coefficient indices inject into shape+numeric-labels. Thus
summing the enlarged envelope really bounds the original coefficient sum,
with no identification of different selected monomials. -/
theorem degreeForcedRoleEnergy_le_envelopes (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming ≤
      ∑t : DegreeForcedShape (b+1) r, ∑x : t.val.Labels T,
        if BinaryWindowLabels.allowed T A s (b+1) (t.forced.labels T x) then
          (t.forced.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0 := by
  let f := fun z : (t : DegreeForcedShape (b+1) r) × t.val.Labels T =>
    if BinaryWindowLabels.allowed T A s (b+1) (z.1.forced.labels T z.2) then
      (z.1.forced.averagedEnvelope T n g s center globalShift z.2 d incoming)^2 else 0
  have hf : ∀z,0≤f z := by intro z; dsimp [f]; split_ifs <;> positivity
  calc
    _ ≤ ∑w : DegreeForcedRole T b r,f (w.encoding T b r) := by
      apply Finset.sum_le_sum
      intro w hw
      dsimp only [f,DegreeForcedRole.encoding]
      by_cases h : BinaryWindowLabels.allowed T A s (b+1)
          ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2))
      · simp only [ite_eq_left h]
        have hh := sourceRoleAverage_envelope T n g s center globalShift b d incoming
          w.val.1 w.val.2 (w.shape T b r).forced
        rw [←sq_abs (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)]
        exact (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
      · simp only [ite_eq_right h,le_refl]
    _ ≤ ∑z,f z := by
      simpa only [ite_true] using sum_injective_profile_le
        (DegreeForcedRole.encoding T b r) (DegreeForcedRole.encoding_injective T b r)
        (fun _ => True) (fun _ => trivial) f hf
    _ = _ := Fintype.sum_sigma _

theorem degreeForcedRoleEnergy_bound (T n g : ℕ → ℕ) (hT : ∀j,0<T j) (s : ℕ)
    (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b r : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming ≤
      (shapeRoleConstant r (b+1):ℝ) * interiorLabelBudget T b r *
        ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
        ((2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b) := by
  let K := interiorLabelBudget T b r * ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
    ((2*((2^s:ℕ):ℝ)^3*B b) * binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b)
  have hbud : 0≤binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
    exact binaryTreeBudget_nonneg _ (fun j =>
      mul_nonneg (mul_nonneg (by positivity) (hC (j+1))) (hB j)) b
  have hb := hB b
  have hK : 0≤K := by dsimp [K,interiorLabelBudget]; positivity
  calc
    _ ≤ ∑t : DegreeForcedShape (b+1) r, ∑x : t.val.Labels T,
        if BinaryWindowLabels.allowed T A s (b+1) (t.forced.labels T x) then
          (t.forced.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0 :=
      degreeForcedRoleEnergy_le_envelopes T n g s center globalShift A b r d incoming
    _ ≤ ∑_t : DegreeForcedShape (b+1) r,K := by
      apply Finset.sum_le_sum
      intro t ht
      apply (t.forced.envelope_energy_root T n g (hT 0) s center globalShift A shift hplat
        B C hB hC b t.val d hcap incoming).trans
      have hi := t.forced.card_interiorLabels_le T hT t.property.1
      rw [t.property.2.1] at hi
      have hi' : (Fintype.card (t.forced.InteriorLabels T):ℝ) ≤ interiorLabelBudget T b r := by
        dsimp [interiorLabelBudget]
        exact_mod_cast hi
      rw [t.forced.card_extraLeafEdge,t.property.2.1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi' (by positivity)) (by positivity)
    _ = (Fintype.card (DegreeForcedShape (b+1) r):ℝ)*K := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (shapeRoleConstant r (b+1):ℝ)*K := by
      apply mul_le_mul_of_nonneg_right _ hK
      exact_mod_cast card_degreeForcedShape_le (b+1) r
    _ = _ := by dsimp [K]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Total role multiplicity for one actual selected monomial. Every level
has at most the number of selected leaves; no ambient-label factor occurs. -/
theorem occupiedWindowChoice_card_le (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) :
    Fintype.card (OccupiedWindowChoice T b S) ≤ 3^((b+1)*S.card) := by
  induction b with
  | zero =>
    change Fintype.card (Fin S.card → Fin 3) ≤ _
    simp
  | succ b ih =>
    change Fintype.card (((i : Fin (selectedChildren S).card) →
      OccupiedWindowChoice T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)) ×
      (Fin (selectedChildren S).card → Fin 3)) ≤ _
    rw [Fintype.card_prod,Fintype.card_pi,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin]
    have hprod := Finset.prod_le_prod' (s:=Finset.univ) (fun i _ =>
      ih (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))
    have hs : (∑i : Fin (selectedChildren S).card,
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val).card)=S.card :=
      (selected_sum_index (selectedChildren S) (fun h => (selectedChildLeaves S h).card)).trans
        (selected_children_card S)
    have hc : (selectedChildren S).card≤S.card := Finset.card_image_le
    calc
      _ ≤ (∏i : Fin (selectedChildren S).card,
          3^((b+1)*(selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val).card)) *
          3^(selectedChildren S).card := Nat.mul_le_mul_right _ hprod
      _ = 3^((b+1)*S.card+(selectedChildren S).card) := by
        rw [Finset.prod_pow_eq_pow_sum,←Finset.mul_sum,hs,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simp only [Nat.add_mul,Nat.one_mul]; omega)

theorem degreeLeafSubset_card (T : ℕ → ℕ) (b r : ℕ) :
    Fintype.card (DegreeLeafSubset T b r)=(Fintype.card (WindowLeaf T (b+1))).choose r := by
  have h := Finset.card_powersetCard r (Finset.univ : Finset (WindowLeaf T (b+1)))
  have he : (Finset.univ.powersetCard r : Finset (Finset (WindowLeaf T (b+1))))=(Finset.univ.filter (fun S : Finset (WindowLeaf T (b+1)) => S.card=r)) := by
    ext S
    simp only [Finset.mem_powersetCard,Finset.subset_univ,true_and,Finset.mem_filter,Finset.mem_univ]
  rw [he,Finset.card_univ] at h
  rw [Fintype.card_subtype]
  exact h

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem BinaryWindowLabels.allowed_of_central (T : ℕ → ℕ)
    (A : (b : ℕ) → Finset (Fin (T b))) (s b : ℕ) (p : BinaryWindowLabels T b)
    (hc : central T A b p) (hd : distinct T b p) (hs : close T s b p) :
    allowed T A s b p := by
  induction b with
  | zero => trivial
  | succ b ih =>
    exact ⟨⟨hc.1,hc.2.1,hd.1,by simpa only [abs_sub_comm] using hs.1⟩,
      ih _ hc.2.2.1 hd.2.1 hs.2.1,ih _ hc.2.2.2 hd.2.2 hs.2.2⟩

theorem sourceRoleTerm_forced_central (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b)))
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (hc : SourceCentral T n g s center globalShift A (b+1) bits incoming)
    (hz : sourceRoleTerm T n g s center globalShift b bits incoming S a≠0) :
    BinaryWindowLabels.central T A (b+1) (forcedWindowLabels T b S a F) := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero] at hz
      change (S.equivFin.symm i).val.1 ∈ A 0 ∧ (S.equivFin.symm j).val.1 ∈ A 0 ∧ True ∧ True
      refine ⟨hc.1 _ ?_,hc.1 _ ?_,trivial,trivial⟩
      · convert nonzero_of_abs_le hz (occupiedRootWeight_bottom_anchor T s S a (center 0-(∑k,(bitIndex (bits.1 k):ℤ))-incoming) i) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ring
      · convert nonzero_of_abs_le hz (occupiedRootWeight_bottom_anchor T s S a (center 0-(∑k,(bitIndex (bits.1 k):ℤ))-incoming) j) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ring
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ] at hz
      have hm := mul_ne_zero_iff.mp hz
      have hp := Finset.prod_ne_zero_iff.mp hm.2
      change ((selectedChildren S).equivFin.symm i).val ∈ A (b+1) ∧
        ((selectedChildren S).equivFin.symm j).val ∈ A (b+1) ∧
        BinaryWindowLabels.central T A (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
            (a.1 i) left) ∧
        BinaryWindowLabels.central T A (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
            (a.1 j) right)
      refine ⟨hc.1 _ ?_,hc.1 _ ?_,
        ih _ _ _ _ left (hc.2 _) (hp i (Finset.mem_univ i)),
        ih _ _ _ _ right (hc.2 _) (hp j (Finset.mem_univ j))⟩
      · convert nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ i hi) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ring
      · convert nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ j hj) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ring

theorem sourceNoncentralMass_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    0 ≤ sourceNoncentralMass T n g s center globalShift A b d incoming := by
  exact Finset.sum_nonneg (fun bits _ => mul_nonneg
    ((windowPosteriorLaw T n g b d).nonneg bits) (by dsimp only; split_ifs <;> norm_num))

theorem sourceRoleAverage_not_allowed (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b)))
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (h : ¬BinaryWindowLabels.allowed T A s (b+1) (forcedWindowLabels T b S a F)) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      sourceNoncentralMass T n g s center globalShift A (b+1) d incoming := by
  apply ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
  apply FiniteLaw.expect_mono
  intro bits
  by_cases hc : SourceCentral T n g s center globalShift A (b+1) bits incoming
  · rw [ite_eq_left hc]
    have hz : sourceRoleTerm T n g s center globalShift b bits incoming S a=0 := by
      by_contra hn
      exact h (BinaryWindowLabels.allowed_of_central T A s (b+1) _
        (sourceRoleTerm_forced_central T n g s center globalShift A b bits incoming S a F hc hn)
        (forcedWindowLabels_distinct T b S a F)
        (sourceRoleTerm_forced_close T n g s center globalShift b bits incoming S a F hn))
    rw [hz,abs_zero]
  · rw [ite_eq_right hc]
    exact occupiedWindowWeight_abs_le_one T s _ b [] S a

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Extension by zero commutes with the finite subtype sum, including an
empty subtype and predicates depending on dependent role indices. -/
theorem sum_subtype_zero_extend {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f : {x // p x} → ℝ) :
    (∑x, if h : p x then f ⟨x,h⟩ else 0) = ∑x,f x := by
  have h := Fintype.sum_subtype_add_sum_subtype p
    (fun x => if h : p x then f ⟨x,h⟩ else 0)
  calc
    _ = (∑x : {x // p x}, if h : p x.val then f ⟨x.val,h⟩ else 0) +
        ∑x : {x // ¬p x}, if h : p x.val then f ⟨x.val,h⟩ else 0 := h.symm
    _ = (∑x,f x)+0 := congrArg₂ (·+·)
      (Finset.sum_congr rfl (fun x _ => dite_eq_left x.property))
      (Finset.sum_eq_zero (fun x _ => dite_eq_right x.property))
    _ = _ := add_zero _

theorem sourceCoefficient_expansion (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) :
    sourceCoefficient T n g s center globalShift b d incoming S =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then
          sourceRoleAverage T n g s center globalShift b d incoming S a else 0 := by
  unfold sourceCoefficient
  simp_rw [sourceTreeLeafSign_eq]
  exact occupiedWindow_averaged_difference _ T s _ b [] S

theorem sourceGoodRoleSquare_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (w : SourceRoleIndex T b) :
    0 ≤ sourceGoodRoleSquare T n g s center globalShift A b r d incoming w := by
  unfold sourceGoodRoleSquare
  split_ifs <;> positivity

theorem sourceGoodRoleSquare_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑w : SourceRoleIndex T b, sourceGoodRoleSquare T n g s center globalShift A b r d incoming w)=
      degreeForcedRoleEnergy T n g s center globalShift A b r d incoming := by
  unfold sourceGoodRoleSquare degreeForcedRoleEnergy
  exact sum_subtype_zero_extend
    (fun w : SourceRoleIndex T b => w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced)
    (fun w : DegreeForcedRole T b r => if BinaryWindowLabels.allowed T A s (b+1)
      ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)^2 else 0)

/-- Every actual odd role term is either smoothed at an actual singleton,
discarded by the literal central-layout failure event, or retained in the
forced-tree sum. There is no unproved coefficient-bound assumption. -/
theorem sourceRoleSquare_split (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (hS : S.card=r) (a : OccupiedWindowChoice T b S)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (if (occupiedWindowTerm T b S a).isOdd then
      sourceRoleAverage T n g s center globalShift b d incoming S a else 0)^2 ≤
      η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2+
        sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩ := by
  have hg := sourceGoodRoleSquare_nonneg T n g s center globalShift A b r d incoming ⟨S,a⟩
  by_cases ho : (occupiedWindowTerm T b S a).isOdd
  swap
  · rw [ite_eq_right ho]; nlinarith [sq_nonneg η, sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  rw [ite_eq_left ho]
  by_cases hz : sourceRoleAverage T n g s center globalShift b d incoming S a=0
  · rw [hz]; nlinarith [sq_nonneg η, sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  by_cases hn : (occupiedWindowTerm T b S a).noSingleton
  swap
  · have hs := sourceRoleAverage_singleton T n g s center globalShift b d incoming S a η hcap hn
    have hs2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hs)).mpr hs
    rw [sq_abs] at hs2
    nlinarith [sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  have hf := OccupiedParityTree.forced_nonempty (occupiedWindowTerm T b S a)
    (sourceRoleAverage_valid T n g s center globalShift b d incoming S a hz) hn ho
  let w : DegreeForcedRole T b r := ⟨⟨S,a⟩,hS,hf⟩
  let F : (occupiedWindowTerm T b S a).Forced := (w.shape T b r).forced
  change _ ≤ _+ (if h : S.card=r ∧ Nonempty (occupiedWindowTerm T b S a).Forced then _ else 0)
  rw [dite_eq_left ⟨hS,hf⟩]
  change _ ≤ _ + (if BinaryWindowLabels.allowed T A s (b+1)
    (F.labels T (occupiedTermLabels T b S a)) then _ else 0)
  rw [occupiedTermLabels_forced T b S a F]
  by_cases ha : BinaryWindowLabels.allowed T A s (b+1) (forcedWindowLabels T b S a F)
  · rw [ite_eq_left ha]; nlinarith [sq_nonneg η,
      sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  · rw [ite_eq_right ha]
    have hs := sourceRoleAverage_not_allowed T n g s center globalShift A b d incoming S a F ha
    have hs2 := (sq_le_sq₀ (abs_nonneg _) (sourceNoncentralMass_nonneg T n g s center globalShift A (b+1) d incoming)).mpr hs
    rw [sq_abs] at hs2
    nlinarith [sq_nonneg η]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem sourceGoodRoleSquare_degree_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑S : DegreeLeafSubset T b r, ∑a : OccupiedWindowChoice T b S.val,
      sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩)=
      degreeForcedRoleEnergy T n g s center globalShift A b r d incoming := by
  rw [←sourceGoodRoleSquare_sum,Fintype.sum_sigma]
  symm
  calc
    _ = ∑S : Finset (WindowLeaf T (b+1)), if h : S.card=r then
        ∑a : OccupiedWindowChoice T b S,
          sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : S.card=r
      · rw [dite_eq_left h]
      · simp [sourceGoodRoleSquare,h]
    _ = _ := sum_subtype_zero_extend
      (fun S : Finset (WindowLeaf T (b+1)) => S.card=r)
      (fun S : DegreeLeafSubset T b r => ∑a : OccupiedWindowChoice T b S.val,
        sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩)

theorem sourceCoefficient_square_bound (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (hS : S.card=r)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (sourceCoefficient T n g s center globalShift b d incoming S)^2 ≤
      4*(3^((b+1)*r):ℕ)*
        ((3^((b+1)*r):ℕ)*(η^2+
          (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
          ∑a : OccupiedWindowChoice T b S,
            sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩) := by
  let f : OccupiedWindowChoice T b S → ℝ := fun a =>
    if (occupiedWindowTerm T b S a).isOdd then
      sourceRoleAverage T n g s center globalShift b d incoming S a else 0
  let M : ℝ := (3^((b+1)*r):ℕ)
  let E : ℝ := η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2
  let G := fun a => sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hcard : (Fintype.card (OccupiedWindowChoice T b S):ℝ) ≤ M := by
    dsimp only [M]
    exact_mod_cast (hS ▸ occupiedWindowChoice_card_le T b S)
  have hcs : (∑a,f a)^2 ≤ (Fintype.card (OccupiedWindowChoice T b S):ℝ)*∑a,(f a)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) f
  have hs : (∑a,(f a)^2) ≤ M*E+∑a,G a := by
    calc
      _ ≤ ∑a : OccupiedWindowChoice T b S,(E+G a) :=
        Finset.sum_le_sum (fun a _ => sourceRoleSquare_split T n g s center globalShift A b r d incoming S hS a η hcap)
      _ = (Fintype.card (OccupiedWindowChoice T b S):ℝ)*E+∑a,G a := by simp [Finset.sum_add_distrib]
      _ ≤ M*E+∑a,G a := add_le_add (mul_le_mul_of_nonneg_right hcard hE) le_rfl
  calc
    _ = 4*(∑a,f a)^2 := by rw [sourceCoefficient_expansion]; dsimp only [f]; ring
    _ ≤ 4*((Fintype.card (OccupiedWindowChoice T b S):ℝ)*∑a,(f a)^2) := by linarith
    _ ≤ 4*(M*∑a,(f a)^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)
    _ ≤ 4*(M*(M*E+∑a,G a)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs hM) (by norm_num)
    _ = _ := by dsimp only [M,E,G]; ring

/-- The full degree coefficient sum, including every selected monomial,
singletons, and off-center labels. This is the finite, unabsorbed version
of the manuscript's low-degree coefficient estimate. -/
theorem sourceCoefficient_degree_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (∑S : DegreeLeafSubset T b r,
      (sourceCoefficient T n g s center globalShift b d incoming S.val)^2) ≤
      4*(3^((b+1)*r):ℕ)*
        (((Fintype.card (WindowLeaf T (b+1))).choose r:ℕ)*(3^((b+1)*r):ℕ)*
          (η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
          degreeForcedRoleEnergy T n g s center globalShift A b r d incoming) := by
  calc
    _ ≤ ∑S : DegreeLeafSubset T b r,
        4*(3^((b+1)*r):ℕ)*
          ((3^((b+1)*r):ℕ)*(η^2+
            (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
            ∑a : OccupiedWindowChoice T b S.val,
              sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩) :=
      Finset.sum_le_sum (fun S _ => sourceCoefficient_square_bound T n g s center globalShift A b r d incoming S.val S.property η hcap)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,sourceGoodRoleSquare_degree_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,degreeLeafSubset_card]
      ring

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section

noncomputable section


noncomputable section

noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

/-- Reorder independent emissions by the literal chronological slot order.
The order is a bijection, so no output is duplicated or silently discarded. -/
theorem indexedProduct_expect_equiv (P : ι → FiniteLaw α) (e : κ ≃ ι)
    (F : (ι → α) → ℝ) :
    (indexedProduct P).expect F=(indexedProduct (fun j => P (e j))).expect
      (fun x => F (fun i => x (e.symm i))) := by
  let E : (κ → α) ≃ (ι → α) :=
    { toFun := fun x i => x (e.symm i)
      invFun := fun x j => x (e j)
      left_inv := fun x => by funext j; simp
      right_inv := fun x => by funext i; simp }
  unfold expect indexedProduct
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏i,(P i).mass (x (e.symm i)))*F (fun i => x (e.symm i))=_
  congr 1
  rw [←e.prod_comp]
  simp only [Equiv.symm_apply_apply]

end FiniteLaw

end TraceReconstruction


noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem boolTypeSign_integerTemplate (N s : ℕ) (X : ℤ) (τ : Bool) (u : Fin N) :
    boolTypeSign (integerTemplateType N s X τ u)=motifChildSign s X u.val (boolTypeSign τ) := by
  have hτ : IsTypeSign (boolTypeSign τ) := by cases τ <;> norm_num [IsTypeSign,boolTypeSign]
  rcases motifChildSign_isSign s X u.val hτ with h | h <;>
    (simp only [integerTemplateType,h]; norm_num [boolTypeSign])

theorem sourceTreeLeafBool_sign (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (v : WindowLeaf T b) :
    boolTypeSign (sourceTreeLeafBool T n s center b bits incoming τ v)=
      sourceTreeLeafSign T n (sourceScheduledTrials T n) s center
        (sourceScheduledShift T n) b bits incoming (boolTypeSign τ) v := by
  induction b generalizing incoming τ with
  | zero => rfl
  | succ b ih =>
    change boolTypeSign (sourceTreeLeafBool T n s center b _ _ _ v.2)=_
    rw [ih,boolTypeSign_integerTemplate]
    rfl

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Metadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem windowPosterior_mass_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (bits : WindowAssignments T n g Bool b) :
    (windowPosteriorLaw T n g b d).mass bits=
      ∏i : WindowTrial T n g b,(FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i)).mass
          (windowAssignmentEquiv T n g Bool b bits i) := by
  induction b with
  | zero =>
    change (1:ℝ)=∏i : PEmpty,_
    simp
  | succ b ih =>
    change (∏i,(FiniteLaw.flagPosterior (d.1 i)).mass (bits.1 i))*
      ((∏i,(FiniteLaw.flagPosterior (d.2.1 i)).mass (bits.2.1 i))*
        ∏u,(windowPosteriorLaw T n g b (d.2.2 u)).mass (bits.2.2 u))=_
    simp_rw [ih]
    change _=∏i : Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b)),
      (FiniteLaw.flagPosterior (match i with
        | .inl k => d.1 k
        | .inr (.inl k) => d.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g (Option Bool) b (d.2.2 u) k)).mass
      (match i with
        | .inl k => bits.1 k
        | .inr (.inl k) => bits.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g Bool b (bits.2.2 u) k)
    simp only [Fintype.prod_sum_type,Fintype.prod_prod_type]

/-- Exact flat posterior distribution, including all paths and zero-mass
 metadata. This is the same independent bit law, not a new assumption. -/
theorem windowPosterior_expect_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b)
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g b d).expect F=
      (FiniteLaw.indexedProduct (fun i : WindowTrial T n g b => FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i))).expect
          (fun bits => F ((windowAssignmentEquiv T n g Bool b).symm bits)) := by
  unfold FiniteLaw.expect FiniteLaw.indexedProduct
  rw [←(windowAssignmentEquiv T n g Bool b).sum_comp]
  apply Finset.sum_congr rfl
  intro bits _
  dsimp only
  rw [Equiv.symm_apply_apply,windowPosterior_mass_flat]

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem expect_add (P : FiniteLaw α) (f g : α → ℝ) :
    P.expect (fun a => f a+g a)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

end FiniteLaw

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simulation

Canonical and filled simulations, central fit, root words, chronology, slots, finite codes, and complete-trace decoding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceAssignmentCode_eval (T n : ℕ → ℕ) (A : Type) (b : ℕ)
    (bits : Fin (SourceTrialCount T n b) → A) (j : Fin (SourceTrialCount T n b)) :
    windowAssignmentEquiv T n (sourceScheduledTrials T n) A b
      ((sourceAssignmentCode T n A b).symm bits) (finEnumeration _ j)=bits j := by
  change (sourceAssignmentCode T n A b ((sourceAssignmentCode T n A b).symm bits)) j=bits j
  rw [Equiv.apply_symm_apply]

end TraceReconstruction



end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact change of coordinates for the posterior of all hidden bits, not
 just separate local marginals. -/
theorem source_posterior_code_expect {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b))
    (F : WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℝ) :
    (PairedMechanisms.orientationsGiven z).expect
      (fun bits => F ((sourceAssignmentCode T n Bool b).symm bits)) =
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z)).expect F := by
  rw [windowPosterior_expect_flat,FiniteLaw.indexedProduct_expect_equiv _ (finEnumeration _)]
  simp only [sourceReportFlags,sourceAssignmentCode_eval]
  simp only [PairedMechanisms.orientationsGiven,FiniteLaw.expect,FiniteLaw.coordinateProduct,
    FiniteLaw.indexedProduct,sourceAssignmentCode,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr (by ext; simp)
  intro bits _
  rfl

theorem sourceSubsetCode_card (T : ℕ → ℕ) (b : ℕ)
    (σ : Fin (SourceLeafCount T b) → Bool) :
    (sourceSubsetCode T b σ).card=monomialDegree σ := by
  simp only [sourceSubsetCode,Equiv.trans_apply,Equiv.finsetCongr_apply,Finset.card_map]
  rfl

theorem selectionCoefficient_sign {k : ℕ} (θ σ : Fin k → Bool) :
    selectionCoefficient θ σ=∏j∈maskSubset σ,(1-boolTypeSign (θ j))/2 := by
  unfold selectionCoefficient maskSubset
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  cases σ j <;> cases θ j <;> norm_num [boolTypeSign]

theorem source_leaf_selection (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (σ : Fin (SourceLeafCount T b) → Bool) :
    selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center b bits incoming τ (finEnumeration _ j)) σ =
    ∏v∈sourceSubsetCode T b σ,
      (1-sourceTreeLeafSign T n (sourceScheduledTrials T n) s center
        (sourceScheduledShift T n) b bits incoming (boolTypeSign τ) v)/2 := by
  rw [selectionCoefficient_sign]
  simp only [sourceSubsetCode,Equiv.trans_apply,Equiv.finsetCongr_apply,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  rw [sourceTreeLeafBool_sign]
  rfl

/-- The real canonical-oracle coefficient difference is the exact source
 polynomial coefficient whose forced-tree energy has been proved. -/
theorem source_canonical_coefficient {Side : Type*} (T n : ℕ → ℕ) (s : ℕ)
    (center : ℕ → ℤ) (b : ℕ) (incoming : ℤ)
    (z : Reports Side (SourceTrialCount T n (b+1)))
    (σ : Fin (SourceLeafCount T (b+1)) → Bool) :
    averagedCoefficient (PairedMechanisms.orientationsGiven z)
      (sourceFlatLeafType T n s center (b+1) incoming false) σ -
    averagedCoefficient (PairedMechanisms.orientationsGiven z)
      (sourceFlatLeafType T n s center (b+1) incoming true) σ =
    sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      b (sourceReportFlags T n (b+1) z) incoming (sourceSubsetCode T (b+1) σ) := by
  unfold averagedCoefficient sourceFlatLeafType
  rw [source_posterior_code_expect T n (b+1) z
    (fun bits => selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center (b+1) bits incoming false (finEnumeration _ j)) σ),
    source_posterior_code_expect T n (b+1) z
    (fun bits => selectionCoefficient
      (fun j => sourceTreeLeafBool T n s center (b+1) bits incoming true (finEnumeration _ j)) σ)]
  simp_rw [source_leaf_selection]
  rfl

/-- Reindexing preserves the entire degree-r square sum, including zero
 and degrees larger than the number of real leaves. -/
theorem source_canonical_degree_sum {Side : Type*} (T n : ℕ → ℕ) (s : ℕ)
    (center : ℕ → ℤ) (b r : ℕ) (incoming : ℤ)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (∑σ : Fin (SourceLeafCount T (b+1)) → Bool, if monomialDegree σ=r then
      (averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s center (b+1) incoming false) σ -
       averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s center (b+1) incoming true) σ)^2 else 0) =
    ∑S : DegreeLeafSubset T b r,
      (sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
        b (sourceReportFlags T n (b+1) z) incoming S.val)^2 := by
  simp_rw [source_canonical_coefficient,←sourceSubsetCode_card]
  rw [(sourceSubsetCode T (b+1)).sum_comp
    (fun S => if S.card=r then (sourceCoefficient T n (sourceScheduledTrials T n) s center
      (sourceScheduledShift T n) b (sourceReportFlags T n (b+1) z) incoming S)^2 else 0)]
  let f : DegreeLeafSubset T b r → ℝ := fun S =>
    (sourceCoefficient T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      b (sourceReportFlags T n (b+1) z) incoming S.val)^2
  simpa only [f, dite_eq_ite] using
    sum_subtype_zero_extend (fun S : Finset (WindowLeaf T (b+1)) => S.card=r) f

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem hiddenBinomialCap_nonneg (m : ℕ) (ω : ℝ) : 0≤hiddenBinomialCap m ω :=
  Real.sqrt_nonneg _

theorem hidden_binomial_bound (m G : ℕ) (ω : ℝ)
    (h : (m:ℝ)*ω^2/2≤G) : binomialBound G≤hiddenBinomialCap m ω := by
  apply Real.sqrt_le_sqrt
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<G+1)
    (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  nlinarith

theorem hidden_smoothing_bound {m : ℕ} (d : Fin m → Option Bool) (s : ℕ) (ω : ℝ)
    (h : (m:ℝ)*ω^2/2≤∑i,(hiddenTrial (d i):ℝ)) :
    posteriorSmoothingCost s d≤hiddenSmoothingBound m s ω := by
  have hn : (m:ℝ)*ω^2/2≤((∑i,hiddenTrial (d i):ℕ):ℝ) := by simpa only [Nat.cast_sum] using h
  have hb : binomialBound ((∑i,hiddenTrial (d i))/(s+1))≤
      Real.sqrt (4*((s:ℝ)+1)/((m:ℝ)*ω^2+2)) := by
    apply (binomialBound_quotient_le _ s).trans
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<((∑i,hiddenTrial (d i):ℕ):ℝ)+1)
      (by positivity : (0:ℝ)<(m:ℝ)*ω^2+2)).mpr
    have hh := mul_le_mul_of_nonneg_left hn (by positivity : (0:ℝ)≤4*((s:ℝ)+1))
    nlinarith
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ)≤2^(s*s))
  have hnon : 0≤binomialBound ((∑i,hiddenTrial (d i))/(s+1)) := Real.sqrt_nonneg _
  exact mul_le_mul
    (pow_le_pow_left₀ (mul_nonneg (by norm_num) hnon) (mul_le_mul_of_nonneg_left hb (by norm_num)) s)
    hb hnon (by positivity)

/-- Hidden-count typicality implies every local/global anchor cap, for the
 actual source metadata and without a coefficient-dependent event. -/
theorem hiddenConditions_binomialCaps (T n g : ℕ → ℕ) (ω : ℝ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b)
    (h : HiddenCollectionConditions T n g ω b d) :
    MetadataBinomialCaps T n g (fun j => hiddenBinomialCap (n j) ω)
      (fun j => hiddenBinomialCap (g j) ω) b d := by
  induction b with
  | zero => trivial
  | succ b ih =>
    refine ⟨hidden_binomial_bound (n b) _ ω ?_,hidden_binomial_bound (g b) _ ω ?_,fun u => ih _ (h.2.2 u)⟩
    · simpa only [Nat.cast_sum] using h.1
    · simpa only [Nat.cast_sum] using h.2.1

theorem hiddenConditions_smoothingCap (T n g : ℕ → ℕ) (ω η : ℝ) (s b : ℕ)
    (hη : ∀j<b,hiddenSmoothingBound (n j) s ω≤η)
    (d : WindowAssignments T n g (Option Bool) b)
    (h : HiddenCollectionConditions T n g ω b d) :
    MetadataSmoothingCap T n g s η b d := by
  induction b with
  | zero => trivial
  | succ b ih =>
    exact ⟨(hidden_smoothing_bound d.1 s ω h.1).trans (hη b (by omega)),
      fun u => ih (fun j hj => hη j (by omega)) _ (h.2.2 u)⟩

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact common plateau with integer half-count centering. Unlike the
 simplified g/2 formula, this identity needs no parity assumption. -/
theorem scheduledGlobalShift_plateau_exact (N t : ℕ)
    (bits : Fin ((N/4)*t) → Bool) (u : Fin N) (hu : u∈centralThird N) :
    scheduledGlobalShift N t bits u = (∑i,(bitIndex (bits i):ℤ))-(N/4:ℕ)*(t/2:ℕ) := by
  calc
    _ = ∑v : Fin (N/4),
        ((∑a : Fin t, (bitIndex (bits (globalTrialIndex N t v a)):ℤ))-(t/2:ℕ)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact ite_eq_left (centralThird_active N u hu v)
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · exact globalTrial_sum N t (fun i => (bitIndex (bits i):ℤ))
      · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem sourceScheduledShift_hasPlateau (T n : ℕ → ℕ) :
    HasGlobalPlateau T (sourceScheduledTrials T n) (fun j => centralThird (T j))
      (sourcePlateauCenter T n) (sourceScheduledShift T n) := by
  intro b bits u hu
  cases b with
  | zero =>
      change (0:ℤ)=(∑i : Fin 0,(bitIndex (bits i):ℤ))-0
      simp
  | succ b => exact scheduledGlobalShift_plateau_exact (T (b+1)) (n b) bits u hu

theorem sourceForcedBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω : ℝ) :
    0 ≤ sourceForcedBudget T n s b r ω := by
  have hB := fun j => hiddenBinomialCap_nonneg (n j) ω
  have hC := fun j => hiddenBinomialCap_nonneg (sourceScheduledTrials T n j) ω
  have ht := binaryTreeBudget_nonneg (fun j => 4*((2^s:ℕ):ℝ)^6*
      hiddenBinomialCap (sourceScheduledTrials T n (j+1)) ω*hiddenBinomialCap (n j) ω)
    (fun j => mul_nonneg (mul_nonneg (by positivity) (hC (j+1))) (hB j)) b
  have hb := hB b
  unfold sourceForcedBudget interiorLabelBudget
  positivity

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Pointwise equality of the literal source types and the signed tree types.
 This holds for every assignment, including overflowing windows. -/
theorem sourceFlatLeafType_window (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (incoming : ℤ) (τ : Bool) (bits : Fin (SourceTrialCount T n b) → Bool) :
    sourceFlatLeafType T n s center b incoming τ bits =
      windowFinType T s (sourceTreeAnchors T n (sourceScheduledTrials T n) center
        (sourceScheduledShift T n) b ((sourceAssignmentCode T n Bool b).symm bits) incoming)
        b (boolTypeSign τ) := by
  funext j
  unfold sourceFlatLeafType windowFinType windowLeafType
  rw [←sourceTreeLeafSign_eq,←sourceTreeLeafBool_sign]
  change sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j)=
    decide (boolTypeSign (sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j))= -1)
  cases sourceTreeLeafBool T n s center b _ incoming τ (finEnumeration _ j) <;> norm_num [boolTypeSign]

theorem sourceFlatLeafType_sparse (T n : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (b : ℕ) (incoming : ℤ) (τ : Bool) (bits : Fin (SourceTrialCount T n (b+1)) → Bool) :
    monomialDegree (sourceFlatLeafType T n s center (b+1) incoming τ bits) ≤ sourceSparseCount T s b := by
  rw [sourceFlatLeafType_window,windowFinType_degree]
  exact windowMinusCount_bound T s _ b [] _

theorem sourceOracleCoefficient_empty {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    sourceOracleCoefficient T n s b z τ (fun _ => false)=1 := averagedCoefficient_empty _ _

theorem sourceOracleCoefficient_degree {Side : Type*} (T n : ℕ → ℕ) (s b r : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (∑σ, if monomialDegree σ=r then (sourceOracleCoefficient T n s b z τ σ)^2 else 0) ≤
      ((sourceSparseCount T s b).choose r:ℝ) :=
  averaged_sparse_degree _ _ (sourceFlatLeafType_sparse T n s _ b 0 τ) r

theorem sourceSignedCoefficient_zero {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) :
    (∑σ, if monomialDegree σ=0 then sourceSignedCoefficient T n s b z σ^2 else 0)=0 := by
  simp [monomialDegree_eq_zero_iff,sourceSignedCoefficient,sourceOracleCoefficient_empty]

theorem sourceSignedCoefficient_degree_geometric {Side : Type*} (T n : ℕ → ℕ) (s b r : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (w : ℝ) :
    w^(2*r)*(∑σ, if monomialDegree σ=r then sourceSignedCoefficient T n s b z σ^2 else 0) ≤
      4*(w^2*sourceSparseCount T s b)^r := by
  have h0 : 0 ≤ w^(2*r) := by rw [pow_mul]; positivity
  have hp := sourceOracleCoefficient_degree T n s b r z false
  have hm := sourceOracleCoefficient_degree T n s b r z true
  have hc : ((sourceSparseCount T s b).choose r:ℝ) ≤ (sourceSparseCount T s b:ℝ)^r := by
    exact_mod_cast Nat.choose_le_pow (sourceSparseCount T s b) r
  have hd := degree_square_sub_le (sourceOracleCoefficient T n s b z false)
    (sourceOracleCoefficient T n s b z true) r
  calc
    _ ≤ w^(2*r)*(4*(sourceSparseCount T s b:ℝ)^r) :=
      mul_le_mul_of_nonneg_left (by dsimp only [sourceSignedCoefficient]; linarith) h0
    _ = _ := by rw [pow_mul,mul_pow]; ring

theorem nonconstant_eq_degreeTail {l : ℕ} (A : (Fin l → Bool) → ℝ) :
    nonconstantCoefficient A=degreeTail A 1 := by
  funext σ
  by_cases h : σ=(fun _ => false)
  · subst σ; simp [nonconstantCoefficient,degreeTail,monomialDegree]
  · have hd : 1 ≤ monomialDegree σ := by
      have := (monomialDegree_eq_zero_iff σ).not.mpr h
      omega
    simp [nonconstantCoefficient,degreeTail,h,hd]

/-- The individual density is close to the pure reference without any
 metadata typicality assumption. -/
theorem source_canonical_centered_energy {Side : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) {w : ℝ} (hw : 0 ≤ w)
    (hsmall : w^2*sourceSparseCount T s b<1) :
    multilinearEnergy (nonconstantCoefficient (sourceOracleCoefficient T n s b z τ)) w ≤
      (w^2*sourceSparseCount T s b)/(1-w^2*sourceSparseCount T s b) := by
  rw [nonconstant_eq_degreeTail]
  simpa only [pow_one,sourceOracleCoefficient] using averaged_sparse_tail_energy _ _
    (sourceFlatLeafType_sparse T n s _ b 0 τ) 1 hw hsmall

end TraceReconstruction

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem density_score_centered (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀a,Q.mass a=P.mass a*(1+Z a)) : P.expect Z=0 := by
  have h := Q.total
  simp_rw [hZ,mul_add,mul_one,Finset.sum_add_distrib,P.total] at h
  change _+P.expect Z=1 at h
  linarith

/-- Common-event mass difference is controlled by the restricted density
 difference at every moment, by finite Jensen rather than a pointwise bound. -/
theorem clipping_mass_difference (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (t : ℕ) :
    |(R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A|^t ≤
      R.expect (fun a => |if a∈A then g a-f a else 0|^t) := by
  have he : (R.withDensity f hf hfm).eventMass A-(R.withDensity g hg hgm).eventMass A=
      -(R.expect (fun a => if a∈A then g a-f a else 0)) := by
    simp only [expect,mul_ite,mul_zero,←Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass,withDensity,mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [he,abs_neg]
  exact R.abs_expect_pow_le _ t

theorem clipped_raw_moment_restricted (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hfm : R.expect f=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hP : 0<(R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1)) ≤
      2^k/(R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |if a∈A then g a-f a else 0|^(k+1)) := by
  let g' : α → ℝ := fun a => if a∈A then g a else f a
  have H := clipped_raw_moment R f g' hf hfm A hAf hP k
  have he : (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1))=
      (condition (R.withDensity f hf hfm) A hP).expect (fun a => |g' a/f a-1|^(k+1)) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈A <;> simp [condition,g',ha]
  rw [he]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext a
  by_cases ha : a∈A <;> simp [g',ha]

/-- Explicit normalized clipping, at half of any positive even moment. This
 constructs the actual conditioned score; no bounded-score hypothesis. -/
theorem clipped_score_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (A : Finset α) (hAf : ∀a∈A,1/2 ≤ f a)
    (hp : 1/2 ≤ (R.withDensity f hf hfm).eventMass A)
    (hq : 1/2 ≤ (R.withDensity g hg hgm).eventMass A)
    (k : ℕ) (hk : 1 ≤ k) (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k) :
    let p := (R.withDensity f hf hfm).eventMass A
    let q := (R.withDensity g hg hgm).eventMass A
    let hP : 0 < p := lt_of_lt_of_le (by norm_num) hp
    (condition (R.withDensity f hf hfm) A hP).evenMomentSq (fun a => p/q*(g a/f a)-1) k ≤64*V := by
  dsimp only
  let p := (R.withDensity f hf hfm).eventMass A
  let q := (R.withDensity g hg hgm).eventMass A
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hp1 : p ≤ 1 := eventMass_le_one _ _
  have hratio : p/q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith)
  have hden : (1:ℝ)/p ≤ 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have ht : 2*k-1+1=2*k := by omega
  have hraw := clipped_raw_moment_restricted R f g hf hfm A hAf hp0 (2*k-1)
  rw [ht] at hraw
  have hraw' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |g a/f a-1|^(2*k)) ≤
      2^(2*k)*V^k := by
    apply hraw.trans
    calc
      _ ≤ (2^(2*k-1)/p)*V^k := mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ (2^(2*k-1)*2)*V^k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hV _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (2:ℝ)^(2*k-1))
      _ = _ := by rw [←pow_succ,ht]
  have hnorm : |p/q-1|^(2*k) ≤ 2^(2*k)*V^k := by
    rw [div_sub_one hq0.ne',abs_div,abs_of_pos hq0,div_pow]
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    have hd := (clipping_mass_difference R f g hf hg hfm hgm A (2*k)).trans hM
    have hqpow : 1 ≤ (2*q)^(2*k) := one_le_pow₀ (by linarith)
    calc
      _ ≤ V^k := hd
      _ ≤ (2*q)^(2*k)*V^k := by nlinarith [pow_nonneg hV k]
      _ = _ := by rw [mul_pow]; ring
  have hs := score_rescaling_moment (condition (R.withDensity f hf hfm) A hp0)
    (fun a => g a/f a) (p/q) (div_nonneg hp0.le hq0.le) (2*k-1)
  rw [ht] at hs
  have hpower : (p/q)^(2*k) ≤ (2:ℝ)^(2*k) :=
    pow_le_pow_left₀ (div_nonneg hp0.le hq0.le) hratio _
  have hs' : (condition (R.withDensity f hf hfm) A hp0).expect (fun a => |p/q*(g a/f a)-1|^(2*k)) ≤
      (64*V)^k := by
    apply hs.trans
    calc
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*V^k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul hpower hraw' (by
          apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) (by positivity)) hnorm
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*(2^(2*k)*V^k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        have htwo : (1:ℝ) ≤ 2^(2*k) := one_le_pow₀ (by norm_num)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo
          (by positivity : 0 ≤ (2:ℝ)^(2*k)*V^k)
      _ = (64*V)^k := by
        have hm : 2^(2*k-1)*2= (2:ℝ)^(2*k) := by rw [←pow_succ,ht]
        calc
          _ = (2^(2*k-1)*2)*(2:ℝ)^(2*k)*(2:ℝ)^(2*k)*V^k := by ring
          _ = _ := by rw [hm,←pow_add,←pow_add,mul_pow]; congr 1; rw [show 2*k+2*k+2*k=6*k by omega,pow_mul]; norm_num
  unfold evenMomentSq
  calc
    _ ≤ ((64*V)^k)^(1/(k:ℝ)) := Real.rpow_le_rpow
      (by apply Finset.sum_nonneg; intro a _; positivity [(condition (R.withDensity f hf hfm) A hp0).nonneg a]) hs' (by positivity)
    _ = _ := by rw [←Real.rpow_natCast,one_div,Real.rpow_rpow_inv (by positivity) (by positivity)]

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eventMass_indicator (P : FiniteLaw α) (A : Finset α) :
    P.eventMass A=P.expect (fun a => if a∈A then 1 else 0) := by
  simp only [expect,mul_ite,mul_one,mul_zero,←Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass]

theorem eventMass_compl (P : FiniteLaw α) (A : Finset α) :
    P.eventMass Aᶜ=1-P.eventMass A := by
  rw [eventMass_indicator,eventMass_indicator]
  have he : P.expect (fun a => (if a∈Aᶜ then (1:ℝ) else 0)+(if a∈A then 1 else 0))=1 := by
    convert P.expect_const 1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; funext a
    by_cases ha : a∈A <;> simp [ha]
  rw [expect_add] at he
  linarith

theorem density_second_moment_le_six (R : FiniteLaw α) (f : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hM : R.expect (fun a => |f a-1|^(2*k)) ≤ 1) :
    R.expect (fun a => f a^2) ≤ 6 := by
  have h := R.expect_lower_moment_le_two (fun a => f a-1) (2*k) hM 2 (by omega)
  calc
    _ ≤ R.expect (fun a => 2*(f a-1)^2+2) := R.expect_mono (fun a => by nlinarith [sq_nonneg (f a-2)])
    _ = 2*R.expect (fun a => (f a-1)^2)+2 := by rw [expect_add,expect_const_mul,expect_const]
    _ ≤ _ := by linarith [le_abs_self (R.expect (fun a => (f a-1)^2))]

/-- Cauchy--Schwarz loss on the actual low-reference-density event, for
 either density. The same clipping event is used for both hypotheses. -/
theorem density_low_event_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hg : ∀a,0 ≤ g a) (hgm : R.expect g=1) (k : ℕ) (hk : 1 ≤ k) (U : ℝ)
    (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    (R.withDensity g hg hgm).eventMass (Finset.univ.filter (fun a => f a<1/2)) ≤
      Real.sqrt (6*(4*U)^k) := by
  let A := Finset.univ.filter (fun a => f a<1/2)
  have hR : R.eventMass A ≤ (4*U)^k := by
    calc
      _ ≤ 2^(2*k)*R.expect (fun a => |f a-1|^(2*k)) :=
        R.low_density_reference_mass f (2*k) A (fun a ha => (Finset.mem_filter.mp ha).2)
      _ ≤ 2^(2*k)*U^k := mul_le_mul_of_nonneg_left hfM (by positivity)
      _ = _ := by rw [pow_mul,mul_pow]; norm_num
  have hsecond := R.density_second_moment_le_six g k hk (hgM.trans (pow_le_one₀ hU hU1))
  have hsq : ((R.withDensity g hg hgm).eventMass A)^2 ≤ 6*(4*U)^k := by
    apply (R.density_bad_mass_sq g A).trans
    calc
      _ ≤ R.eventMass A*6 := mul_le_mul_of_nonneg_left hsecond (R.eventMass_nonneg A)
      _ ≤ _ := by nlinarith
  exact (Real.le_sqrt ((R.withDensity g hg hgm).eventMass_nonneg A) (by positivity)).mpr hsq

theorem commonClipEvent_loss (P : FiniteLaw α) (B : Finset α) (f : α → ℝ) :
    1-P.eventMass (commonClipEvent B f) ≤
      P.eventMass Bᶜ+P.eventMass (Finset.univ.filter (fun a => f a<1/2)) := by
  rw [←eventMass_compl,eventMass_indicator,eventMass_indicator,eventMass_indicator,←expect_add]
  apply P.expect_mono
  intro a
  simp only [commonClipEvent,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp_all


/-- Quantitative common clipping on any genuine good event. Both bad-event
 costs below are measured under the actual normalized laws, not reference mass. -/
theorem commonClipEvent_mass (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    1-(R.withDensity f hf hfm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) ∧
    1-(R.withDensity g hg hgm).eventMass (commonClipEvent B f) ≤ e+Real.sqrt (6*(4*U)^k) := by
  constructor
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hfB
      (density_low_event_mass R f f hf hfm k hk U hU hU1 hfM hfM))
  · exact (commonClipEvent_loss _ B f).trans (add_le_add hgB
      (density_low_event_mass R f g hg hgm k hk U hU hU1 hfM hgM))

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem exists_clippedOracle (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀a,0 ≤ f a) (hg : ∀a,0 ≤ g a) (hfm : R.expect f=1) (hgm : R.expect g=1)
    (B : Finset α) (e : ℝ) (hfB : (R.withDensity f hf hfm).eventMass Bᶜ ≤ e)
    (hgB : (R.withDensity g hg hgm).eventMass Bᶜ ≤ e)
    (k : ℕ) (hk : 1 ≤ k) (U : ℝ) (hU : 0 ≤ U) (hU1 : U ≤ 1)
    (hfM : R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM : R.expect (fun a => |g a-1|^(2*k)) ≤ U^k)
    (V : ℝ) (hV : 0 ≤ V)
    (hM : R.expect (fun a => |if a∈B then g a-f a else 0|^(2*k)) ≤ V^k)
    (hsmall : e+Real.sqrt (6*(4*U)^k) ≤ 1/2) :
    Nonempty (ClippedOracle (R.withDensity f hf hfm) (R.withDensity g hg hgm)
      k (e+Real.sqrt (6*(4*U)^k)) (64*V)) := by
  let A := commonClipEvent B f
  let P := R.withDensity f hf hfm
  let Q := R.withDensity g hg hgm
  have hA (a : α) (ha : a∈A) : 1/2 ≤ f a := (Finset.mem_filter.mp ha).2
  have hloss := commonClipEvent_mass R f g hf hg hfm hgm B e hfB hgB k hk U hU hU1 hfM hgM
  have hp : 1/2 ≤ P.eventMass A := by linarith [hloss.1]
  have hq : 1/2 ≤ Q.eventMass A := by linarith [hloss.2]
  have hp0 : 0<P.eventMass A := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0<Q.eventMass A := lt_of_lt_of_le (by norm_num) hq
  let Z : α → ℝ := fun a => P.eventMass A/Q.eventMass A*(g a/f a)-1
  have hden (a : α) : (Q.condition A hq0).mass a=(P.condition A hp0).mass a*(1+Z a) := by
    dsimp only [Z]
    rw [show 1+(P.eventMass A/Q.eventMass A*(g a/f a)-1)=P.eventMass A/Q.eventMass A*(g a/f a) by ring]
    exact conditioned_density_identity R f g hf hg hfm hgm A
      (fun a ha => lt_of_lt_of_le (by norm_num) (hA a ha)) hp0 hq0 a
  have hAM : R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k := by
    apply le_trans (R.expect_mono _) hM
    intro a
    by_cases ha : a∈A
    · have hb := (Finset.mem_filter.mp ha).1
      simp only [ite_eq_left ha,ite_eq_left hb,le_refl]
    · rw [ite_eq_right ha]
      simp only [abs_zero,zero_pow (by omega : 2*k≠0)]
      exact pow_nonneg (abs_nonneg _) _
  exact ⟨{
    first := P.condition A hp0
    second := Q.condition A hq0
    score := Z
    density := hden
    likelihood_nonneg := fun a => by
      dsimp only [Z]
      have hh := mul_nonneg (div_nonneg hp0.le hq0.le) (div_nonneg (hg a) (hf a))
      linarith
    centered := density_score_centered _ _ Z hden
    moment := clipped_score_moment R f g hf hg hfm hgm A hA hp hq k hk V hV hAM
    first_tv := by rw [tv_symm,tv_condition]; exact hloss.1
    second_tv := by rw [tv_symm,tv_condition]; exact hloss.2
  }⟩

end FiniteLaw
end TraceReconstruction

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceOracleDensity_expansion {Side Leaf : Type*} (T n : ℕ → ℕ) (s b : ℕ)
    (Z : Leaf → ℝ) (τ : Bool)
    (z : Reports Side (SourceTrialCount T n (b+1))) (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
    sourceOracleDensity T n s b Z τ (z,x)=multilinear (sourceOracleCoefficient T n s b z τ) Z x :=
  averagedDensity_expansion _ _ _ _

theorem source_canonical_centered_moment {Side Leaf : Type*} [Fintype Leaf]
    (T n : ℕ → ℕ) (s b k : ℕ) (P : FiniteLaw Leaf) (Z : Leaf → ℝ)
    (hk : 1 ≤ k) (hcenter : P.expect Z=0) {L : ℝ} (hL : 0<L)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (z : Reports Side (SourceTrialCount T n (b+1))) (τ : Bool) :
    (P.product (SourceLeafCount T (b+1))).expect
      (fun x => |sourceOracleDensity T n s b Z τ (z,x)-1|^(2*k)) ≤
        ((((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b)/
          (1-((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b))^k := by
  have he (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
      sourceOracleDensity T n s b Z τ (z,x)-1=
        multilinear (nonconstantCoefficient (sourceOracleCoefficient T n s b z τ)) Z x := by
    rw [nonconstant_multilinear,sourceOracleCoefficient_empty,sourceOracleDensity_expansion]
  simp_rw [he]
  apply (multilinear_moment_scaled P Z k hk hcenter hL hMoment _ _).trans
  exact pow_le_pow_left₀ (multilinearEnergy_nonneg _ _)
    (source_canonical_centered_energy T n s b z τ (by positivity) hsmall) k

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem degreeForcedRoleEnergy_zero_of_lt (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ) (hr : r<2^(b+1))
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming=0 := by
  have hi : IsEmpty (DegreeForcedRole T b r) := ⟨fun w => by
    obtain ⟨F⟩ := w.property.2
    have hh := F.leaf_lower
    rw [occupiedWindowTerm_leafCount,w.property.1] at hh
    omega⟩
  let := hi
  exact Finset.sum_eq_zero (fun w _ => isEmptyElim w)

theorem sourceSharpDegreeBudget_nonneg (T n : ℕ → ℕ) (s b r : ℕ) (ω η a : ℝ) :
    0 ≤ sourceSharpDegreeBudget T n s b r ω η a := by
  have h := sourceForcedBudget_nonneg T n s b r ω
  unfold sourceSharpDegreeBudget
  split_ifs <;> positivity

theorem source_canonical_sharp_degree_bound {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b r : ℕ) (ω η a : ℝ) (ha : 0≤a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (∑σ : Fin (SourceLeafCount T (b+1)) → Bool, if monomialDegree σ=r then
      (averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false) σ -
       averagedCoefficient (PairedMechanisms.orientationsGiven z)
        (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true) σ)^2 else 0) ≤
      sourceSharpDegreeBudget T n s b r ω η a := by
  rw [source_canonical_degree_sum]
  apply (sourceCoefficient_degree_energy T n _ s _ _ (fun j => centralThird (T j)) b r
    (sourceReportFlags T n (b+1) z) 0 η
    (hiddenConditions_smoothingCap T n _ ω η s (b+1) hη _ hz.1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    exact (sq_le_sq₀ (sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).mpr hz.2.le
  · by_cases hr : 2^(b+1) ≤ r
    · rw [ite_eq_left hr]
      exact degreeForcedRoleEnergy_bound T n _ hT s (sourceLocalCenter T n) _ _ _ (sourceScheduledShift_hasPlateau T n)
        (fun j => hiddenBinomialCap (n j) ω) (fun j => hiddenBinomialCap (sourceScheduledTrials T n j) ω)
        (fun j => hiddenBinomialCap_nonneg _ _) (fun j => hiddenBinomialCap_nonneg _ _)
        b r _ (hiddenConditions_binomialCaps T n _ ω (b+1) _ hz.1) 0
    · rw [ite_eq_right hr,degreeForcedRoleEnergy_zero_of_lt T n _ s _ _ _ b r (lt_of_not_ge hr)]

/-- Complete signed energy, with finite low-degree forced-tree bound and
 the geometric high tail. No coefficient estimates remain as hypotheses. -/
theorem source_canonical_sharp_energy {Side : Type*} (T n : ℕ → ℕ) (hT : ∀j,0<T j)
    (s b R : ℕ) (ω η a w : ℝ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hsmall : w^2*sourceSparseCount T s b<1)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    multilinearEnergy (sourceSignedCoefficient T n s b z) w ≤ sourceSharpEnergyBudget T n s b R ω η a w := by
  apply multilinearEnergy_low_high _ w (w^2*sourceSparseCount T s b) 4 hw (by positivity) hsmall
    (by norm_num) (fun r => if r=0 then 0 else sourceSharpDegreeBudget T n s b r ω η a)
  · intro r _
    by_cases hr : r=0
    · subst r
      rw [sourceSignedCoefficient_zero,ite_eq_left rfl]
    · rw [ite_eq_right hr]
      exact source_canonical_sharp_degree_bound T n hT s b r ω η a ha hη z hz
  · intro r _
    exact sourceSignedCoefficient_degree_geometric T n s b r z w
  · intro r
    split_ifs
    · rfl
    · exact sourceSharpDegreeBudget_nonneg T n s b r ω η a

theorem sourceSharpEnergyBudget_nonneg (T n : ℕ → ℕ) (s b R : ℕ) (ω η a w : ℝ)
    (hsmall : w^2*sourceSparseCount T s b<1) :
    0 ≤ sourceSharpEnergyBudget T n s b R ω η a w := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (pow_nonneg (sq_nonneg w) r |>.trans_eq (pow_mul w 2 r).symm)
    split_ifs
    · rfl
    · exact sourceSharpDegreeBudget_nonneg T n s b r ω η a
  · exact div_nonneg (by positivity) (sub_nonneg.mpr hsmall.le)

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_canonical_sharp_signed_moment {Side Leaf : Type*} [Fintype Leaf]
    (T n : ℕ → ℕ) (hT : ∀j,0<T j) (s b R k : ℕ) (ω η a : ℝ) (ha : 0 ≤ a)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (z : Reports Side (SourceTrialCount T n (b+1))) (hz : SourceTypical T n s b ω a z) :
    (P.product (SourceLeafCount T (b+1))).expect
      (fun x => |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|^(2*k)) ≤
        (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k := by
  have he (x : Fin (SourceLeafCount T (b+1)) → Leaf) :
      |sourceOracleDensity T n s b Z true (z,x)-sourceOracleDensity T n s b Z false (z,x)|=
        |multilinear (sourceSignedCoefficient T n s b z) Z x| := by
    unfold sourceSignedCoefficient
    rw [multilinear_sub,←sourceOracleDensity_expansion,←sourceOracleDensity_expansion,abs_sub_comm]
  simp_rw [he]
  apply (multilinear_moment_scaled P Z k hk hcenter hL hMoment _ _).trans
  exact pow_le_pow_left₀ (multilinearEnergy_nonneg _ _)
    (source_canonical_sharp_energy T n hT s b R ω η a _ ha (by positivity) hsmall hη z hz) k


theorem sourceCenteredBudget_nonneg (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ)
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1) :
    0 ≤ sourceCenteredBudget T s b k L :=
  div_nonneg (by positivity) (sub_nonneg.mpr hsmall.le)

theorem sourceCenteredBudget_le_one (T : ℕ → ℕ) (s b k : ℕ) (L : ℝ)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2) :
    sourceCenteredBudget T s b k L ≤ 1 := by
  have hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1 := by linarith
  apply (div_le_iff₀ (sub_pos.mpr hsmall)).mpr
  linarith

theorem source_reference_centered_moment {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b k : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P : FiniteLaw Leaf) (Z : Leaf → ℝ) (hk : 1 ≤ k) (hc : P.expect Z=0)
    {L : ℝ} (hL : 0<L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1) (τ : Bool) :
    (sourceReferenceLaw T n b M P).expect
      (fun zx => |sourceOracleDensity T n s b Z τ zx-1|^(2*k)) ≤ (sourceCenteredBudget T s b k L)^k := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  calc
    _ ≤ M.reports.expect (fun _ => (sourceCenteredBudget T s b k L)^k) :=
      M.reports.expect_mono (fun z => source_canonical_centered_moment T n s b k P Z hk hc hL hMoment hsmall z τ)
    _ = _ := M.reports.expect_const _

attribute [local instance] OAI.TraceReconstruction.instDecidableEqProd_solutions
theorem source_reference_signed_moment {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1 ≤ k) (hc : P.expect Z=0)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η) :
    (sourceReferenceLaw T n b M P).expect (fun zx =>
      |if zx∈sourceTypicalSet T n s b ω a then sourceOracleDensity T n s b Z true zx-
        sourceOracleDensity T n s b Z false zx else 0|^(2*k)) ≤
      (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k := by
  rw [sourceReferenceLaw,FiniteLaw.expect_prod]
  have hV := sourceSharpEnergyBudget_nonneg T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L) hsmall
  calc
    _ ≤ M.reports.expect (fun _ => (sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))^k) := by
      apply M.reports.expect_mono
      intro z
      by_cases hz : SourceTypical T n s b ω a z
      · simp only [sourceTypicalSet,Finset.mem_filter,Finset.mem_univ,true_and,hz,ite_true]
        exact source_canonical_sharp_signed_moment T n hTpos s b R k ω η a ha hη P Z hk hc hL hMoment hsmall z hz
      · simp only [sourceTypicalSet,Finset.mem_filter,Finset.mem_univ,true_and,hz,ite_false,
          abs_zero,zero_pow (by omega : 2*k≠0),FiniteLaw.expect_const]
        exact pow_nonneg hV k
    _ = _ := M.reports.expect_const _

theorem source_reference_clipped_exists_oai {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0)
    (ω a η L : ℝ) (ha : 0≤a) (hL : 0<L) (hk : 1≤k)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (hB : ∀τ,((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
      (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
        (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
    Nonempty (ClippedOracle
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z false)
        (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_total T n s b M P Z hc false))
      ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z true)
        (sourceOracleDensity_nonneg T n s b Z hZ true) (sourceOracleDensity_total T n s b M P Z hc true))
      k (sourceClippingCost T n s b k ω a L)
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  have hsmall : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b<1 := by linarith
  exact FiniteLaw.exists_clippedOracle (sourceReferenceLaw T n b M P)
    (sourceOracleDensity T n s b Z false) (sourceOracleDensity T n s b Z true)
    (sourceOracleDensity_nonneg T n s b Z hZ false) (sourceOracleDensity_nonneg T n s b Z hZ true)
    (sourceOracleDensity_total T n s b M P Z hc false) (sourceOracleDensity_total T n s b M P Z hc true)
    (sourceTypicalSet T n s b ω a) _ (hB false) (hB true) k hk (sourceCenteredBudget T s b k L)
    (sourceCenteredBudget_nonneg T s b k L hsmall) (sourceCenteredBudget_le_one T s b k L hscale)
    (source_reference_centered_moment T n s b k M P Z hk hc hL hMoment hsmall false)
    (source_reference_centered_moment T n s b k M P Z hk hc hL hMoment hsmall true)
    _ (sourceSharpEnergyBudget_nonneg T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L) hsmall)
    (source_reference_signed_moment T n hTpos s b R k M P Z ω a η L ha hL hk hc hMoment hsmall hη) herror

end TraceReconstruction



end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TraceReconstruction.source_reference_clipped_exists_oai.{u_1, u_2} := @OAI.TraceReconstruction.source_reference_clipped_exists_oai.{u_1, u_2}
