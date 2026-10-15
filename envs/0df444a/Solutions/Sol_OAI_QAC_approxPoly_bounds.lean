-- Prove2me | solution 1 for OAI.QAC.approxPoly_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:15:51.04519+00:00
-- url     : https://prove2.me/submissions/71712ff3-9a97-40f1-bb5a-2b763fb48e32

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean:L273-L343
-- (upload_full_project.md Phase 4): solution for node OAI.QAC.approxPoly_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Theorems.Thm_OAI_QAC_chebyshev_denominator
import Theorems.Thm_OAI_QAC_weight_mul_le

-- ---- from OAI.InformationTheory.QuantumCircuit.Polynomial ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

lemma weight_nonneg {R : ℝ} (hR : 0 ≤ R) (p : ℝ[X]) : 0 ≤ weight R p := by
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hR _)

lemma weight_add_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p + q) ≤ weight R p + weight R q := by
  let s := p.support ∪ q.support
  have hf : ∀ i : ℕ, |(0 : ℝ)| * R ^ i = 0 := by simp
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  unfold weight
  rw [sum_eq_of_subset _ hf (support_add.trans (Finset.Subset.refl s)),
    sum_eq_of_subset _ hf hp, sum_eq_of_subset _ hf hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [coeff_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hR _)

lemma weight_sub_le {R : ℝ} (hR : 0 ≤ R) (p q : ℝ[X]) :
    weight R (p - q) ≤ weight R p + weight R q := by
  simpa only [sub_eq_add_neg, weight_neg] using weight_add_le hR p (-q)

lemma weight_prod_le {ι : Type*} {R : ℝ} (hR : 0 ≤ R) (s : Finset ι) (p : ι → ℝ[X]) :
    weight R (∏ i ∈ s, p i) ≤ ∏ i ∈ s, weight R (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (weight_mul_le hR _ _).trans
      (mul_le_mul_of_nonneg_left ih (weight_nonneg hR _))

lemma weight_chebyshev {R : ℝ} (hR : 0 ≤ R) (z : ℝ[X]) (k : ℕ) :
    weight R ((Polynomial.Chebyshev.T ℝ k).comp z) ≤ (2 * weight R z + 1) ^ k := by
  let b := weight R z
  let A := 2 * b + 1
  have hb : 0 ≤ b := weight_nonneg hR z
  have hA : 1 ≤ A := by dsimp [A]; linarith
  change weight R ((Polynomial.Chebyshev.T ℝ k).comp z) ≤ A ^ k
  induction k using Nat.twoStepInduction with
  | zero => simp [Polynomial.Chebyshev.T_zero]
  | one => simpa [Polynomial.Chebyshev.T_one, A, b] using (show b ≤ A by dsimp [A]; linarith)
  | more k hk hk1 =>
    have heq : Polynomial.Chebyshev.T ℝ (↑(k + 2)) =
        2 * X * Polynomial.Chebyshev.T ℝ (↑(k + 1)) - Polynomial.Chebyshev.T ℝ k := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
    rw [heq, sub_comp, mul_comp, mul_comp, X_comp]
    have htwo : weight R ((2 : ℝ[X]).comp z) = 2 := by
      rw [show (2 : ℝ[X]) = C 2 by exact (map_ofNat C 2).symm, C_comp, weight_C]
      norm_num
    calc
      _ ≤ weight R (((2 : ℝ[X]).comp z) * z * (Polynomial.Chebyshev.T ℝ (↑(k + 1))).comp z) +
          weight R ((Polynomial.Chebyshev.T ℝ (↑k)).comp z) := weight_sub_le hR _ _
      _ ≤ (2 * b) * A ^ (k + 1) + A ^ k := by
        apply add_le_add _ hk
        apply (weight_mul_le hR _ _).trans
        apply mul_le_mul _ hk1 (weight_nonneg hR _) (by positivity)
        simpa only [htwo] using weight_mul_le hR ((2 : ℝ[X]).comp z) z
      _ ≤ A ^ (k + 2) := by
        rw [pow_succ, pow_succ, pow_succ]
        have h : 2 * b * A + 1 ≤ A * A := by dsimp [A]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg (le_trans zero_le_one hA) k)]

lemma chebyshev_abs_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.T ℝ k).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

lemma rootPoly_eval_nat {r x : ℕ} (hx0 : 1 ≤ x) (hxr : x ≤ r) :
    (rootPoly r).eval (x : ℝ) = 0 := by
  have hx : x - 1 ∈ Finset.range r := Finset.mem_range.2 (by omega)
  have hx1 : x - 1 + 1 = x := by omega
  simp only [rootPoly, Polynomial.eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  apply Finset.prod_eq_zero hx
  have hxne : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have he : ((x - 1 : ℕ) : ℝ) + 1 = x := by exact_mod_cast hx1
  rw [he, inv_mul_cancel₀ hxne, sub_self]

lemma rootPoly_weight {R : ℝ} (hR : 0 ≤ R) (r : ℕ) :
    weight R (rootPoly r) ≤ (1 + R) ^ r := by
  unfold rootPoly
  apply (weight_prod_le hR _ _).trans
  calc
    _ ≤ ∏ _j ∈ Finset.range r, (1 + R) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact weight_nonneg hR _
      · intro j hj
        apply (weight_sub_le hR _ _).trans
        simp only [weight_one]
        apply add_le_add_right
        apply (weight_mul_le hR _ _).trans
        rw [weight_C, weight_X, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left hR (inv_le_one_of_one_le₀ (by norm_num))
    _ = (1 + R) ^ r := by simp

lemma rootPoly_abs_eval {m x : ℝ} (hm : 1 ≤ m) (hx0 : 0 ≤ x) (hxm : x ≤ m) (r : ℕ) :
    |(rootPoly r).eval x| ≤ m ^ r := by
  simp only [rootPoly, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    Finset.abs_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.range r, m := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro j hj
      have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
      have hj0 : 0 < (j : ℝ) + 1 := by positivity
      have hv0 : 0 ≤ ((j : ℝ) + 1)⁻¹ * x := by positivity
      have hv : ((j : ℝ) + 1)⁻¹ * x ≤ m :=
        (mul_le_of_le_one_left hx0 (inv_le_one_of_one_le₀ hj1)).trans hxm
      exact abs_le.2 ⟨by linarith, by linarith⟩
    _ = m ^ r := by simp

lemma rootPoly_degree (r : ℕ) : (rootPoly r).natDegree ≤ r := by
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.range r, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      apply (natDegree_sub_le _ _).trans
      apply max_le (by simp)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = r := by simp

lemma scalePoly_eval (r m x : ℝ) :
    (scalePoly r m).eval x = (m + r - 2 * x) / (m - r) := by
  simp only [scalePoly, eval_sub, eval_C, eval_mul, eval_X]
  ring

lemma scalePoly_zero (r m : ℝ) :
    (scalePoly r m).eval 0 = (m + r) / (m - r) := by rw [scalePoly_eval]; ring

lemma scalePoly_interval {r m x : ℝ} (hrm : r < m) (hrx : r ≤ x) (hxm : x ≤ m) :
    (scalePoly r m).eval x ∈ Set.Icc (-1) 1 := by
  rw [scalePoly_eval]
  constructor
  · apply (le_div_iff₀ (sub_pos.2 hrm)).2
    linarith
  · apply (div_le_one (sub_pos.2 hrm)).2
    linarith

lemma scalePoly_degree (r m : ℝ) : (scalePoly r m).natDegree ≤ 1 := by
  apply (natDegree_sub_le _ _).trans
  simp only [natDegree_C, Nat.zero_max]
  exact (natDegree_C_mul_le _ _).trans (by simp)

lemma scalePoly_weight {R r m : ℝ} (hR : 0 ≤ R) (hr : 1 ≤ r) (hm : 2 * r ≤ m) :
    weight R (scalePoly r m) ≤ 3 + 2 * R := by
  have hmr : 1 ≤ m - r := by linarith
  have hmr0 : 0 < m - r := by linarith
  have hconst0 : 0 ≤ (m + r) / (m - r) := div_nonneg (by linarith) hmr0.le
  have hconst : (m + r) / (m - r) ≤ 3 := by
    apply (div_le_iff₀ hmr0).2
    linarith
  have hlin0 : 0 ≤ 2 / (m - r) := by positivity
  have hlin : 2 / (m - r) ≤ 2 := by
    apply (div_le_iff₀ hmr0).2
    linarith
  apply (weight_sub_le hR _ _).trans
  apply (add_le_add_right (weight_mul_le hR _ _) _).trans
  simp only [weight_C, weight_X, abs_of_nonneg hconst0, abs_of_nonneg hlin0]
  exact add_le_add hconst (mul_le_mul_of_nonneg_right hlin hR)

/-- Finite degree, coefficient, normalization, and decay bounds for the approximating polynomial. -/
lemma approxPoly_bounds {r m k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hr : 1 ≤ r) (hm : 2 * r ≤ m)
    (hk : 4 * (r : ℝ) * Real.log m ≤ (k : ℝ) * Real.sqrt ((r : ℝ) / m)) :
    (approxPoly r m k).natDegree ≤ r + k ∧
    weight R (approxPoly r m k) ≤ (1 + R) ^ r * (7 + 4 * R) ^ k ∧
    (approxPoly r m k).eval 0 = 1 ∧
    ∀ x : ℕ, 1 ≤ x → x ≤ m →
      |(approxPoly r m k).eval (x : ℝ)| ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : 2 * (r : ℝ) ≤ m := by exact_mod_cast hm
  have hrm : (r : ℝ) < m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hden := chebyshev_denominator k (lt_of_lt_of_le zero_lt_one hrR) hrm
  let den := (Polynomial.Chebyshev.T ℝ k).eval (((m : ℝ) + r) / (m - r))
  have hd1 : 1 ≤ den := hden.1
  have hd0 : 0 < den := lt_of_lt_of_le zero_lt_one hd1
  have hdb : Real.exp (4 * (r : ℝ) * Real.log m) / 2 ≤ den :=
    (div_le_div_of_nonneg_right (Real.exp_le_exp.2 hk) (by norm_num)).trans hden.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply natDegree_mul_le.trans
    apply add_le_add
    · exact (natDegree_C_mul_le _ _).trans (rootPoly_degree r)
    · apply natDegree_comp_le.trans
      simpa only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one] using
        Nat.mul_le_mul_left k (scalePoly_degree r m)
  · apply (weight_mul_le hR _ _).trans
    apply mul_le_mul _ _ (weight_nonneg hR _) (by positivity)
    · apply (weight_mul_le hR _ _).trans
      rw [weight_C, abs_of_pos (inv_pos.2 hd0)]
      exact (mul_le_of_le_one_left (weight_nonneg hR _) (inv_le_one_of_one_le₀ hd1)).trans
        (rootPoly_weight hR r)
    · apply (weight_chebyshev hR _ k).trans
      apply pow_le_pow_left₀ (by have := weight_nonneg hR (scalePoly r m); linarith)
      have := scalePoly_weight hR hrR hmR
      linarith
  · simp only [approxPoly, eval_mul, eval_C, rootPoly_eval_zero, mul_one,
      eval_comp, scalePoly_zero]
    exact inv_mul_cancel₀ (ne_of_gt hd0)
  · intro x hx0 hxm
    by_cases hxr : x ≤ r
    · simp only [approxPoly, eval_mul, rootPoly_eval_nat hx0 hxr, mul_zero, zero_mul,
        abs_zero]
      positivity
    have hrx : (r : ℝ) ≤ x := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hxr))
    have hxmR : (x : ℝ) ≤ m := by exact_mod_cast hxm
    have hroot := rootPoly_abs_eval (show (1 : ℝ) ≤ m by linarith)
      (Nat.cast_nonneg x) hxmR r
    have hcheb := chebyshev_abs_le_one k (scalePoly_interval hrm hrx hxmR)
    have heq : (approxPoly r m k).eval (x : ℝ) =
        den⁻¹ * (rootPoly r).eval (x : ℝ) *
          (Polynomial.Chebyshev.T ℝ k).eval ((scalePoly r m).eval (x : ℝ)) := by
      simp only [approxPoly, eval_mul, eval_C, eval_comp, den]
    rw [heq, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hd0)]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hroot (le_of_lt (inv_pos.2 hd0)))
      hcheb (abs_nonneg _) (by positivity)).trans
    rw [mul_one, inv_mul_eq_div]
    apply (div_le_iff₀ hd0).2
    have epos : 0 ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by positivity
    apply (le_trans ?_ (mul_le_mul_of_nonneg_left hdb epos))
    rw [show 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) *
        (Real.exp (4 * (r : ℝ) * Real.log m) / 2) =
        Real.exp ((r : ℝ) * Real.log m) by
      rw [show 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) *
          (Real.exp (4 * (r : ℝ) * Real.log m) / 2) =
          Real.exp (-(3 * (r : ℝ) * Real.log m)) *
            Real.exp (4 * (r : ℝ) * Real.log m) by ring,
        ← Real.exp_add]
      congr 1
      ring]
    rw [Real.exp_nat_mul, Real.exp_log hm0]

end QAC

end

end OAI

-- ---- platform node ----
open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem solution {r m k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hr : 1 ≤ r) (hm : 2 * r ≤ m)
    (hk : 4 * (r : ℝ) * Real.log m ≤ (k : ℝ) * Real.sqrt ((r : ℝ) / m)) :
    (approxPoly r m k).natDegree ≤ r + k ∧
    weight R (approxPoly r m k) ≤ (1 + R) ^ r * (7 + 4 * R) ^ k ∧
    (approxPoly r m k).eval 0 = 1 ∧
    ∀ x : ℕ, 1 ≤ x → x ≤ m →
      |(approxPoly r m k).eval (x : ℝ)| ≤ 2 * Real.exp (-(3 * (r : ℝ) * Real.log m)) := by
  first
    | exact OAI.QAC.approxPoly_bounds hR hr hm hk
    | exact OAI.QAC.approxPoly_bounds
    | (apply OAI.QAC.approxPoly_bounds <;> assumption)
    | (intros; apply OAI.QAC.approxPoly_bounds <;> assumption)
