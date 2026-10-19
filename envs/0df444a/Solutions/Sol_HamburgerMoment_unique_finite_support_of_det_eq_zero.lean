-- Prove2me | solution 1 for HamburgerMoment.unique_finite_support_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:18:29.274963+00:00
-- url     : https://prove2.me/submissions/325b64b0-6706-4015-abc6-3c3ca9b2103a

import Theorems.Thm_HamburgerMoment_isMomentSequence_of_hankelPosDef
import Theorems.Thm_HamburgerMoment_unique_of_abs_le_factorial

open MeasureTheory HamburgerMoment
open scoped BigOperators

private lemma polynomial_sq_integral (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (n : ℕ) (a : Fin (n+1) → ℝ) :
    Integrable (fun x => (∑ i, a i * x ^ i.val)^2) μ ∧
    (∫ x, (∑ i, a i * x ^ i.val)^2 ∂μ) =
      ∑ i, ∑ j, a i * a j * m (i.val+j.val) := by
  have he (x : ℝ) : (∑ i, a i * x ^ i.val)^2 =
      ∑ i, ∑ j, a i * a j * x^(i.val+j.val) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  have hi (i j : Fin (n+1)) : Integrable (fun x : ℝ => a i * a j * x^(i.val+j.val)) μ :=
    (hμ _).1.const_mul _
  simp_rw [he]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, (hμ _).2]

private lemma finite_support (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (n : ℕ) (hdet : (hankelMatrix m n).det = 0) :
    ∃ S : Finset ℝ, μ (↑S)ᶜ = 0 := by
  classical
  obtain ⟨a, ha, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : Polynomial ℝ := Polynomial.ofFn (n+1) a
  have hp : p ≠ 0 := by
    intro hp
    apply ha
    apply Polynomial.injective_ofFn (n+1)
    simpa [p] using hp
  have he (x : ℝ) : p.eval x = ∑ i, a i * x ^ i.val := by
    simp [p, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  have hq : (∑ i, ∑ j, a i * a j * m (i.val+j.val)) = 0 := by
    calc
      _ = ∑ i, a i * ((hankelMatrix m n).mulVec a) i := by
        simp only [Matrix.mulVec, dotProduct, hankelMatrix, Matrix.of_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hker]; simp
  have hi := polynomial_sq_integral m μ hμ n a
  have hz : (fun x : ℝ => (p.eval x)^2) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x)) ?_).mp
    · simpa only [he] using hi.2.trans hq
    · simpa only [he] using hi.1
  refine ⟨p.roots.toFinset, ?_⟩
  apply ae_iff.mp
  filter_upwards [hz] with x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact (sq_eq_zero_iff.mp hx : p.eval x = 0)

private lemma factorial_bound (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsMomentMeasure m μ) (S : Finset ℝ) (hS : μ (↑S)ᶜ = 0) :
    ∃ C D : ℝ, ∀ k : ℕ, |m k| ≤ C * D^k * (k.factorial : ℝ) := by
  classical
  let : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (by simpa using (hμ 0).1)
  let D : ℝ := 1 + ∑ x ∈ S, |x|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha : ∀ᵐ x ∂μ, x ∈ S := ae_iff.mpr hS
  refine ⟨μ.real Set.univ, D, fun k => ?_⟩
  have hb : ∀ᵐ x ∂μ, ‖x^k‖ ≤ D^k := by
    filter_upwards [ha] with x hx
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg x)
    have hs := Finset.single_le_sum (fun y (_ : y ∈ S) => abs_nonneg y) hx
    simp only [Real.norm_eq_abs]
    dsimp [D]
    linarith
  have hbound : |m k| ≤ μ.real Set.univ * D^k := by
    rw [← (hμ k).2, ← Real.norm_eq_abs]
    simpa only [mul_comm] using norm_integral_le_of_norm_le_const hb
  calc
    _ ≤ μ.real Set.univ * D^k := hbound
    _ ≤ μ.real Set.univ * D^k * (k.factorial : ℝ) := by
      apply le_mul_of_one_le_right (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos k)

theorem solution (m : ℕ → ℝ) (hm : HankelPosDef m) (n : ℕ)
    (hdet : (hankelMatrix m n).det = 0) :
    ∃ μ : Measure ℝ, (∀ ν : Measure ℝ, IsMomentMeasure m ν ↔ ν = μ) ∧
      ∃ S : Finset ℝ, μ (↑S)ᶜ = 0 := by
  obtain ⟨μ, hμ⟩ := HamburgerMoment.isMomentSequence_of_hankelPosDef m hm
  obtain ⟨S, hS⟩ := finite_support m μ hμ n hdet
  obtain ⟨C, D, hb⟩ := factorial_bound m μ hμ S hS
  refine ⟨μ, fun ν => ⟨fun hν => ?_, fun hν => hν ▸ hμ⟩, S, hS⟩
  exact HamburgerMoment.unique_of_abs_le_factorial m C D hb ν μ hν hμ
