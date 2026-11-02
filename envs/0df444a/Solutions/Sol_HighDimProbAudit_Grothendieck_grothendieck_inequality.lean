-- Prove2me | solution 1 for HighDimProbAudit.Grothendieck.grothendieck_inequality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T23:15:48.397589+00:00
-- url     : https://prove2.me/submissions/f8309c26-1336-47c2-aa29-f27f7bdb89b0

import Mathlib
import Theorems.Thm_HighDimProbAudit_Grothendieck_sphere_linearization
import Theorems.Thm_HighDimProb_RandomVectors_grothendieck_identity

set_option autoImplicit false
universe uH

open MeasureTheory ProbabilityTheory
open HighDimProbAudit.Grothendieck
open HighDimProb.RandomVectors
open scoped BigOperators

namespace SolGrothendieckInequality

lemma abs_sum_mul_le_of_abs_le_one {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    ∃ s : ι → ℝ, (∀ i, s i = -1 ∨ s i = 1) ∧
      |∑ i, w i * x i| ≤ ∑ i, w i * s i := by
  let s : ι → ℝ := fun i => if 0 ≤ w i then 1 else -1
  refine ⟨s, fun i => ?_, ?_⟩
  · dsimp [s]
    split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
  · have h1 : |∑ i, w i * x i| ≤ ∑ i, |w i * x i| := Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ i, |w i * x i| ≤ ∑ i, w i * s i := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      have hws : w i * s i = |w i| := by
        dsimp [s]
        split_ifs with h0
        · rw [mul_one, abs_of_nonneg h0]
        · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h0)]
      rw [hws]
      exact mul_le_of_le_one_right (abs_nonneg (w i)) (hx i)
    exact h1.trans h2

lemma bilinear_abs_le_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : ∀ (x : Fin m → ℝ) (y : Fin n → ℝ),
      (∀ i, x i = -1 ∨ x i = 1) → (∀ j, y j = -1 ∨ y j = 1) →
        |∑ i, ∑ j, A i j * x i * y j| ≤ 1)
    (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    |∑ i, ∑ j, A i j * x i * y j| ≤ 1 := by
  have h_re1 : ∑ i, ∑ j, A i j * x i * y j = ∑ i, (∑ j, A i j * y j) * x i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨s, hs, h_le1⟩ := abs_sum_mul_le_of_abs_le_one (fun i => ∑ j, A i j * y j) x hx
  have h_re2 : ∑ i, (∑ j, A i j * y j) * s i = ∑ j, (∑ i, A i j * s i) * y j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨t, ht, h_le2⟩ := abs_sum_mul_le_of_abs_le_one (fun j => ∑ i, A i j * s i) y hy
  have h_re3 : ∑ j, (∑ i, A i j * s i) * t j = ∑ i, ∑ j, A i j * s i * t j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  calc |∑ i, ∑ j, A i j * x i * y j|
    _ = |∑ i, (∑ j, A i j * y j) * x i| := by rw [h_re1]
    _ ≤ ∑ i, (∑ j, A i j * y j) * s i := h_le1
    _ = ∑ j, (∑ i, A i j * s i) * y j := h_re2
    _ ≤ |∑ j, (∑ i, A i j * s i) * y j| := le_abs_self _
    _ ≤ ∑ j, (∑ i, A i j * s i) * t j := h_le2
    _ = ∑ i, ∑ j, A i j * s i * t j := h_re3
    _ ≤ |∑ i, ∑ j, A i j * s i * t j| := le_abs_self _
    _ ≤ 1 := hA s t hs ht

lemma abs_real_sign_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

lemma measurable_real_sign : Measurable Real.sign := by
  change Measurable (fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0)
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

lemma embed_unit_vectors {m n : ℕ} {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H) (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ (N : ℕ) (u' : Fin m → EuclideanSpace ℝ (Fin N)) (v' : Fin n → EuclideanSpace ℝ (Fin N)),
      (∀ i, ‖u' i‖ = 1) ∧ (∀ j, ‖v' j‖ = 1) ∧
      (∀ i j, inner ℝ (u' i) (v' j) = inner ℝ (u i) (v j)) := by
  let S : Set H := Set.range u ∪ Set.range v
  have hS : S.Finite := (Set.finite_range u).union (Set.finite_range v)
  let V : Submodule ℝ H := Submodule.span ℝ S
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hS
  let N := Module.finrank ℝ V
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ V).repr
  let uV (i : Fin m) : V := ⟨u i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩
  let vV (j : Fin n) : V := ⟨v j, Submodule.subset_span (Or.inr ⟨j, rfl⟩)⟩
  refine ⟨N, fun i => e (uV i), fun j => e (vV j), fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · rw [e.norm_map]; exact hu i
  · rw [e.norm_map]; exact hv j
  · rw [e.inner_map_map]; rfl

lemma euclidean_sum_sq_eq_one {M : ℕ} (w : EuclideanSpace ℝ (Fin M)) (hw : ‖w‖ = 1) :
    ∑ k : Fin M, (w k) ^ 2 = 1 := by
  have h1 : inner ℝ w w = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hw, mul_one]
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct] at h1
  simpa [sq] using h1

lemma euclidean_sum_mul_eq_inner {M : ℕ} (u v : EuclideanSpace ℝ (Fin M)) :
    ∑ k : Fin M, u k * v k = inner ℝ u v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  refine Finset.sum_congr rfl fun k _ => mul_comm (u k) (v k)

lemma exists_standard_gaussian_vector (M : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (g : Fin M → Ω → ℝ), IsStandardGaussianVector P g := by
  let Ω := Fin M → ℝ
  let P : Measure Ω := Measure.pi (fun _ : Fin M => gaussianReal 0 1)
  let g (k : Fin M) (ω : Ω) : ℝ := ω k
  refine ⟨Ω, inferInstance, P, inferInstance, g, ?_, ?_, ?_⟩
  · intro k
    exact measurable_pi_apply k
  · have h_indep : iIndepFun (fun (k : Fin M) (ω : Ω) => id (ω k)) P :=
      iIndepFun_pi (fun _ => measurable_id.aemeasurable)
    exact h_indep
  · intro k
    exact (MeasureTheory.measurePreserving_eval (fun _ : Fin M => gaussianReal 0 1) k).map_eq

lemma log_one_add_sqrt_two_ge : (881 : ℝ) / 1000 ≤ Real.log (1 + Real.sqrt 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h_bound := Real.exp_bound (x := (881 : ℝ) / 1000) (by norm_num) (n := 7) (by decide)
  have h_abs := (abs_le.mp h_bound).2
  have h_sqrt : (14142 : ℝ) / 10000 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h_abs
  norm_num at h_abs
  linarith

lemma grothendieck_constant_le :
    Real.pi / (2 * Real.log (1 + Real.sqrt 2)) ≤ (1783 : ℝ) / 1000 := by
  have hlog : (881 : ℝ) / 1000 ≤ Real.log (1 + Real.sqrt 2) := log_one_add_sqrt_two_ge
  have hpi : Real.pi < (31416 : ℝ) / 10000 := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end SolGrothendieckInequality

open SolGrothendieckInequality

theorem solution :
    ∃ K : ℝ, 0 < K ∧ K ≤ (1783 : ℝ) / 1000 ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
        (∀ (x : Fin m → ℝ) (y : Fin n → ℝ),
          (∀ i, x i = -1 ∨ x i = 1) → (∀ j, y j = -1 ∨ y j = 1) →
            |∑ i, ∑ j, A i j * x i * y j| ≤ 1) →
        ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          (u : Fin m → H) (v : Fin n → H),
          (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
            |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ K := by
  refine ⟨(1783 : ℝ) / 1000, by norm_num, le_rfl, ?_⟩
  intro m n A hA H _ _ _ u v hu hv
  obtain ⟨N, u', v', hu', hv', huv'⟩ := embed_unit_vectors u v hu hv
  obtain ⟨H1, hN1, hI1, hC1, Φ, Ψ, hΦΨ⟩ :=
    HighDimProbAudit.Grothendieck.sphere_linearization N
  letI := hN1
  letI := hI1
  let u1 (i : Fin m) : H1 := (Φ ⟨u' i, hu' i⟩).val
  let v1 (j : Fin n) : H1 := (Ψ ⟨v' j, hv' j⟩).val
  have hu1 : ∀ i, ‖u1 i‖ = 1 := fun i => (Φ ⟨u' i, hu' i⟩).property
  have hv1 : ∀ j, ‖v1 j‖ = 1 := fun j => (Ψ ⟨v' j, hv' j⟩).property
  obtain ⟨M, p, q, hp, hq, hpq⟩ := embed_unit_vectors u1 v1 hu1 hv1
  obtain ⟨Ω, mΩ, P, hP, g, hg⟩ := exists_standard_gaussian_vector M
  letI := mΩ
  letI := hP
  let X (i : Fin m) (ω : Ω) : ℝ := Real.sign (∑ k : Fin M, g k ω * p i k)
  let Y (j : Fin n) (ω : Ω) : ℝ := Real.sign (∑ k : Fin M, g k ω * q j k)
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    refine measurable_real_sign.comp ?_
    exact Finset.measurable_sum Finset.univ fun k _ => (hg.1 k).mul measurable_const
  have hY_meas : ∀ j, Measurable (Y j) := by
    intro j
    refine measurable_real_sign.comp ?_
    exact Finset.measurable_sum Finset.univ fun k _ => (hg.1 k).mul measurable_const
  have hXY_int : ∀ i j, Integrable (fun ω => A i j * (X i ω * Y j ω)) P := by
    intro i j
    refine Integrable.const_mul ?_ (A i j)
    refine Integrable.of_bound ((hX_meas i).mul (hY_meas j)).aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (abs_real_sign_le_one _) (abs_nonneg _) (abs_real_sign_le_one _)
  let β : ℝ := (2 / Real.pi) * Real.log (1 + Real.sqrt 2)
  have h_entry : ∀ i j, ∫ ω, A i j * (X i ω * Y j ω) ∂P = A i j * (β * inner ℝ (u i) (v j)) := by
    intro i j
    rw [integral_const_mul]
    have h_id := HighDimProb.RandomVectors.grothendieck_identity P g hg (p i) (q j)
      (euclidean_sum_sq_eq_one (p i) (hp i)) (euclidean_sum_sq_eq_one (q j) (hq j))
    change A i j * ∫ ω, X i ω * Y j ω ∂P = _
    rw [h_id, euclidean_sum_mul_eq_inner, hpq i j]
    have h_lin := hΦΨ ⟨u' i, hu' i⟩ ⟨v' j, hv' j⟩
    change (2 / Real.pi) * Real.arcsin (inner ℝ (u1 i) (v1 j)) = β * inner ℝ (u' i) (v' j) at h_lin
    rw [h_lin, huv' i j]
  have h_sum_int : ∫ ω, (∑ i, ∑ j, A i j * X i ω * Y j ω) ∂P =
      β * ∑ i, ∑ j, A i j * inner ℝ (u i) (v j) := by
    have h_fn : (fun ω => ∑ i, ∑ j, A i j * X i ω * Y j ω) =
        fun ω => ∑ i, ∑ j, A i j * (X i ω * Y j ω) := by
      ext ω
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [h_fn, integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ => hXY_int i j))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum Finset.univ (fun j _ => hXY_int i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_entry i j]
    ring
  have h_int_bound : |∫ ω, (∑ i, ∑ j, A i j * X i ω * Y j ω) ∂P| ≤ 1 := by
    have h1 : ‖∫ ω, (∑ i, ∑ j, A i j * X i ω * Y j ω) ∂P‖ ≤ ∫ ω, (1 : ℝ) ∂P := by
      refine norm_integral_le_of_norm_le (integrable_const 1) ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      exact bilinear_abs_le_one A hA (fun i => X i ω) (fun j => Y j ω)
        (fun i => abs_real_sign_le_one _) (fun j => abs_real_sign_le_one _)
    simpa [Real.norm_eq_abs] using h1
  rw [h_sum_int] at h_int_bound
  have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    linarith [log_one_add_sqrt_two_ge]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hβ_pos : 0 < β := by
    dsimp [β]
    positivity
  rw [abs_mul, abs_of_pos hβ_pos] at h_int_bound
  have h_le_inv : |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ 1 / β := by
    rw [le_div_iff₀' hβ_pos]
    exact h_int_bound
  have h_inv_eq : 1 / β = Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
    dsimp [β]
    field_simp
  rw [h_inv_eq] at h_le_inv
  exact h_le_inv.trans grothendieck_constant_le
