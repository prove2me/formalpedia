-- Prove2me | solution 1 for McFadden1974.Asymptotics.expected_hessian_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:19:19.222409+00:00
-- url     : https://prove2.me/submissions/3716ff33-1598-42ae-8cb6-a8492e6447ee

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

set_option autoImplicit false

namespace E1ed2617

open McFadden1974.Asymptotics Matrix

variable {K : ℕ}

/-- the partition function -/
noncomputable def Sf (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ)

/-- its gradient (unnormalized) -/
noncomputable def Tf (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ :=
  ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j)

lemma Sf_pos (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) : 0 < Sf D m θ := by
  have : Nonempty (Fin (D.J m)) := ⟨⟨0, D.one_le_J m⟩⟩
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

lemma hasFDerivAt_Sf (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (Sf D m) (Tf D m θ) θ := by
  unfold Sf Tf
  have h : ∀ j ∈ (Finset.univ : Finset (Fin (D.J m))),
      HasFDerivAt (fun θ => Real.exp (inner ℝ (D.z m j) θ))
        (Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j)) θ := by
    intro j _
    have := ((innerSL ℝ (D.z m j)).hasFDerivAt (x := θ)).exp
    simpa using this
  simpa using HasFDerivAt.fun_sum h

lemma log_prob_eq (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) :
    (fun θ => Real.log (prob D m i θ)) =
      fun θ => inner ℝ (D.z m i) θ - Real.log (Sf D m θ) := by
  funext θ
  show Real.log (Real.exp (inner ℝ (D.z m i) θ) / Sf D m θ) = _
  rw [Real.log_div (Real.exp_pos _).ne' (Sf_pos D m θ).ne', Real.log_exp]

lemma hasFDerivAt_logS (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ => Real.log (Sf D m θ)) ((Sf D m θ)⁻¹ • Tf D m θ) θ :=
  (hasFDerivAt_Sf D m θ).log (Sf_pos D m θ).ne'

lemma fderiv_logprob (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) :
    fderiv ℝ (fun θ => Real.log (prob D m i θ)) =
      fun θ => innerSL ℝ (D.z m i) - (Sf D m θ)⁻¹ • Tf D m θ := by
  rw [log_prob_eq]
  funext θ
  have h1 : HasFDerivAt (fun θ => inner ℝ (D.z m i) θ) (innerSL ℝ (D.z m i)) θ := by
    simpa using (innerSL ℝ (D.z m i)).hasFDerivAt (x := θ)
  exact (h1.sub (hasFDerivAt_logS D m θ)).fderiv

lemma hasFDerivAt_Tf (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (Tf D m)
      (∑ j : Fin (D.J m), (Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j)).smulRight
        (innerSL ℝ (D.z m j))) θ := by
  unfold Tf
  have h : ∀ j ∈ (Finset.univ : Finset (Fin (D.J m))),
      HasFDerivAt (fun θ => Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j))
        ((Real.exp (inner ℝ (D.z m j) θ) • innerSL ℝ (D.z m j)).smulRight
          (innerSL ℝ (D.z m j))) θ := by
    intro j _
    have := ((innerSL ℝ (D.z m j)).hasFDerivAt (x := θ)).exp
    simp only [innerSL_apply_apply] at this
    exact this.smul_const (innerSL ℝ (D.z m j))
  simpa using HasFDerivAt.fun_sum h

lemma hasFDerivAt_invS (D : SerialData K) (m : ℕ) (θ : EuclideanSpace ℝ (Fin K)) :
    HasFDerivAt (fun θ => (Sf D m θ)⁻¹) ((-(Sf D m θ ^ 2)⁻¹) • Tf D m θ) θ :=
  (hasDerivAt_inv (Sf_pos D m θ).ne').comp_hasFDerivAt θ (hasFDerivAt_Sf D m θ)

lemma second (D : SerialData K) (m : ℕ) (i : Fin (D.J m)) (θ₀ u v : EuclideanSpace ℝ (Fin K)) :
    iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m i θ)) θ₀ ![u, v] =
      -( (Sf D m θ₀)⁻¹ * ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) *
            inner ℝ (D.z m j) u * inner ℝ (D.z m j) v
        - (Sf D m θ₀ ^ 2)⁻¹ * (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) *
            inner ℝ (D.z m j) u) *
          (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) v)) := by
  rw [iteratedFDeriv_two_apply, fderiv_logprob]
  have hG : HasFDerivAt (fun θ => innerSL ℝ (D.z m i) - (Sf D m θ)⁻¹ • Tf D m θ) _ θ₀ :=
    ((hasFDerivAt_invS D m θ₀).smul (hasFDerivAt_Tf D m θ₀)).const_sub (innerSL ℝ (D.z m i))
  rw [hG.fderiv]
  simp only [Tf, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma dot_ofLp (a b : EuclideanSpace ℝ (Fin K)) :
    WithLp.ofLp a ⬝ᵥ WithLp.ofLp b = inner ℝ b a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

lemma inner_zbar (D : SerialData K) (m : ℕ) (θ x : EuclideanSpace ℝ (Fin K)) :
    inner ℝ (zbar D m θ) x =
      (Sf D m θ)⁻¹ * ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) * inner ℝ (D.z m j) x := by
  unfold zbar
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_smul_left]
  show Real.exp (inner ℝ (D.z m j) θ) / Sf D m θ * _ = _
  ring

lemma rhs (D : SerialData K) (m : ℕ) (θ₀ u v : EuclideanSpace ℝ (Fin K)) :
    -(WithLp.ofLp u ⬝ᵥ (momentMatrix D θ₀ m *ᵥ WithLp.ofLp v)) =
      -( (Sf D m θ₀)⁻¹ * ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) *
            inner ℝ (D.z m j) u * inner ℝ (D.z m j) v
        - (Sf D m θ₀ ^ 2)⁻¹ * (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) *
            inner ℝ (D.z m j) u) *
          (∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) v)) := by
  congr 1
  unfold momentMatrix
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul,
    smul_eq_mul, dot_ofLp]
  simp only [real_inner_comm _ v]
  simp only [inner_sub_left, inner_zbar]
  set S := Sf D m θ₀ with hS
  set A := ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) u
  set B := ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) v
  have hSpos : 0 < S := Sf_pos D m θ₀
  have hp : ∀ j, prob D m j θ₀ = Real.exp (inner ℝ (D.z m j) θ₀) / S := fun j => rfl
  have hsum : ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ₀) = S := rfl
  have key : ∀ j : Fin (D.J m),
      prob D m j θ₀ * ((inner ℝ (D.z m j) v - S⁻¹ * B) * (inner ℝ (D.z m j) u - S⁻¹ * A)) =
        S⁻¹ * (Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) u * inner ℝ (D.z m j) v)
        - (S⁻¹ * S⁻¹ * B) * (Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) u)
        - (S⁻¹ * S⁻¹ * A) * (Real.exp (inner ℝ (D.z m j) θ₀) * inner ℝ (D.z m j) v)
        + (S⁻¹ * S⁻¹ * S⁻¹ * A * B) * Real.exp (inner ℝ (D.z m j) θ₀) := by
    intro j; rw [hp]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  field_simp
  ring

end E1ed2617

open McFadden1974.Asymptotics MeasureTheory ProbabilityTheory Filter Topology Matrix in
theorem solution {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (m : ℕ) (u v : EuclideanSpace ℝ (Fin K)) :
    Integrable (fun ω =>
        iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ![u, v]) μ ∧
      ∫ ω, iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ![u, v] ∂μ =
        -(WithLp.ofLp u ⬝ᵥ (momentMatrix D θ₀ m *ᵥ WithLp.ofLp v)) := by
  have h : (fun ω =>
        iteratedFDeriv ℝ 2 (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀ ![u, v]) =
      fun _ => -(WithLp.ofLp u ⬝ᵥ (momentMatrix D θ₀ m *ᵥ WithLp.ofLp v)) := by
    funext ω
    rw [E1ed2617.second, E1ed2617.rhs]
  rw [h]
  refine ⟨integrable_const _, ?_⟩
  simp
