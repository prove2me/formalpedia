-- Prove2me | solution 1 for MilnorDynamics.gl_action_uniformContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T13:18:32.530497+00:00
-- url     : https://prove2.me/submissions/a45e57c3-f8da-4339-868e-d0dd0f9da7be

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint Topology
open Bornology
open Filter Set
open MilnorDynamics

/-- The embedded coordinates of a point of the sphere, as a plain vector. -/
def embedF : OnePoint ℂ → (Fin 2 → ℂ)
  | some z => ![z, 1]
  | none => ![1, 0]

/-- Embedding of the Riemann sphere into `ℂ²`: `z ↦ (z, 1)`, `∞ ↦ (1, 0)`. -/
noncomputable def embed (x : OnePoint ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (embedF x)

/-- `Kz z = √(1 + ‖z‖ ^ 2)`. -/
noncomputable def Kz (z : ℂ) : ℝ := Real.sqrt (1 + ‖z‖ ^ 2)

lemma norm_embed_coe (z : ℂ) : ‖embed (↑z : OnePoint ℂ)‖ = Kz z := by
  rw [EuclideanSpace.norm_eq, Kz]
  simp [embed, embedF, WithLp.ofLp_toLp, Fin.sum_univ_two, add_comm]

lemma norm_embed_infty : ‖embed (∞ : OnePoint ℂ)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [embed, embedF, WithLp.ofLp_toLp, Real.sqrt_one]

lemma embed_ne_zero (x : OnePoint ℂ) : embed x ≠ 0 := by
  intro h
  have h' : embedF x = 0 := by
    have := congrArg WithLp.ofLp h
    simpa [embed, WithLp.ofLp_toLp] using this
  cases x with
  | infty => exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa [embedF] using congrFun h' 0)
  | coe z => exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa [embedF] using congrFun h' 1)

/-- Determinant of the two coordinate columns of `ℂ²`. -/
def det2 (u v : EuclideanSpace ℂ (Fin 2)) : ℂ := u 0 * v 1 - u 1 * v 0

lemma det2_smul (c d : ℂ) (u v : EuclideanSpace ℂ (Fin 2)) :
    det2 (c • u) (d • v) = c * d * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The chordal distance is the Fubini–Study ratio of the embedded vectors. -/
lemma chordalDist_nonneg (x y : OnePoint ℂ) : 0 ≤ chordalDist x y := by
  cases x <;> cases y <;> simp [chordalDist] <;> positivity

/-- The chordal distance is the Fubini–Study ratio of the embedded vectors. -/
lemma chordalDist_eq_det2 (x y : OnePoint ℂ) :
    chordalDist x y = 2 * ‖det2 (embed x) (embed y)‖ / (‖embed x‖ * ‖embed y‖) := by
  cases x with
  | infty =>
      cases y with
      | infty =>
          rw [MilnorDynamics.chordalDist.eq_def, norm_embed_infty]
          simp [det2, embed, embedF, WithLp.ofLp_toLp, Kz]
      | coe b =>
          rw [MilnorDynamics.chordalDist.eq_def, norm_embed_infty, norm_embed_coe]
          simp [det2, embed, embedF, WithLp.ofLp_toLp, Kz]
  | coe a =>
      cases y with
      | infty =>
          rw [MilnorDynamics.chordalDist.eq_def, norm_embed_coe, norm_embed_infty]
          simp [det2, embed, embedF, WithLp.ofLp_toLp, Kz]
      | coe b =>
          rw [MilnorDynamics.chordalDist.eq_def, norm_embed_coe, norm_embed_coe]
          simp [det2, embed, embedF, WithLp.ofLp_toLp, Kz]

/-- The linear map of `ℂ²` attached to a matrix. -/
noncomputable def mobiusP (A : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin A

lemma mobiusP_comp (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    mobiusP (A * B) v = mobiusP A (mobiusP B v) := by
  simp only [mobiusP]
  rw [Matrix.toLpLin_mul_same]
  rfl

lemma mobiusP_one (v : EuclideanSpace ℂ (Fin 2)) :
    mobiusP (1 : Matrix (Fin 2) (Fin 2) ℂ) v = v := by
  simp [mobiusP, Matrix.toLpLin_one]

lemma mobiusP_unit_inv (g : GL (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) (mobiusP (↑g) v) = v := by
  rw [← mobiusP_comp]
  have h : (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) * (↑g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
  rw [h]
  exact mobiusP_one v

lemma mobiusP_unit_mul (g : GL (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    mobiusP (↑g) (mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) v) = v := by
  rw [← mobiusP_comp]
  have h : (↑g : Matrix (Fin 2) (Fin 2) ℂ) * (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp
  rw [h]
  exact mobiusP_one v

/-- The matrix action as a linear equivalence of `ℂ²`. -/
noncomputable def mobiusE (g : GL (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearEquiv.ofBijective (mobiusP (↑g))
    ⟨fun v w h => by
      have h' : mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) (mobiusP (↑g) v)
          = mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) (mobiusP (↑g) w) :=
        congrArg (fun u => mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) u) h
      rw [mobiusP_unit_inv g v, mobiusP_unit_inv g w] at h'
      exact h',
     fun w => ⟨mobiusP ((↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) w, mobiusP_unit_mul g w⟩⟩

/-- Its upgrade to a continuous linear equivalence. -/
noncomputable def mobiusC (g : GL (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) ≃L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquivOfContinuous (mobiusE g)
    (LinearMap.continuous_of_finiteDimensional (mobiusE g).toLinearMap)

/-- The inverse of the matrix action, as a continuous linear map. -/
noncomputable def mobiusCinv (g : GL (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (mobiusC g).symm

lemma mobiusCinv_pos (g : GL (Fin 2) ℂ) : 0 < ‖mobiusCinv g‖ := by
  simpa only [mobiusCinv] using (mobiusC g).norm_symm_pos

/-- The determinant of an invertible matrix has positive norm. -/
lemma det_norm_pos (g : GL (Fin 2) ℂ) :
    0 < ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ := by
  refine norm_pos_iff.mpr fun h0 => g.det_ne_zero h0

lemma mobiusC_bound (g : GL (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖v‖ ≤ ‖mobiusCinv g‖ * ‖mobiusC g v‖ := by
  have h : mobiusCinv g (mobiusC g v) = v :=
    ContinuousLinearEquiv.symm_apply_apply (mobiusC g) v
  calc ‖v‖ = ‖mobiusCinv g (mobiusC g v)‖ := by rw [h]
    _ ≤ ‖mobiusCinv g‖ * ‖mobiusC g v‖ := ContinuousLinearMap.le_opNorm (mobiusCinv g) _

/-- Coordinates of the matrix action. -/
lemma mobiusP_apply (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    mobiusP A v i = A i 0 * v 0 + A i 1 * v 1 := by
  simp only [mobiusP, Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_apply_eq_sum,
    Fin.sum_univ_two]

lemma mobiusE_apply (g : GL (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    mobiusE g v i = (↑g : Matrix (Fin 2) (Fin 2) ℂ) i 0 * v 0
      + (↑g : Matrix (Fin 2) (Fin 2) ℂ) i 1 * v 1 :=
  mobiusP_apply (↑g) v i

/-- The underlying linear map of `mobiusE` is `mobiusP`. -/
lemma mobiusE_apply_eq (g : GL (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    mobiusE g v = mobiusP (↑g) v := rfl

/-- The matrix action on the *unwrapped* coordinates. -/
lemma ofLp_mobiusP (A : Matrix (Fin 2) (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    WithLp.ofLp (mobiusP A v) = A.mulVec (WithLp.ofLp v) := by
  rw [mobiusP, Matrix.toLpLin_apply, WithLp.ofLp_toLp]

lemma ofLp_embed_infty : WithLp.ofLp (embed (∞ : OnePoint ℂ)) = (![1, 0] : Fin 2 → ℂ) := by
  simp [embed, embedF, WithLp.ofLp_toLp]

lemma ofLp_embed_coe (z : ℂ) :
    WithLp.ofLp (embed (z : OnePoint ℂ)) = (![z, 1] : Fin 2 → ℂ) := by
  simp [embed, embedF, WithLp.ofLp_toLp]

/-- The embedded sphere and the matrix action commute up to a nonzero scalar. -/
lemma mobiusE_embed_prop (g : GL (Fin 2) ℂ) (x : OnePoint ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ mobiusE g (embed x) = c • embed (g • x) := by
  have hdet : (↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
      - (↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 := by
    have h := g.det_ne_zero
    rwa [Matrix.det_fin_two] at h
  cases x with
  | infty =>
      rw [OnePoint.smul_infty_eq_ite]
      by_cases hr : (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
      · refine ⟨(↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 0, ?_, ?_⟩
        · intro h0
          exact hdet (by rw [hr, h0]; ring)
        · rw [if_pos hr]
          apply WithLp.ofLp_injective
          rw [mobiusE_apply_eq, ofLp_mobiusP, WithLp.ofLp_smul, ofLp_embed_infty]
          ext i
          fin_cases i <;>
            simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, hr]
      · refine ⟨(↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0, hr, ?_⟩
        rw [if_neg hr]
        apply WithLp.ofLp_injective
        rw [mobiusE_apply_eq, ofLp_mobiusP, WithLp.ofLp_smul, ofLp_embed_coe, ofLp_embed_infty]
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, hr, div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]

  | coe a =>
      by_cases hp : (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a
          + (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0
      · refine ⟨(↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a
            + (↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 1, ?_, ?_⟩
        · intro h0
          exact hdet (by
            have e1 : (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
                = -((↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a) := by
              linear_combination hp
            have e2 : (↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
                = -((↑g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a) := by
              linear_combination h0
            rw [e1, e2]
            ring)
        · rw [OnePoint.smul_some_eq_ite, if_pos hp]
          apply WithLp.ofLp_injective
          rw [mobiusE_apply_eq, ofLp_mobiusP, WithLp.ofLp_smul, ofLp_embed_coe, ofLp_embed_infty]
          ext i
          fin_cases i <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, hp]
      · refine ⟨(↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a
            + (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 1, hp, ?_⟩
        rw [OnePoint.smul_some_eq_ite, if_neg hp]
        have hq : a * (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 + (↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
          intro h
          exact hp (by rwa [mul_comm a ((↑g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)] at h)
        apply WithLp.ofLp_injective
        rw [mobiusE_apply_eq, ofLp_mobiusP, WithLp.ofLp_smul, ofLp_embed_coe, ofLp_embed_coe]
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, hp, hq, div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]

/-- `det2` is multiplicative under the matrix action. -/
lemma det2_mobiusE (g : GL (Fin 2) ℂ) (u v : EuclideanSpace ℂ (Fin 2)) :
    det2 (mobiusE g u) (mobiusE g v) = ((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det * det2 u v := by
  simp only [det2, mobiusE_apply]
  rw [Matrix.det_fin_two]
  ring

/-- Chordal distance of the images as a Fubini–Study ratio of the matrix images. -/
lemma chordal_smul_eq (g : GL (Fin 2) ℂ) (x y : OnePoint ℂ) :
    chordalDist (g • x) (g • y) =
      2 * ‖det2 (mobiusE g (embed x)) (mobiusE g (embed y))‖
        / (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖) := by
  obtain ⟨c, hc, hx⟩ := mobiusE_embed_prop g x
  obtain ⟨d, hd, hy⟩ := mobiusE_embed_prop g y
  have hcx : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hdx : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hx0 : ‖embed (g • x)‖ ≠ 0 := norm_ne_zero_iff.mpr (embed_ne_zero _)
  have hy0 : ‖embed (g • y)‖ ≠ 0 := norm_ne_zero_iff.mpr (embed_ne_zero _)
  rw [hx, hy, det2_smul, norm_mul, norm_mul, norm_smul, norm_smul,
    chordalDist_eq_det2 (g • x) (g • y)]
  field_simp

/-- The division-free chordal identity. -/
lemma chordal_identity (g : GL (Fin 2) ℂ) (x y : OnePoint ℂ) :
    chordalDist (g • x) (g • y) * (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖)
      = ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * chordalDist x y
        * (‖embed x‖ * ‖embed y‖) := by
  have hx0 : ‖embed x‖ ≠ 0 := norm_ne_zero_iff.mpr (embed_ne_zero x)
  have hy0 : ‖embed y‖ ≠ 0 := norm_ne_zero_iff.mpr (embed_ne_zero y)
  have hMx : mobiusE g (embed x) ≠ 0 := fun h =>
    embed_ne_zero x ((mobiusE g).injective (by simpa using h))
  have hMy : mobiusE g (embed y) ≠ 0 := fun h =>
    embed_ne_zero y ((mobiusE g).injective (by simpa using h))
  have hX0 : ‖mobiusE g (embed x)‖ ≠ 0 := norm_ne_zero_iff.mpr hMx
  have hY0 : ‖mobiusE g (embed y)‖ ≠ 0 := norm_ne_zero_iff.mpr hMy
  rw [chordal_smul_eq, det2_mobiusE, chordalDist_eq_det2 x y, norm_mul]
  field_simp [hx0, hy0, hX0, hY0]

/-- The uniform Lipschitz estimate with an explicit constant. -/
lemma chordal_smul_le (g : GL (Fin 2) ℂ) (x y : OnePoint ℂ) :
    chordalDist (g • x) (g • y)
      ≤ (‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g‖ ^ 2)
        * chordalDist x y := by
  have hkey := chordal_identity g x y
  have hx0 : 0 < ‖mobiusE g (embed x)‖ := by
    refine norm_pos_iff.mpr fun h0 => embed_ne_zero x ((mobiusE g).injective ?_)
    rw [h0, map_zero]
  have hy0 : 0 < ‖mobiusE g (embed y)‖ := by
    refine norm_pos_iff.mpr fun h0 => embed_ne_zero y ((mobiusE g).injective ?_)
    rw [h0, map_zero]
  have h1 : ‖embed x‖ ≤ ‖mobiusCinv g‖ * ‖mobiusE g (embed x)‖ :=
    mobiusC_bound g (embed x)
  have h2 : ‖embed y‖ ≤ ‖mobiusCinv g‖ * ‖mobiusE g (embed y)‖ :=
    mobiusC_bound g (embed y)
  have hb : ‖embed x‖ * ‖embed y‖
      ≤ ‖mobiusCinv g‖ ^ 2 * (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖) := by
    have hm := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    nlinarith [hm]
  have hC : 0 < ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ := det_norm_pos g
  calc chordalDist (g • x) (g • y)
      = ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * chordalDist x y
          * (‖embed x‖ * ‖embed y‖) / (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖) := by
        rw [eq_div_iff (mul_ne_zero hx0.ne' hy0.ne')]
        exact hkey
    _ ≤ ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * chordalDist x y
          * (‖mobiusCinv g‖ ^ 2
            * (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖))
          / (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖) := by
        have hA : ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * chordalDist x y
              * (‖embed x‖ * ‖embed y‖)
            ≤ ‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * chordalDist x y
              * (‖mobiusCinv g‖ ^ 2 * (‖mobiusE g (embed x)‖ * ‖mobiusE g (embed y)‖)) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (chordalDist_nonneg x y))
        exact div_le_div_of_nonneg_right hA (by positivity)
    _ = (‖(((↑g : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g‖ ^ 2)
          * chordalDist x y := by
        field_simp
        try ring

theorem solution (g : GL (Fin 2) ℂ) :
    (∀ ε > 0, ∃ δ > 0, ∀ x y : OnePoint ℂ,
        chordalDist x y < δ → chordalDist (g • x) (g • y) < ε) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x y : OnePoint ℂ,
        chordalDist x y < δ → chordalDist (g⁻¹ • x) (g⁻¹ • y) < ε) := by
  have key : ∀ g' : GL (Fin 2) ℂ, ∀ ε > 0, ∃ δ > 0, ∀ x y : OnePoint ℂ,
      chordalDist x y < δ → chordalDist (g' • x) (g' • y) < ε := by
    intro g' ε hε
    have hC : 0 < ‖(((↑g' : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g'‖ ^ 2 :=
      mul_pos (det_norm_pos g') (pow_pos (mobiusCinv_pos g') 2)
    refine ⟨ε / (‖(((↑g' : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g'‖ ^ 2),
      div_pos hε hC, ?_⟩
    intro x y hxy
    have hle := chordal_smul_le g' x y
    calc chordalDist (g' • x) (g' • y)
        ≤ (‖(((↑g' : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g'‖ ^ 2)
            * chordalDist x y := hle
      _ < (‖(((↑g' : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g'‖ ^ 2)
            * (ε / (‖(((↑g' : Matrix (Fin 2) (Fin 2) ℂ)).det : ℂ)‖ * ‖mobiusCinv g'‖ ^ 2)) := by
          exact mul_lt_mul_of_pos_left hxy hC
      _ = ε := by
          rw [mul_div_assoc']
          exact mul_div_cancel_left₀ ε hC.ne'
  exact ⟨key g, key g⁻¹⟩
