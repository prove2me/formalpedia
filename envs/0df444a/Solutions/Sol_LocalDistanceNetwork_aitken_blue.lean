-- Prove2me | solution 1 for LocalDistanceNetwork.aitken_blue
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:43:14.504426+00:00
-- url     : https://prove2.me/submissions/e8936869-70ec-48e2-a239-7a1182011e99

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
open Matrix LocalDistanceNetwork

namespace GLSAux

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

lemma M_posDef (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) : (Aᵀ * W * A).PosDef := by
  have := hW.conjTranspose_mul_mul_same hA
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma M_det (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) : IsUnit (Aᵀ * W * A).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (M_posDef A hA W hW).isUnit

lemma unbiased (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) : glsEstimatorMatrix A W * A = 1 := by
  unfold glsEstimatorMatrix
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ,
    Matrix.nonsing_inv_mul _ (M_det A hA W hW)]

lemma symm_of_posDef {k : Type*} [Fintype k] (C : Matrix k k ℝ) (hC : C.PosDef) : Cᵀ = C := by
  have := hC.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

lemma covariance [DecidableEq m] (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef) :
    linearEstimatorCov (glsEstimatorMatrix A C⁻¹) C = (Aᵀ * C⁻¹ * A)⁻¹ := by
  have hCi : C⁻¹.PosDef := hC.inv
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit
  set M := Aᵀ * C⁻¹ * A with hM
  have hMdet := M_det A hA C⁻¹ hCi
  have hMs : Mᵀ = M := symm_of_posDef M (M_posDef A hA C⁻¹ hCi)
  have hCis : (C⁻¹)ᵀ = C⁻¹ := symm_of_posDef _ hCi
  unfold linearEstimatorCov glsEstimatorMatrix
  rw [← hM]
  simp only [transpose_mul, hCis, transpose_transpose, transpose_nonsing_inv, hMs]
  calc M⁻¹ * Aᵀ * C⁻¹ * C * (C⁻¹ * (A * M⁻¹))
      = M⁻¹ * Aᵀ * (C⁻¹ * C) * (C⁻¹ * (A * M⁻¹)) := by simp only [Matrix.mul_assoc]
    _ = M⁻¹ * (Aᵀ * C⁻¹ * A) * M⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hCdet]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = M⁻¹ := by rw [← hM, Matrix.nonsing_inv_mul _ hMdet, Matrix.one_mul]

end GLSAux

namespace GLSAux

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

lemma aitken [DecidableEq m] (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (L : Matrix n m ℝ) (hL : L * A = 1) :
    (linearEstimatorCov L C - (Aᵀ * C⁻¹ * A)⁻¹).PosSemidef := by
  set G := glsEstimatorMatrix A C⁻¹ with hG
  set D := L - G with hD
  have hCi : C⁻¹.PosDef := hC.inv
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).mp hC.isUnit
  have hGA : G * A = 1 := unbiased A hA C⁻¹ hCi
  have hDA : D * A = 0 := by rw [hD, Matrix.sub_mul, hL, hGA, sub_self]
  have hCs : Cᵀ = C := symm_of_posDef C hC
  have hCis : (C⁻¹)ᵀ = C⁻¹ := symm_of_posDef _ hCi
  set M := Aᵀ * C⁻¹ * A with hM
  have hMs : Mᵀ = M := symm_of_posDef M (M_posDef A hA C⁻¹ hCi)
  -- cross term vanishes
  have hcross : G * C * Dᵀ = 0 := by
    rw [hG]; unfold glsEstimatorMatrix
    rw [← hM]
    calc M⁻¹ * Aᵀ * C⁻¹ * C * Dᵀ = M⁻¹ * Aᵀ * (C⁻¹ * C) * Dᵀ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (D * A)ᵀ := by
          rw [Matrix.nonsing_inv_mul _ hCdet, transpose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hDA, transpose_zero, Matrix.mul_zero]
  have hcross' : D * C * Gᵀ = 0 := by
    have := congrArg Matrix.transpose hcross
    rw [transpose_mul, transpose_mul, transpose_transpose, hCs, transpose_zero] at this
    rw [← this]; simp only [Matrix.mul_assoc]
  have hcov := covariance A hA C hC
  have hL' : L = G + D := by rw [hD]; abel
  have key : linearEstimatorCov L C - M⁻¹ = D * C * Dᵀ := by
    rw [← hcov]
    unfold linearEstimatorCov
    rw [hL', transpose_add]
    simp only [Matrix.add_mul, Matrix.mul_add]
    rw [hcross, hcross']
    abel
  rw [key]
  have := hC.posSemidef.mul_mul_conjTranspose_same D
  rwa [conjTranspose_eq_transpose_of_trivial] at this

end GLSAux

namespace GLSAux

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

lemma minimizes (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (W : Matrix m m ℝ) (hW : W.PosDef) (Y : m → ℝ) (X : n → ℝ) :
    glsObjective A W Y (glsEstimate A W Y) ≤ glsObjective A W Y X := by
  set M := Aᵀ * W * A with hM
  have hMdet := M_det A hA W hW
  have hWs : Wᵀ = W := symm_of_posDef W hW
  set Xh := glsEstimate A W Y with hXh
  set r := Y - A *ᵥ Xh with hr
  set d := X - Xh with hd
  have hres : Y - A *ᵥ X = r - A *ᵥ d := by
    rw [hr, hd, mulVec_sub]; abel
  have hzero : (Aᵀ * W) *ᵥ r = 0 := by
    rw [hr, mulVec_sub, hXh]
    unfold glsEstimate glsEstimatorMatrix
    rw [mulVec_mulVec, mulVec_mulVec]
    have : Aᵀ * W * A * (M⁻¹ * Aᵀ * W) = Aᵀ * W := by
      calc Aᵀ * W * A * (M⁻¹ * Aᵀ * W) = (Aᵀ * W * A) * M⁻¹ * (Aᵀ * W) := by
            simp only [Matrix.mul_assoc]
        _ = Aᵀ * W := by rw [Matrix.mul_nonsing_inv _ hMdet, Matrix.one_mul]
    rw [this, sub_self]
  -- the two cross terms vanish
  have hc1 : (A *ᵥ d) ⬝ᵥ (W *ᵥ r) = 0 := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hzero,
      zero_dotProduct]
  have hc2 : r ⬝ᵥ (W *ᵥ (A *ᵥ d)) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hWs, dotProduct_comm, hc1]
  have hpsd : 0 ≤ (A *ᵥ d) ⬝ᵥ (W *ᵥ (A *ᵥ d)) := by
    have := hW.posSemidef.dotProduct_mulVec_nonneg (A *ᵥ d)
    simpa using this
  have hQX : glsObjective A W Y X = r ⬝ᵥ (W *ᵥ r) - r ⬝ᵥ (W *ᵥ (A *ᵥ d)) -
      ((A *ᵥ d) ⬝ᵥ (W *ᵥ r) - (A *ᵥ d) ⬝ᵥ (W *ᵥ (A *ᵥ d))) := by
    have gen : ∀ u v : m → ℝ, (u - v) ⬝ᵥ (W *ᵥ (u - v)) =
        u ⬝ᵥ (W *ᵥ u) - u ⬝ᵥ (W *ᵥ v) - (v ⬝ᵥ (W *ᵥ u) - v ⬝ᵥ (W *ᵥ v)) := by
      intro u v
      rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]; ring
    unfold glsObjective
    rw [hres, gen]
  have hQh : glsObjective A W Y Xh = r ⬝ᵥ (W *ᵥ r) := rfl
  rw [hQX, hQh, hc1, hc2]
  linarith

end GLSAux

open MeasureTheory ProbabilityTheory

namespace GLSVar

lemma var_linear {m n : Type*} [Fintype m] [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Matrix m m ℝ) (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (A : Matrix m n ℝ) (X₀ : n → ℝ) (L : Matrix n m ℝ) (v : n → ℝ) :
    Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] = v ⬝ᵥ (linearEstimatorCov L C *ᵥ v) := by
  set w := Lᵀ *ᵥ v with hw
  set c := v ⬝ᵥ (L *ᵥ (A *ᵥ X₀)) with hc
  have hfun : (fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω))) =
      fun ω => c + ∑ i, w i * ε ω i := by
    funext ω
    rw [mulVec_add, dotProduct_add]
    congr 1
    rw [dotProduct_mulVec, ← mulVec_transpose]
    rfl
  have hmem : ∀ i, MemLp (fun ω => w i * ε ω i) 2 μ := fun i => (hε i).const_mul (w i)
  have hS : MemLp (fun ω => ∑ i, w i * ε ω i) 2 μ := memLp_finsetSum _ fun i _ => hmem i
  rw [hfun, variance_const_add hS.aestronglyMeasurable, ← covariance_self hS.aemeasurable,
    covariance_fun_sum_fun_sum hmem hmem]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hcov]
  unfold linearEstimatorCov
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, ← hw]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GLSVar

namespace GLSVar

lemma mean_linear {m n : Type*} [Fintype m] [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : Ω → m → ℝ) (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (L : Matrix n m ℝ) (y : m → ℝ) (j : n) :
    μ[fun ω => (L *ᵥ (y + ε ω)) j] = (L *ᵥ y) j + ∑ i, L j i * μ[fun ω => ε ω i] := by
  have hint : ∀ i, Integrable (fun ω => ε ω i) μ := fun i => (hε i).integrable (by norm_num)
  have hfun : (fun ω => (L *ᵥ (y + ε ω)) j) = fun ω => (L *ᵥ y) j + ∑ i, L j i * ε ω i := by
    funext ω
    rw [mulVec_add, Pi.add_apply]
    rfl
  rw [hfun, integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => (hint i).const_mul _),
    integral_const, integral_finset_sum _ fun i _ => (hint i).const_mul _]
  simp [integral_const_mul]

end GLSVar

theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, μ[fun ω => ε ω i] = 0)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (X₀ : n → ℝ) :
    (∀ j, μ[fun ω => glsEstimate A C⁻¹ (A *ᵥ X₀ + ε ω) j] = X₀ j) ∧
    ∀ L : Matrix n m ℝ,
      (∀ X₁ : n → ℝ, ∀ j, μ[fun ω => (L *ᵥ (A *ᵥ X₁ + ε ω)) j] = X₁ j) →
      ∀ v : n → ℝ,
        Var[fun ω => v ⬝ᵥ glsEstimate A C⁻¹ (A *ᵥ X₀ + ε ω); μ] ≤
          Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] := by
  set G := glsEstimatorMatrix A C⁻¹ with hG
  have hGA : G * A = 1 := GLSAux.unbiased A hA C⁻¹ hC.inv
  have hmeanL : ∀ (L : Matrix n m ℝ) (y : m → ℝ) (j : n),
      μ[fun ω => (L *ᵥ (y + ε ω)) j] = (L *ᵥ y) j := by
    intro L y j
    rw [GLSVar.mean_linear μ ε hε L y j]
    simp [hmean]
  refine ⟨fun j => ?_, fun L hL v => ?_⟩
  · unfold glsEstimate
    rw [← hG, hmeanL, mulVec_mulVec, hGA, one_mulVec]
  · have hLA : L * A = 1 := by
      ext j k
      have h := hL (Pi.single k 1) j
      rw [hmeanL, mulVec_mulVec] at h
      have e : ((L * A) *ᵥ Pi.single k 1) j = (L * A) j k := by
        simp [mulVec, dotProduct, Pi.single_apply]
      rw [e] at h
      rw [h, Matrix.one_apply, Pi.single_apply]
    unfold glsEstimate
    rw [← hG, GLSVar.var_linear μ C ε hε hcov A X₀ G v, GLSVar.var_linear μ C ε hε hcov A X₀ L v,
      hG, GLSAux.covariance A hA C hC]
    have hpsd := GLSAux.aitken A hA C hC L hLA
    have := hpsd.dotProduct_mulVec_nonneg v
    simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
    linarith
