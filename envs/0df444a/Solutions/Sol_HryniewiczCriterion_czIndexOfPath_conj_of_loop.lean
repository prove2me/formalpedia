-- Prove2me | solution 1 for HryniewiczCriterion.czIndexOfPath_conj_of_loop
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T17:52:21.830482+00:00
-- url     : https://prove2.me/submissions/344ea40c-202d-42b7-9281-3c36700f55d5

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Definitions.Def_HryniewiczCriterion_GraphAngle
import Theorems.Thm_FiniteEnergyPlane_czIndex_eq_czIndexOfPath
import Theorems.Thm_ConleyZehnder_czIndex_naturality
import Theorems.Thm_ConleyZehnder_czIndex_loop
import Theorems.Thm_ConleyZehnder_maslovValue_existsUnique
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous

open HryniewiczCriterion
open ConleyZehnder HryniewiczCriterion Matrix
open ConleyZehnder HryniewiczCriterion Matrix Set

namespace CZBH

noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

theorem trace_mat1 (A : Mat 1) : A.trace = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.trace, Fintype.sum_sum_type]


theorem det_mat1 (A : Mat 1) : A.det = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) * A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) := by
  rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl


theorem cld_mat1 (A : Mat 1) :
    complexLinearDet A = ⟨(A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2, (A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)) / 2⟩ := by
  unfold complexLinearDet complexLinearPart
  rw [Matrix.det_unique]
  apply Complex.ext <;>
    simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.fromBlocks] <;> ring


theorem det_eq_one (A : Mat 1) (hA : IsSymplectic A) : A.det = 1 := by
  have h := (SymplecticGroup.mem_iff (A := A)).1 hA
  have h' := congrFun (congrFun h (Sum.inl 0 : Fin 1 ⊕ Fin 1)) (Sum.inr 0 : Fin 1 ⊕ Fin 1)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.transpose_apply] at h'
  rw [det_mat1]
  linarith


theorem det_one_sub (A : Mat 1) (hA : IsSymplectic A) : (1 - A).det = 2 - A.trace := by
  have h := det_eq_one A hA
  rw [det_mat1] at h
  rw [det_mat1, trace_mat1]
  simp [Matrix.sub_apply, Matrix.one_apply]
  linarith


theorem rhoHat_re_pos (A : Mat 1) (hA : IsSymplectic A) (htr : 0 < A.trace) :
    0 < (rhoHat A).re := by
  have hne := complexLinearDet_ne_zero A hA
  have hn : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  unfold rhoHat
  rw [Complex.div_ofReal_re]
  apply div_pos _ hn
  rw [cld_mat1, trace_mat1] at *
  simp only
  linarith


theorem rhoHat_ne_one (A : Mat 1) (hA : IsSymplectic A) (htr : A.trace < 2) :
    rhoHat A ≠ 1 := by
  intro h1
  have hne := complexLinearDet_ne_zero A hA
  have hn : (‖complexLinearDet A‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
  have he : complexLinearDet A = (‖complexLinearDet A‖ : ℂ) := by
    unfold rhoHat at h1
    rw [div_eq_one_iff_eq hn] at h1
    exact h1
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  have hpos : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  rw [cld_mat1] at hre him hpos
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hdet := det_eq_one A hA
  rw [det_mat1] at hdet
  rw [trace_mat1] at htr
  have hc : A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) = A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  rw [hc] at hdet
  have hs : 0 < A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by linarith
  nlinarith [sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) - A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), sq_nonneg (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)), mul_pos hs (by linarith : (0:ℝ) < 2 - (A (Sum.inl 0 : Fin 1 ⊕ Fin 1) (Sum.inl 0 : Fin 1 ⊕ Fin 1) + A (Sum.inr 0 : Fin 1 ⊕ Fin 1) (Sum.inr 0 : Fin 1 ⊕ Fin 1)))]


def dotv (M : M2) (s : ℝ) : ℝ :=
  M 0 0 * Real.cos s ^ 2 + (M 0 1 + M 1 0) * Real.cos s * Real.sin s + M 1 1 * Real.sin s ^ 2


def crossv (M : M2) (s : ℝ) : ℝ :=
  M 1 0 * Real.cos s ^ 2 + (M 1 1 - M 0 0) * Real.cos s * Real.sin s - M 0 1 * Real.sin s ^ 2


theorem mulVec_rv (M : M2) (s : ℝ) :
    M *ᵥ rotationVector s = ![dotv M s * Real.cos s - crossv M s * Real.sin s,
      dotv M s * Real.sin s + crossv M s * Real.cos s] := by
  have h := Real.sin_sq_add_cos_sq s
  ext i; fin_cases i <;>
    simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two, dotv, crossv]
  · linear_combination (-(M 0 0 * Real.cos s) - M 0 1 * Real.sin s) * h
  · linear_combination (-(M 1 0 * Real.cos s) - M 1 1 * Real.sin s) * h


theorem dotProduct_eq (M : M2) (s : ℝ) :
    rotationVector s ⬝ᵥ (M *ᵥ rotationVector s) = dotv M s := by
  have h := Real.sin_sq_add_cos_sq s
  rw [mulVec_rv]
  simp [rotationVector, dotProduct, Fin.sum_univ_two]
  linear_combination dotv M s * h


theorem rot_mul_apply0 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 0 j = Real.cos a * M 0 j - Real.sin a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]; ring


theorem rot_mul_apply1 (a : ℝ) (M : M2) (j : Fin 2) :
    (rotationMatrix a * M) 1 j = Real.sin a * M 0 j + Real.cos a * M 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [rotationMatrix]


theorem rv_ne_zero (s : ℝ) : rotationVector s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [rotationVector] at h0 h1
  have := Real.sin_sq_add_cos_sq s
  rw [h0, h1] at this; norm_num at this


end

end CZBH

/-!
# T2 child C: `czIndexOfPath` is invariant under a change of frame by a loop of winding zero

`czIndexOfPath (G φ G(0)⁻¹) = czIndexOfPath φ` for a nondegenerate path `φ` in `Sp(1)` and a
loop `G` in `Sp(1)` along which `G(t) G(0)⁻¹ e₁` does not wind.
-/


namespace T2C

noncomputable section

abbrev E2 : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

lemma windingInterval_congr {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) : windingInterval φ = windingInterval φ' := by
  have key : ∀ s θ, IsAngleLift φ s θ ↔ IsAngleLift φ' s θ := by
    intro s θ
    unfold IsAngleLift
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun t ht => by rw [← h t ht]; exact h3 t ht⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun t ht => by rw [h t ht]; exact h3 t ht⟩
  unfold windingInterval; simp_rw [key]

lemma czIndexOfPath_congr {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) : czIndexOfPath φ = czIndexOfPath φ' := by
  unfold czIndexOfPath; rw [windingInterval_congr h]

lemma isSymplectic_of_det (A : ConleyZehnder.Mat 1) (h : A.det = 1) : IsSymplectic A := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff]
  rw [CZBH.det_mat1] at h
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.transpose_apply] <;> linarith

/-- An `ℝ`-indexed path, continuous on `[0, 1]`, as a path of `Mat 1` matrices. -/
def toPath (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hc : ContinuousOn φ (Icc 0 1)) :
    C(unitInterval, ConleyZehnder.Mat 1) :=
  ⟨fun t => reindex E2.symm E2.symm (φ t),
    (hc.comp_continuous continuous_subtype_val (fun t => t.2)).matrix_reindex _ _⟩

lemma toPath_apply (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hc : ContinuousOn φ (Icc 0 1))
    (t : unitInterval) : toPath φ hc t = reindex E2.symm E2.symm (φ t) := rfl

lemma reindex_toPath_projIcc (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hc : ContinuousOn φ (Icc 0 1))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    reindex E2 E2 (toPath φ hc (projIcc 0 1 zero_le_one τ)) = φ τ := by
  rw [toPath_apply, projIcc_of_mem _ hτ]
  ext i j; simp [Matrix.reindex_apply]

lemma det_reindex_symm (A : Matrix (Fin 2) (Fin 2) ℝ) : (reindex E2.symm E2.symm A).det = A.det :=
  det_reindex_self _ _

/-- The rotation-invariance computation: if `A ∈ Sp(1)` has first column `r e^{iθ}` with `r > 0`,
then `Re(ρ̂(A) e^{-iθ}) > 0`. -/
lemma rhoHat_mul_re_pos (A : ConleyZehnder.Mat 1) (hA : IsSymplectic A) (r θ : ℝ) (hr : 0 < r)
    (h0 : A (Sum.inl 0) (Sum.inl 0) = r * Real.cos θ)
    (h1 : A (Sum.inr 0) (Sum.inl 0) = r * Real.sin θ) :
    0 < (rhoHat A * Complex.exp (-(θ : ℂ) * Complex.I)).re := by
  have hne := complexLinearDet_ne_zero A hA
  have hn : 0 < ‖complexLinearDet A‖ := norm_pos_iff.2 hne
  have hdet := CZBH.det_eq_one A hA
  rw [CZBH.det_mat1] at hdet
  unfold rhoHat
  rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
  apply div_pos _ hn
  rw [CZBH.cld_mat1, show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  simp only [Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  rw [Real.cos_neg, Real.sin_neg]
  have hc2 := Real.sin_sq_add_cos_sq θ
  have key : r * ((A (Sum.inl 0) (Sum.inl 0) + A (Sum.inr 0) (Sum.inr 0)) / 2 * Real.cos θ -
      (A (Sum.inr 0) (Sum.inl 0) - A (Sum.inl 0) (Sum.inr 0)) / 2 * (-Real.sin θ)) =
      (r ^ 2 + 1) / 2 := by
    rw [← hdet]
    have e0 : r * Real.cos θ = A (Sum.inl 0) (Sum.inl 0) := h0.symm
    have e1 : r * Real.sin θ = A (Sum.inr 0) (Sum.inl 0) := h1.symm
    have hr2 : r ^ 2 = A (Sum.inl 0) (Sum.inl 0) ^ 2 + A (Sum.inr 0) (Sum.inl 0) ^ 2 := by
      rw [h0, h1]; linear_combination (-(r ^ 2)) * hc2
    linear_combination ((A (Sum.inl 0) (Sum.inl 0) + A (Sum.inr 0) (Sum.inr 0)) / 2) * e0 +
      ((A (Sum.inr 0) (Sum.inl 0) - A (Sum.inl 0) (Sum.inr 0)) / 2) * e1 - (1 / 2 : ℝ) * hr2
  have : 0 < r * ((A (Sum.inl 0) (Sum.inl 0) + A (Sum.inr 0) (Sum.inr 0)) / 2 * Real.cos θ -
      (A (Sum.inr 0) (Sum.inl 0) - A (Sum.inl 0) (Sum.inr 0)) / 2 * (-Real.sin θ)) := by
    rw [key]; positivity
  have := (pos_iff_pos_of_mul_pos this).1 hr
  simpa using (lt_of_lt_of_eq this (by ring))

end

end T2C

namespace T2C

noncomputable section

/-- A loop in `Sp(1)` whose first column does not wind has Maslov index `0`. -/
lemma maslovIndex_eq_zero (γ : C(unitInterval, ConleyZehnder.Mat 1)) (hγ : IsSymplecticLoop γ)
    (θ : unitInterval → ℝ) (hθc : Continuous θ) (hθ1 : θ 1 = θ 0) (r : unitInterval → ℝ)
    (hr : ∀ t, 0 < r t)
    (h0 : ∀ t, γ t (Sum.inl 0) (Sum.inl 0) = r t * Real.cos (θ t))
    (h1 : ∀ t, γ t (Sum.inr 0) (Sum.inl 0) = r t * Real.sin (θ t)) :
    maslovIndex γ = 0 := by
  obtain ⟨hρc, hρn⟩ := rhoHat_path_continuous γ hγ.1
  set z : unitInterval → ℂ := fun t => rhoHat (γ t) * Complex.exp (-(θ t : ℂ) * Complex.I)
    with hzdef
  have hz : ∀ t, 0 < (z t).re := fun t =>
    rhoHat_mul_re_pos (γ t) (hγ.1 t) (r t) (θ t) (hr t) (h0 t) (h1 t)
  have hzc : Continuous z := hρc.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp hθc).neg.mul continuous_const))
  have hzn : ∀ t, ‖z t‖ = 1 := fun t => by
    simp only [z, norm_mul, hρn t, one_mul]
    rw [show -(θ t : ℂ) * Complex.I = ((-θ t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  set Θ : unitInterval → ℝ := fun t => θ t + Complex.arg (z t) with hΘdef
  have hΘc : Continuous Θ := hθc.add (continuous_iff_continuousAt.2 fun t =>
    (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inl (hz t)))).comp hzc.continuousAt)
  have hlift : ∀ t, rhoHat (γ t) = Complex.exp ((Θ t : ℂ) * Complex.I) := fun t => by
    have e := Complex.norm_mul_exp_arg_mul_I (z t)
    rw [hzn t, Complex.ofReal_one, one_mul] at e
    have : Complex.exp ((Θ t : ℂ) * Complex.I) =
        Complex.exp ((θ t : ℂ) * Complex.I) * Complex.exp ((Complex.arg (z t) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; simp only [Θ]; push_cast; ring
    rw [this, e]
    simp only [z]
    rw [mul_left_comm, ← Complex.exp_add]
    simp
  have hval : IsMaslovValue γ 0 := by
    refine ⟨Θ, ⟨hΘc, hlift⟩, ?_⟩
    have hz10 : z 1 = z 0 := by simp only [z, hγ.2.1, hγ.2.2, hθ1]
    simp only [Θ, hz10, hθ1]; simp
  obtain ⟨k, -, hu⟩ := maslovValue_existsUnique γ hγ
  have hex : ∃ k, IsMaslovValue γ k := ⟨0, hval⟩
  unfold maslovIndex
  rw [dif_pos hex]
  exact (hu _ hex.choose_spec).trans (hu 0 hval).symm

lemma reindex_mul' {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m ℝ) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  simpa [Matrix.reindexAlgEquiv_apply] using
    (Matrix.reindexAlgEquiv_mul (R := ℝ) (A := ℝ) e A B)

lemma symp_mul {A B : ConleyZehnder.Mat 1} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := (symplecticGroup (Fin 1) ℝ).mul_mem hA hB

lemma det_inv_one {A : ConleyZehnder.Mat 1} (h : A.det = 1) : (A⁻¹).det = 1 := by
  rw [det_nonsing_inv, h]; simp

/-- Child C. -/
theorem czIndexOfPath_conj (φ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφc : ContinuousOn φ (Icc 0 1)) (hφ0 : φ 0 = 1)
    (hφd : ∀ t ∈ Icc (0 : ℝ) 1, (φ t).det = 1) (hφ1 : (1 - φ 1).det ≠ 0)
    (hGc : ContinuousOn G (Icc 0 1)) (hGd : ∀ t ∈ Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) :
    czIndexOfPath (fun t => G t * φ t * (G 0)⁻¹) = czIndexOfPath φ := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set ψ := toPath φ hφc with hψdef
  have hψ : ψ ∈ SP 1 := by
    refine ⟨fun t => isSymplectic_of_det _ (by rw [toPath_apply, det_reindex_symm]; exact hφd t t.2),
      ?_, ?_⟩
    · rw [toPath_apply]; simp [hφ0, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
    · rw [toPath_apply]
      have : (1 : ConleyZehnder.Mat 1) - reindex E2.symm E2.symm (φ ((1 : unitInterval) : ℝ)) =
          reindex E2.symm E2.symm (1 - φ 1) := by
        ext i j; simp [Matrix.reindex_apply, Matrix.one_apply, Matrix.sub_apply]
      rw [this, det_reindex_symm]; exact hφ1
  set g := toPath G hGc with hgdef
  set g0 := g 0 with hg0def
  have hg0 : g0 = reindex E2.symm E2.symm (G 0) := by
    simp only [g0, g, toPath_apply, Set.Icc.coe_zero]
  have hgd : ∀ t, (g t).det = 1 := fun t => by rw [toPath_apply, det_reindex_symm]; exact hGd t t.2
  have hgS : ∀ t, IsSymplectic (g t) := fun t => isSymplectic_of_det _ (hgd t)
  have hg0d : g0.det = 1 := hgd 0
  have hinvS : IsSymplectic g0⁻¹ := isSymplectic_of_det _ (det_inv_one hg0d)
  have hu : IsUnit g0.det := by rw [hg0d]; exact isUnit_one
  have hmi : g0 * g0⁻¹ = 1 := mul_nonsing_inv _ hu
  have him : g0⁻¹ * g0 = 1 := nonsing_inv_mul _ hu
  let γ : C(unitInterval, ConleyZehnder.Mat 1) := g * ContinuousMap.const _ g0⁻¹
  let ψ0 : C(unitInterval, ConleyZehnder.Mat 1) :=
    ContinuousMap.const _ g0 * ψ * ContinuousMap.const _ g0⁻¹
  have hγt : ∀ t, γ t = g t * g0⁻¹ := fun t => rfl
  have hψ0t : ∀ t, ψ0 t = g0 * ψ t * g0⁻¹ := fun t => rfl
  have hg1 : g 1 = g0 := by
    simp only [g0, g, toPath_apply, Set.Icc.coe_one, Set.Icc.coe_zero, hG1]
  have hγ : IsSymplecticLoop γ :=
    ⟨fun t => symp_mul (hgS t) hinvS, by rw [hγt]; exact hmi, by rw [hγt, hg1]; exact hmi⟩
  have hψ0 : ψ0 ∈ SP 1 := by
    refine ⟨fun t => symp_mul (symp_mul (hgS 0) (hψ.1 t)) hinvS, ?_, ?_⟩
    · rw [hψ0t, hψ.2.1, mul_one, hmi]
    · rw [hψ0t]
      have : (1 : ConleyZehnder.Mat 1) - g0 * ψ 1 * g0⁻¹ = g0 * (1 - ψ 1) * g0⁻¹ := by
        rw [mul_sub, sub_mul, mul_one, hmi]
      rw [this, det_mul, det_mul, hg0d, det_inv_one hg0d, one_mul, mul_one]
      exact hψ.2.2
  have hprod : γ * ψ0 ∈ SP 1 := by
    refine ⟨fun t => symp_mul (hγ.1 t) (hψ0.1 t), ?_, ?_⟩
    · show γ 0 * ψ0 0 = 1; rw [hγ.2.1, hψ0.2.1, one_mul]
    · show (1 - γ 1 * ψ0 1).det ≠ 0; rw [hγ.2.2, one_mul]; exact hψ0.2.2
  -- step 1: the conjugated path is `γ ψ0` on `[0, 1]`
  have eq1 : czIndexOfPath (fun t => G t * φ t * (G 0)⁻¹) = czIndex (γ * ψ0) := by
    rw [FiniteEnergyPlane.czIndex_eq_czIndexOfPath _ hprod]
    apply czIndexOfPath_congr
    intro τ hτ
    show G τ * φ τ * (G 0)⁻¹ =
      reindex E2 E2 (γ (projIcc 0 1 zero_le_one τ) * ψ0 (projIcc 0 1 zero_le_one τ))
    rw [hγt, hψ0t]
    have : g (projIcc 0 1 zero_le_one τ) * g0⁻¹ *
        (g0 * ψ (projIcc 0 1 zero_le_one τ) * g0⁻¹) =
        g (projIcc 0 1 zero_le_one τ) * ψ (projIcc 0 1 zero_le_one τ) * g0⁻¹ := by
      rw [mul_assoc, ← mul_assoc g0⁻¹, ← mul_assoc g0⁻¹, him, one_mul, ← mul_assoc]
    rw [this, reindex_mul', reindex_mul', reindex_toPath_projIcc G hGc hτ,
      reindex_toPath_projIcc φ hφc hτ, hg0, ← inv_reindex]
    simp [Matrix.reindex_apply]
  -- step 2: loop property with a loop of Maslov index `0`
  have hm : maslovIndex γ = 0 := by
    have hθ' : ∀ t : unitInterval, ∃ r : ℝ, 0 < r ∧
        γ t (Sum.inl 0) (Sum.inl 0) = r * Real.cos (θ t) ∧
        γ t (Sum.inr 0) (Sum.inl 0) = r * Real.sin (θ t) := by
      intro t
      obtain ⟨r, hr, hv⟩ := hθ t t.2
      have hγe : γ t = reindex E2.symm E2.symm (G t * (G 0)⁻¹) := by
        rw [hγt, toPath_apply, hg0, inv_reindex, ← reindex_mul']
      refine ⟨r, hr, ?_, ?_⟩
      · have := congrFun hv 0
        simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
        rw [hγe]; exact this
      · have := congrFun hv 1
        simp [rotationVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
        rw [hγe]; exact this
    choose r hr hr0 hr1 using hθ'
    exact maslovIndex_eq_zero γ hγ (fun t => θ t)
      (hθc.comp_continuous continuous_subtype_val (fun t => t.2))
      (by simp [hθ1]) r hr hr0 hr1
  have eq2 : czIndex (γ * ψ0) = czIndex ψ0 := by
    rw [czIndex_loop 1 γ hγ ψ0 hψ0, hm]; ring
  -- step 3: naturality under the constant conjugation by `g0`
  have eq3 : czIndex ψ0 = czIndex ψ :=
    czIndex_naturality (ContinuousMap.const _ g0) (fun _ => hgS 0) ψ hψ ψ0 (fun t => rfl)
  have eq4 : czIndex ψ = czIndexOfPath φ := by
    rw [FiniteEnergyPlane.czIndex_eq_czIndexOfPath ψ hψ]
    apply czIndexOfPath_congr
    intro τ hτ
    exact reindex_toPath_projIcc φ hφc hτ
  rw [eq1, eq2, eq3, eq4]

end

end T2C

open HryniewiczCriterion

theorem solution (φ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφc : ContinuousOn φ (Set.Icc 0 1)) (hφ0 : φ 0 = 1)
    (hφd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ1 : (1 - φ 1).det ≠ 0)
    (hGc : ContinuousOn G (Set.Icc 0 1)) (hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) :
    czIndexOfPath (fun t => G t * φ t * (G 0)⁻¹) = czIndexOfPath φ :=
  T2C.czIndexOfPath_conj φ G hφc hφ0 hφd hφ1 hGc hGd hG1 θ hθc hθ1 hθ
