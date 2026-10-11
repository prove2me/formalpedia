-- Prove2me | solution 1 for KochHF.energy_variation_first_order
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T16:40:40.166102+00:00
-- url     : https://prove2.me/submissions/595a1a4a-61aa-4286-a2c2-ee7b23eaacc9

import Mathlib
import Definitions.Def_KochHF_FockSpace


open Matrix KochHF

namespace KochHFAux

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {K : ℕ}

lemma matEl_add (ψ φ : FockVec K) (A B : FockOp K) :
    matEl ψ (A + B) φ = matEl ψ A φ + matEl ψ B φ := by
  simp [matEl, add_mulVec, dotProduct_add]

lemma matEl_sub (ψ φ : FockVec K) (A B : FockOp K) :
    matEl ψ (A - B) φ = matEl ψ A φ - matEl ψ B φ := by
  simp [matEl, sub_mulVec, dotProduct_sub]

lemma matEl_smul (ψ φ : FockVec K) (c : ℂ) (A : FockOp K) :
    matEl ψ (c • A) φ = c * matEl ψ A φ := by
  simp [matEl, smul_mulVec, dotProduct_smul]

/-- The matrix element as a real-linear map. -/
noncomputable def matElLin (ψ φ : FockVec K) : FockOp K →ₗ[ℝ] ℂ where
  toFun A := matEl ψ A φ
  map_add' A B := matEl_add ψ φ A B
  map_smul' c A := by
    simp only [RingHom.id_apply]
    rw [← Complex.coe_smul, matEl_smul]; rfl

lemma real_smul_eq (A : FockOp K) (t : ℝ) :
    (Complex.I * t) • A = t • (Complex.I • A) := by
  rw [mul_comm, ← smul_smul, Complex.coe_smul]

lemma neg_real_smul_eq (A : FockOp K) (t : ℝ) :
    (-(Complex.I * t)) • A = t • (-(Complex.I • A)) := by
  rw [neg_smul, real_smul_eq, smul_neg]

lemma hasDerivAt_conj_exp (A H : FockOp K) (t : ℝ) :
    HasDerivAt
      (fun t : ℝ => NormedSpace.exp ((Complex.I * t) • A) * H *
        NormedSpace.exp ((-(Complex.I * t)) • A))
      (NormedSpace.exp ((Complex.I * t) • A) * (Complex.I • A) * H *
          NormedSpace.exp ((-(Complex.I * t)) • A) +
        NormedSpace.exp ((Complex.I * t) • A) * H *
          (NormedSpace.exp ((-(Complex.I * t)) • A) * (-(Complex.I • A)))) t := by
  simp only [real_smul_eq, neg_real_smul_eq]
  have hU := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • A) t
  have hV := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-(Complex.I • A)) t
  exact HasDerivAt.fun_mul (HasDerivAt.mul_const hU H) hV

theorem main_energy_variation_first_order {K N : ℕ} (H : FockOp K) (α : Fin N → Fin K → ℂ)
    (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian) :
    HasDerivAt
      (fun t : ℝ => matEl (slater α)
        (NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * H *
          NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M)) (slater α))
      (Complex.I * matEl (slater α) (oneBodyOp M * H - H * oneBodyOp M) (slater α)) 0 := by
  have h := hasDerivAt_conj_exp (oneBodyOp M) H 0
  let L := LinearMap.toContinuousLinearMap (matElLin (slater α) (slater α))
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  refine h2.congr_deriv ?_
  show matEl (slater α) _ (slater α) = _
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul,
    mul_one]
  rw [← matEl_smul]
  congr 1
  simp only [smul_sub, mul_neg, smul_mul_assoc, mul_smul_comm]
  abel

end KochHFAux

open Matrix KochHF

theorem solution {K N : ℕ} (H : FockOp K) (α : Fin N → Fin K → ℂ)
    (M : Matrix (Fin K) (Fin K) ℂ) (hM : M.IsHermitian) :
    HasDerivAt
      (fun t : ℝ => matEl (slater α)
        (NormedSpace.exp ((Complex.I * t) • oneBodyOp M) * H *
          NormedSpace.exp ((-(Complex.I * t)) • oneBodyOp M)) (slater α))
      (Complex.I * matEl (slater α) (oneBodyOp M * H - H * oneBodyOp M) (slater α)) 0 := by
  exact KochHFAux.main_energy_variation_first_order H α M hM
