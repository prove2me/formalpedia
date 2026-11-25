-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:41.892024+00:00
-- url     : https://prove2.me/submissions/c3893cfe-b788-4c95-af41-6ae127588993

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (ε : ℂ) (hε : star ε = ε) (a b : Fin n → ℂ)
    (ha : H *ᵥ a = ε • a) (hb : H *ᵥ b = ε • b) (hab : star a ⬝ᵥ a = star b ⬝ᵥ b) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ H * U = U * H ∧ U *ᵥ a = b ∧
      ∀ w, star a ⬝ᵥ w = 0 → star b ⬝ᵥ w = 0 → U *ᵥ w = w := by
  classical
  set v : Fin n → ℂ := a - b with hv
  set s : ℂ := star v ⬝ᵥ a with hs
  have hsa : star (star a ⬝ᵥ a) = star a ⬝ᵥ a := (Matrix.star_dotProduct (v := a) (w := a)).symm
  have hba : star (star b ⬝ᵥ a) = star a ⬝ᵥ b := (Matrix.star_dotProduct (v := a) (w := b)).symm
  have hvv : star v ⬝ᵥ v = s + star s := by
    simp only [hv, hs, star_sub, sub_dotProduct, dotProduct_sub, hsa, hba]
    linear_combination (-1 : ℂ) * hab
  by_cases hs0 : s = 0
  · have hv0 : v = 0 := by
      have h0 : star v ⬝ᵥ v = 0 := by rw [hvv, hs0, star_zero, add_zero]
      exact dotProduct_star_self_eq_zero.mp h0
    have hab' : a = b := sub_eq_zero.mp (by rw [← hv]; exact hv0)
    refine ⟨1, by simp, by simp, by rw [Matrix.one_mulVec, hab'], fun w _ _ => Matrix.one_mulVec w⟩
  · set A : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec v (star v) with hA
    have hA1 : ∀ w, A *ᵥ w = (star v ⬝ᵥ w) • v := by
      intro w
      rw [hA, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    have hA2 : Aᴴ = A := by rw [hA, Matrix.conjTranspose_vecMulVec, star_star]
    have hA3 : A * A = (star v ⬝ᵥ v) • A := by
      rw [hA, Matrix.vecMulVec_mul_vecMulVec]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hHv : H *ᵥ v = ε • v := by rw [hv, Matrix.mulVec_sub, ha, hb, smul_sub]
    have hvH : star v ᵥ* H = ε • star v := by
      have h1 := Matrix.star_mulVec H v
      rw [hH, hHv, star_smul, hε] at h1
      exact h1.symm
    have hHA : H * A = A * H := by
      rw [hA, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hHv, hvH]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨1 - s⁻¹ • A, ?_, ?_, ?_, ?_⟩
    · have hss : star s ≠ 0 := by rwa [star_ne_zero]
      have hcoef : -s⁻¹ - star s⁻¹ + star s⁻¹ * s⁻¹ * (s + star s) = 0 := by
        rw [star_inv₀]
        field_simp
        ring
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hA2]
      calc (1 - star s⁻¹ • A) * (1 - s⁻¹ • A)
          = 1 + (-s⁻¹ - star s⁻¹ + star s⁻¹ * s⁻¹ * (star v ⬝ᵥ v)) • A := by
            simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hA3, smul_smul]
            module
        _ = 1 := by rw [hvv, hcoef, zero_smul, add_zero]
    · rw [mul_sub, sub_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, hHA]
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hA1, ← hs, smul_smul, inv_mul_cancel₀ hs0,
        one_smul, hv, sub_sub_cancel]
    · intro w hw1 hw2
      have hvw : star v ⬝ᵥ w = 0 := by rw [hv, star_sub, sub_dotProduct, hw1, hw2, sub_zero]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hA1, hvw, zero_smul, smul_zero, sub_zero]
end GlobalTheory.CompanionTheory.BesselCartan
