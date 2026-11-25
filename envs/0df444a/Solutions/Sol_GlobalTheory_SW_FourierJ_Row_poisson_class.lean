-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.Row.poisson_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:17.892366+00:00
-- url     : https://prove2.me/submissions/b8a0611d-8942-484f-b4bb-6ba2a1b03542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCoset
import Theorems.Thm_GlobalTheory_IsSiegel_natCast_smul
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_eq_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_sq_mul_det
import Theorems.Thm_GlobalTheory_SW_FourierJ_norm_ech


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ GlobalTheory.SW.FourierJ.Row
variable {ι : Type} [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.SW.FourierJ.Row
namespace _root_.GlobalTheory.SW.FourierJ.Row
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : ℕ), 0 < R → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, -τ⁻¹ ∈ _root_.GlobalTheory.SW.Siegel ι →
    IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧
    ∀ (a : ι → ℚ) (ζ : ι → ℂ),
    (Summable fun m : ι → ℤ => ‖_root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    (Summable fun m : ι → ℤ =>
      ‖_root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) *
      ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
    c * ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
      _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) := by
  intro ι _ _ R hR τ hτ hτ' hdet
  have hτS : _root_.GlobalTheory.IsSiegel τ := hτ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef
  have hΩ : _root_.GlobalTheory.IsSiegel Ω := hτS.natCast_smul (pow_pos hR 2)
  have hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]
  have T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ) := by
      funext i
      simp only [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp
      ring
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, _root_.GlobalTheory.SW.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero,
      add_zero]
    generalize (fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x
    congr 1
    simp only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    push_cast
    ring
  have T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ) := by
      funext i
      simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv]
    have hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ := by
      rw [← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]
    have hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) : ℚ)) : ℂ) =
        (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, _root_.GlobalTheory.SW.FourierJ.zv, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) =
        Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ) := rfl
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]
    rw [_root_.GlobalTheory.SW.FourierJ.gs, _root_.GlobalTheory.SW.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]
    generalize (fun i => ((m i : ℤ) : ℂ)) = x
    congr 1
    simp only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]
    first | (field_simp; ring) | field_simp | ring
  refine ⟨_root_.GlobalTheory.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩
  · have h := hΩ.siegelGaussIntegral_sq_mul_det
    rw [hΩdef, smul_smul, Matrix.det_smul] at h
    rw [show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]
    exact h
  have hS1 := hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)
  have hS2 := hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R)
    (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))
  refine ⟨?_, ?_, ?_⟩
  · exact hS1.congr fun m => by rw [T1]
  · refine hS2.congr fun m => ?_
    rw [← T2, norm_mul, _root_.GlobalTheory.SW.FourierJ.norm_ech, one_mul]
  · have e1 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T1 a ζ m
    have e2 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T2 a ζ m
    have hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ := by
      rw [hΩinv]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      first | (field_simp; ring) | field_simp
    rw [e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]
    have hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    linear_combination (_root_.GlobalTheory.siegelGaussIntegral Ω *
      _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp
end _root_.GlobalTheory.SW.FourierJ.Row
end GlobalTheory.SW.FourierJ.Row
