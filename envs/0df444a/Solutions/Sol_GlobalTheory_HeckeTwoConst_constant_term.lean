-- Prove2me | solution 1 for GlobalTheory.HeckeTwoConst.constant_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:51.295681+00:00
-- url     : https://prove2.me/submissions/d9ac7508-c6a1-4c0c-ab39-cef28f796d13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne
import Theorems.Thm_GlobalTheory_HeckeTwoConst_aPart_zero
import Theorems.Thm_GlobalTheory_HeckeTwoConst_gammaR_two
import Theorems.Thm_GlobalTheory_HeckeTwoConst_gammaR_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoConst
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (C : ClassGroup (NumberField.RingOfIntegers F)) (D : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) (Za Za' : ℂ → ℂ), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) → C * (ClassGroup.mk F 𝔞)⁻¹ = ClassGroup.mk0 D → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Za → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Za' → (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Za s = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Za' (1 - s)) → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * GlobalTheory.HeckeTwo.aPart 𝔞 0 / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Za' (1 - ((2 : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 C D Za Za' hD hC hZ _ hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfe2 := hfe 2 (fun n h => by
      have h' : (2 : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - 2 : ℤ) = -2 * n := by exact_mod_cast h
      omega)
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by
    rw [nrm]
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 𝔞.ne_zero)
  set r : ℝ := dF F ^ ((1 : ℝ) / 2) with hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hd _).ne'
  have hrr : (dF F : ℂ) = (r : ℂ) ^ 2 := by
    have : dF F = r ^ 2 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]; norm_num
    exact_mod_cast this
  have hc : cK F 2 = r := by
    rw [cK, hr]; norm_num
  have hneg : (dF F : ℂ) ^ ((-1 : ℂ) / 2) = (r : ℂ)⁻¹ := by
    rw [hr, ofReal_cpow hd.le, ← cpow_neg]
    congr 1
    push_cast; ring
  rw [show (1 : ℂ) - 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, cpow_one, hneg, gammaR_two,
    gammaR_neg_one] at hfe2
  rw [show (1 : ℂ) - ((2 : ℕ) : ℂ) = -1 by norm_num, aPart_zero 𝔞 C D Za hD hC hZ, hc, omegaFactor, ← hr]
  have hI : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 = 2⁻¹ * (Real.pi : ℂ)⁻¹ * (-2 * (Real.pi : ℂ))⁻¹ := by
    rw [inv_pow, mul_pow, I_sq]; field_simp
  have hg : (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)
  rw [hI, mul_pow, mul_pow, inv_pow (-2 * (Real.pi : ℂ)), hrr]
  rw [hrr] at hfe2
  generalize (-2 * (Real.pi : ℂ)) ^ Module.finrank ℚ F = g at hg hfe2
  generalize ((Real.pi : ℂ)⁻¹) ^ Module.finrank ℚ F = p at hfe2
  generalize ((2 : ℂ)⁻¹) ^ Module.finrank ℚ F = t
  push_cast
  field_simp at hfe2 ⊢
  linear_combination t * hfe2
end GlobalTheory.HeckeTwoConst
