-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/89c4e50c-bb53-56bc-b8c5-dcb023b867c2

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

/-!
                                                                  -/

namespace Ws23HLD1

noncomputable def kappa1 : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (by rw [Matrix.det_fin_two_of]; norm_num)

theorem kappa1_mem : kappa1 ∈ rowIsometrySubgroup₀ ℝ := weyl_mem_rowIsometrySubgroup₀ ℝ

theorem coe_kappa1 : (kappa1 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] := rfl

theorem archWeightCharℝ_kappa1 (k : ℤ) :
    (archWeightCharℝ k ⟨kappa1, kappa1_mem⟩ : ℂ) = Complex.I ^ k := by
  show (((archWeightOneℝ ⟨kappa1, kappa1_mem⟩) ^ k : ℂˣ) : ℂ) = Complex.I ^ k
  rw [Units.val_zpow_eq_zpow_val]
  exact congrArg (fun w : ℂ => w ^ k) archWeightOneℝ_weyl

end Ws23HLD1

open Ws23HLD1 in
set_option linter.unusedVariables false in
theorem solution
    (a : ℚ)
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (par : ZMod 2) (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    WA par (w₀R * RSCarrier.transposeInv (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne')) =
      Complex.I ^ (kw par default) *
        ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
          ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
        Wr par default (-a₁ / a₂) := by

  have ha₁' : (-a₁⁻¹ : ℝ) ≠ 0 := neg_ne_zero.2 (inv_ne_zero ha₁)
  have ht' : (-a₁ / a₂ : ℝ) ≠ 0 := div_ne_zero (neg_ne_zero.2 ha₁) ha₂.ne'
  set z : ℝˣ := Units.mk0 (-a₁⁻¹) ha₁' with hz
  set t : ℝˣ := Units.mk0 (-a₁ / a₂) ht' with ht

  have hqinv : (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne')⁻¹ =
      AutomorphicForm.SiegelCoordinates.upperUnit a₁⁻¹ 0 a₂⁻¹ (inv_ne_zero ha₁) (inv_ne_zero ha₂.ne') := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.SiegelCoordinates.upperUnit, ha₁, ha₂.ne']

  have hmat : w₀R * RSCarrier.transposeInv (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne') =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagOne t * kappa1 := by
    have hti : (RSCarrier.transposeInv (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne') :
        Matrix (Fin 2) (Fin 2) ℝ) =
        (((AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne')⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).transpose := rfl
    refine Units.ext ?_
    rw [Units.val_mul, hw₀R, Units.val_mul, Units.val_mul, coe_kappa1, hti, hqinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, AutomorphicForm.SiegelCoordinates.upperUnit, diagOne, hz, ht,
        Matrix.GeneralLinearGroup.scalar, Matrix.transpose_apply, Matrix.diagonal] <;>
      field_simp
  rw [hmat, hWAK par kappa1 kappa1_mem, hWAZ par z, hWAt par t, archWeightCharℝ_kappa1]
  simp only [hz, ht, Units.val_mk0]
  push_cast
  ring

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile (solution)
