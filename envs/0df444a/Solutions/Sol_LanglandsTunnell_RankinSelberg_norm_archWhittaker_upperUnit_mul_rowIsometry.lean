-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.norm_archWhittaker_upperUnit_mul_rowIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/234637ce-bbc5-5af4-b60b-2109cbc4f3eb

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23K3

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

noncomputable abbrev eps : GL (Fin 2) ℝ := upperUnit (1 : ℝ) 0 (-1) one_ne_zero (by norm_num)

theorem eps_coe : ((eps : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, -1] := rfl

theorem eps_mem : (eps : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup ℝ := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [eps_coe, Matrix.det_fin_two_of]; simp
  · simp [eps_coe]

theorem det_eps : ((eps : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  rw [eps_coe, Matrix.det_fin_two_of]; ring

theorem det_cases {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∨ (k : Matrix (Fin 2) (Fin 2) ℝ).det = -1 := by
  have h : |(k : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 := by
    have := hk.1; rwa [Real.norm_eq_abs] at this
  exact abs_eq (by norm_num) |>.mp h

theorem mem₀_of_det_one {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ)
    (hd : (k : Matrix (Fin 2) (Fin 2) ℝ).det = 1) : k ∈ rowIsometrySubgroup₀ ℝ :=
  (mem_rowIsometrySubgroup₀_iff ℝ).2 ⟨hd, hk⟩

theorem norm_archWeightCharℝ (n : ℤ) (κ : rowIsometrySubgroup₀ ℝ) :
    ‖((archWeightCharℝ n κ : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : ‖((archWeightOneℝ κ : ℂˣ) : ℂ)‖ = 1 := by
    have hsq : Complex.normSq ((archWeightOneℝ κ : ℂˣ) : ℂ) = 1 := normSq_firstRowℂ_of_mem κ.2
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg ((archWeightOneℝ κ : ℂˣ) : ℂ)]
  have h2 : (archWeightCharℝ n κ : ℂˣ) = (archWeightOneℝ κ) ^ n := rfl
  rw [h2, Units.val_zpow_eq_zpow_val, norm_zpow, h1, one_zpow]

theorem upperUnit_eq_scalar_mul_diagOne (t₁ t₂ : ℝ) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    upperUnit t₁ 0 t₂ h₁ h₂ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t₂ h₂) * diagOne (Units.mk0 (t₁ / t₂) (div_ne_zero h₁ h₂)) := by
  refine Units.ext ?_
  change (!![t₁, 0; 0, t₂] : Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.scalar, diagOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.scalar_apply] <;> field_simp

theorem upperUnit_eq_mul_eps (t₁ t₂ : ℝ) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    upperUnit t₁ 0 t₂ h₁ h₂ = upperUnit t₁ 0 (-t₂) h₁ (neg_ne_zero.2 h₂) * eps := by
  refine Units.ext ?_
  change (!![t₁, 0; 0, t₂] : Matrix (Fin 2) (Fin 2) ℝ) = (!![t₁, 0; 0, -t₂] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, -1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_centre_factor (c : ℂ) (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    ‖((((|t| : ℝ) : ℝ) : ℂ) ^ (c + 1)) * ((((t : ℝ) : ℂ) / (((|t| : ℝ) : ℝ) : ℂ)) ^ (n : ℤ))‖ = |t| ^ (c.re + 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 ht), norm_zpow, norm_div, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs, div_self (abs_ne_zero.2 ht), one_zpow, mul_one,
    Complex.add_re, Complex.one_re]

end Ws23K3

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in

theorem solution
    (P : RealArchParam)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (par : ZMod 2) (t₁ t₂ : ℝ) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)
    (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup ℝ) :
    ‖WA par (upperUnit t₁ 0 t₂ h₁ h₂ * k)‖ =
      |t₂| ^ (P.centralExponent.re + 1) *
        ‖Wr par default ((Matrix.GeneralLinearGroup.det k : ℝ) * t₁ / t₂)‖ := by

  have core : ∀ (s₁ s₂ : ℝ) (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ),
      ‖WA par (upperUnit s₁ 0 s₂ hs₁ hs₂ * κ)‖ = |s₂| ^ (P.centralExponent.re + 1) * ‖Wr par default (s₁ / s₂)‖ := by
    intro s₁ s₂ hs₁ hs₂ κ hκ
    rw [hWAK par κ hκ, norm_mul, Ws23K3.norm_archWeightCharℝ, one_mul,
      Ws23K3.upperUnit_eq_scalar_mul_diagOne s₁ s₂ hs₁ hs₂, hWAZ, hWAt, norm_mul]
    simp only [Units.val_mk0]
    rw [Ws23K3.norm_centre_factor _ _ _ hs₂]
    push_cast
    rfl
  rcases Ws23K3.det_cases hk with hd | hd
  ·
    rw [core t₁ t₂ h₁ h₂ k (Ws23K3.mem₀_of_det_one hk hd), Matrix.GeneralLinearGroup.val_det_apply, hd]
    simp
  ·
    have hk' : Ws23K3.eps * k ∈ rowIsometrySubgroup₀ ℝ := by
      refine Ws23K3.mem₀_of_det_one (Subgroup.mul_mem _ Ws23K3.eps_mem hk) ?_
      rw [Units.val_mul, Matrix.det_mul, Ws23K3.det_eps, hd]; norm_num
    have hmul : upperUnit t₁ 0 t₂ h₁ h₂ * k = upperUnit t₁ 0 (-t₂) h₁ (neg_ne_zero.2 h₂) * (Ws23K3.eps * k) := by
      rw [← mul_assoc, ← Ws23K3.upperUnit_eq_mul_eps]
    rw [hmul, core t₁ (-t₂) h₁ (neg_ne_zero.2 h₂) _ hk', abs_neg, Matrix.GeneralLinearGroup.val_det_apply, hd]
    congr 2
    push_cast
    field_simp

end S_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry (solution)
