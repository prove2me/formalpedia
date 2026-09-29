-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/fac4f4c0-ab54-52c4-9a98-ec286c9d3639

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
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace UNFOLDC

theorem integral3_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ]
    (H : α × β × γ → ℂ) (hH : Integrable H (μ.prod (ν.prod ρ))) :
    ∫ y, ∫ t, ∫ e, H (y, t, e) ∂ρ ∂ν ∂μ = ∫ e, ∫ t, ∫ y, H (y, t, e) ∂μ ∂ν ∂ρ := by
  have h1 : ∫ y, ∫ t, ∫ e, H (y, t, e) ∂ρ ∂ν ∂μ = ∫ y, ∫ te, H (y, te) ∂(ν.prod ρ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hH.prod_right_ae] with y hy
    exact (integral_prod (fun te => H (y, te)) hy).symm
  rw [h1, ← integral_prod H hH]

  let ψ₁ : α × β × γ ≃ᵐ (β × γ) × α := MeasurableEquiv.prodComm
  let ψ₂ : (β × γ) × α ≃ᵐ β × γ × α := MeasurableEquiv.prodAssoc
  let ψ₃ : β × γ × α ≃ᵐ (γ × α) × β := MeasurableEquiv.prodComm
  let ψ₄ : (γ × α) × β ≃ᵐ γ × α × β := MeasurableEquiv.prodAssoc
  let ψ₅ : γ × α × β ≃ᵐ γ × β × α := MeasurableEquiv.prodCongr (MeasurableEquiv.refl γ) MeasurableEquiv.prodComm
  let ψ : α × β × γ ≃ᵐ γ × β × α := (((ψ₁.trans ψ₂).trans ψ₃).trans ψ₄).trans ψ₅
  have hψ : MeasurePreserving ψ (μ.prod (ν.prod ρ)) (ρ.prod (ν.prod μ)) := by
    have h₁ : MeasurePreserving ψ₁ (μ.prod (ν.prod ρ)) ((ν.prod ρ).prod μ) := Measure.measurePreserving_swap
    have h₂ : MeasurePreserving ψ₂ ((ν.prod ρ).prod μ) (ν.prod (ρ.prod μ)) := measurePreserving_prodAssoc ν ρ μ
    have h₃ : MeasurePreserving ψ₃ (ν.prod (ρ.prod μ)) ((ρ.prod μ).prod ν) := Measure.measurePreserving_swap
    have h₄ : MeasurePreserving ψ₄ ((ρ.prod μ).prod ν) (ρ.prod (μ.prod ν)) := measurePreserving_prodAssoc ρ μ ν
    have h₅ : MeasurePreserving ψ₅ (ρ.prod (μ.prod ν)) (ρ.prod (ν.prod μ)) :=
      (MeasurePreserving.id ρ).prod Measure.measurePreserving_swap
    exact (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  have hψs : ∀ e t y, ψ.symm (e, t, y) = (y, t, e) := fun _ _ _ => rfl
  have h2 : ∫ x, H x ∂(μ.prod (ν.prod ρ)) = ∫ z, (H ∘ ψ.symm) z ∂(ρ.prod (ν.prod μ)) := by
    rw [← hψ.integral_comp' (H ∘ ψ.symm)]
    simp only [Function.comp, MeasurableEquiv.symm_apply_apply]
  have hH' : Integrable (H ∘ ψ.symm) (ρ.prod (ν.prod μ)) := by
    have hψ' : MeasurePreserving ψ.symm (ρ.prod (ν.prod μ)) (μ.prod (ν.prod ρ)) := hψ.symm ψ
    exact hψ'.integrable_comp_emb ψ.symm.measurableEmbedding |>.mpr hH
  rw [h2, integral_prod _ hH']
  refine integral_congr_ae ?_
  filter_upwards [hH'.prod_right_ae] with e he
  rw [integral_prod _ he]
  simp only [Function.comp, hψs]

open AutomorphicForm.StandardKernel LanglandsTunnell.Converse in

theorem upperUnit_eq_scalar_mul_diagOne (y t : ℝ) (hy : y ≠ 0) (ht : t ≠ 0) :
    AutomorphicForm.SiegelCoordinates.upperUnit (y * t) 0 y (mul_ne_zero hy ht) hy =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 y hy) * diagOne (Units.mk0 t ht) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.SiegelCoordinates.upperUnit, Matrix.GeneralLinearGroup.scalar, diagOne,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_comm]

theorem det_upperUnit (y t : ℝ) (hy : y ≠ 0) (ht : t ≠ 0) :
    ((Matrix.GeneralLinearGroup.det
        (AutomorphicForm.SiegelCoordinates.upperUnit (y * t) 0 y (mul_ne_zero hy ht) hy) : ℝˣ) : ℝ) = y * t * y := by
  simp [AutomorphicForm.SiegelCoordinates.upperUnit, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

theorem diagOne_mul_diag (a y t : ℝ) :
    LanglandsTunnell.Converse.ArchR.diagOne a * (!![y * t, 0; 0, y] : Matrix (Fin 2) (Fin 2) ℝ) =
      y • LanglandsTunnell.Converse.ArchR.diagOne (a * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.Converse.ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem ypow (P P₂ : RealArchParam) (s : ℂ) (y t : ℝ) (hy : 0 < y) (ht : t ≠ 0) :
    ((|y| : ℝ) : ℂ) *
        ((((|y| : ℝ) : ℂ) ^ (P.centralExponent + 1)) * ((((y : ℝ) : ℂ) / ((|y| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ))) *
        (((|y * t * y| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((y * t) ^ 2)⁻¹ : ℝ) : ℂ) *
        (LanglandsTunnell.Converse.ArchR.centralChar P₂ y * ((|y| : ℝ) : ℂ)) =
      (((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s)) *
        (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hy0 : y ≠ 0 := hy.ne'
  have hyC : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy0
  have habs : |y| = y := abs_of_pos hy
  have hcc : LanglandsTunnell.Converse.ArchR.centralChar P₂ y = ((y : ℝ) : ℂ) ^ P₂.centralExponent := by
    unfold LanglandsTunnell.Converse.ArchR.centralChar LanglandsTunnell.Converse.ArchR.quasiChar
    rw [habs, sign_pos hy]
    split_ifs <;> simp
  have h3 : ((|y * t * y| : ℝ) : ℂ) ^ (s - 1 / 2) =
      ((y : ℝ) : ℂ) ^ (s - 1 / 2) * ((y : ℝ) : ℂ) ^ (s - 1 / 2) * ((|t| : ℝ) : ℂ) ^ (s - 1 / 2) := by
    rw [show |y * t * y| = y * y * |t| by rw [abs_mul, abs_mul, habs]; ring]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (mul_nonneg hy.le hy.le) (abs_nonneg t),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le hy.le]
  rw [habs, div_self hyC, one_zpow, mul_one, hcc, h3]
  have e1 : ((y : ℝ) : ℂ) ^ (P.centralExponent + 1) = ((y : ℝ) : ℂ) ^ P.centralExponent * ((y : ℝ) : ℂ) := by
    rw [Complex.cpow_add _ _ hyC, Complex.cpow_one]
  have e2 : ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) =
      ((y : ℝ) : ℂ) ^ P.centralExponent * ((y : ℝ) : ℂ) ^ P₂.centralExponent *
        (((y : ℝ) : ℂ) ^ (s - 1 / 2) * ((y : ℝ) : ℂ) ^ (s - 1 / 2) * ((y : ℝ) : ℂ)) := by
    rw [show P.centralExponent + P₂.centralExponent + 2 * s =
        P.centralExponent + P₂.centralExponent + ((s - 1 / 2) + (s - 1 / 2) + 1) by ring]
    rw [Complex.cpow_add _ _ hyC, Complex.cpow_add _ _ hyC, Complex.cpow_add _ _ hyC, Complex.cpow_add _ _ hyC,
      Complex.cpow_one]
  rw [e1, e2]
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

end UNFOLDC

open UNFOLDC in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
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
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (par₀ : ZMod 2) :
    ∃ σu : ℝ, ∀ s : ℂ, σu < s.re →
      (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                ((WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
        = ∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)) := by
  classical
  obtain ⟨σB, hB⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
      K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz S hS par₀
  refine ⟨σB, fun s hs => ?_⟩
  have hI := hB s hs
  set H : ℝ × ℝ × (Fin 2 → Fin 2 → ℝ) → ℂ := fun p =>
    ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of p.2.2).det *
        (((|(Matrix.of p.2.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      (Wr par₀ default p.2.1 * D.W (ArchR.diagOne ((a : ℝ) * p.2.1) * (Matrix.of p.2.2)⁻¹) *
          (((|p.2.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((p.2.1 ^ 2)⁻¹ : ℝ) : ℂ)) *
      (((p.1 : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
        godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S (Matrix.of p.2.2) 1) with hH
  have hI' : Integrable H ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → Fin 2 → ℝ)))) := hI

  have hR : (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1))) =
      ∫ e : Fin 2 → Fin 2 → ℝ, ∫ t : ℝ, ∫ y in Set.Ioi (0 : ℝ), H (y, t, e) := by
    congr 1
    funext e
    simp only [hH]
    simp_rw [integral_const_mul]
    rw [integral_mul_const, integral_const_mul]
    ring

  have hL : (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                ((WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) =
      ∫ y in Set.Ioi (0 : ℝ), ∫ t : ℝ, ∫ e : Fin 2 → Fin 2 → ℝ, H (y, t, e) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    have hyne : y ≠ 0 := hy0.ne'

    set g : ℝ → ℂ := fun a₁ =>
      if ha : a₁ ≠ 0 ∧ 0 < y then
        let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 y ha.1 ha.2.ne'
        ((WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
          (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
      else 0 with hg

    have hsub : (∫ a₁ : ℝ, g a₁) = ((|y| : ℝ) : ℂ) * ∫ t : ℝ, g (y * t) := by
      rw [Measure.integral_comp_mul_left g y, Complex.real_smul, ← mul_assoc, abs_inv]
      push_cast
      rw [mul_inv_cancel₀ (by exact_mod_cast (abs_pos.mpr hyne).ne'), one_mul]
    show (∫ a₁ : ℝ, g a₁) = _
    rw [hsub, ← integral_const_mul]
    refine integral_congr_ae ?_
    have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hae] with t ht
    simp only [hg, hH]
    rw [dif_pos ⟨mul_ne_zero hyne ht, hy0⟩]
    rw [LanglandsTunnell.CubicInduction.jacquetVector3_iota_upperUnit_eq_integral_godementInner3_mulShift
      D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S (y * t) y (mul_ne_zero hyne ht) hyne,
      det_upperUnit y t hyne ht,
      upperUnit_eq_scalar_mul_diagOne y t hyne ht, hWAZ, hWAt]

    rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const, ← integral_const_mul]
    congr 1
    funext e
    rw [diagOne_mul_diag, Matrix.smul_mul, D.central_law y _ hyne]
    have key := ypow P P₂ s y t hy0 ht
    have hmk : (((Units.mk0 y hyne : ℝˣ) : ℝ)) = y := rfl
    have hmk' : (((Units.mk0 t ht : ℝˣ) : ℝ)) = t := rfl
    simp only [hmk, hmk']
    linear_combination (Wr par₀ default t *
      godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1 *
      ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹)) * key
  rw [hL, hR]
  exact integral3_swap _ _ _ H hI'

end S_LanglandsTunnell_RankinSelberg_exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin (solution)
