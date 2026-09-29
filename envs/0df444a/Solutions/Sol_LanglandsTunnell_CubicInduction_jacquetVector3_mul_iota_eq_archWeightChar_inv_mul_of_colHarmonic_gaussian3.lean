-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9b3e2f5d-ed5d-5e97-aa34-5093f7cd8a67

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

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_colHarmonic_gaussian3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws23K6A

open AutomorphicForm.StandardKernel

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _

noncomputable abbrev ιh (κ : GL (Fin 2) ℝ) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt hR κ))

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl : v = default := Subsingleton.elim _ _
  show AutomorphicForm.archMatrixUpdate ℚ default ((glEquivOfRingEquiv (ringEquivRealOfIsReal hR).symm M :
    GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
  rw [AutomorphicForm.archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem val_ιh_apply (h : GL (Fin 2) ℝ) (i j : Fin 3) :
    ((ιh h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      (embedMat2 ((archRealGLAt hR h : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 :=
  rfl

theorem realCoord_fst_archRealGLAt (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    realCoord (((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      (M : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  rw [realCoord_apply]
  show (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      ((((archRealGLAt hR M : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 Rat.infinitePlace) = _
  rw [iotaR_fst]
  exact (ringEquivRealOfIsReal _).apply_symm_apply _

theorem realMat_ιh (κ : GL (Fin 2) ℝ) : realMat (ιh κ) = embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  rw [realMat_eq, Matrix.map_apply, val_ιh_apply]
  fin_cases i <;> fin_cases j <;> simp [embedMat2, realCoord_fst_archRealGLAt] <;>
    first | exact map_zero realCoord | exact map_one realCoord

theorem det_embedMat2 (M : Matrix (Fin 2) (Fin 2) ℝ) : (embedMat2 M).det = M.det := by
  simp [embedMat2, Matrix.det_fin_three, Matrix.det_fin_two]

theorem lines_mul (m E : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    (Matrix.of ![fun b => (m * E) 0 b + v 0 * (m * E) 2 b, fun b => (m * E) 1 b + v 1 * (m * E) 2 b] : Matrix (Fin 2) (Fin 3) ℝ) =
      (Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b] : Matrix (Fin 2) (Fin 3) ℝ) * E := by
  ext i b
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem godementInner3_mul_right (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (c : ℂ) (hSE : ∀ M : Matrix (Fin 2) (Fin 3) ℝ, S (M * E) = c * S M)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ S h (m * E) = c * godementInner3 ψ S h m := by
  rw [godementInner3, godementInner3, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  show S (h * _) * _ = c * (S (h * _) * _)
  rw [lines_mul, ← Matrix.mul_assoc, hSE, mul_assoc]

theorem colHarmonic_mul_embed (p : ℝ → ℝ → ℂ) (m δ : ℕ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => p (M 0 2) (M 1 2) * (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        (((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m) *
        gaussian3 M)
    {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (M : Matrix (Fin 2) (Fin 3) ℝ) :
    S (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) - Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m * S M := by
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hκ
  have e0 : ∀ i : Fin 2, (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 0 =
      M i 0 * (κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - M i 1 * (κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_three, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
    linear_combination (M i 1) * h10
  have e1 : ∀ i : Fin 2, (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 1 =
      M i 0 * (κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + M i 1 * (κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    intro i
    simp only [Matrix.mul_apply, Fin.sum_univ_three, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
    linear_combination (M i 1) * h11
  have e2 : ∀ i : Fin 2, (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 2 = M i 2 := by
    intro i
    simp [Matrix.mul_apply, Fin.sum_univ_three, embedMat2]
  have hsum : ∀ i : Fin 2, (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 0 ^ 2 + (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 1 ^ 2 +
      (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) i 2 ^ 2 = M i 0 ^ 2 + M i 1 ^ 2 + M i 2 ^ 2 := by
    intro i
    rw [e0, e1, e2]
    linear_combination (M i 0 ^ 2 + M i 1 ^ 2) * hab
  have hg : gaussian3 (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) = gaussian3 M := by
    simp only [gaussian3, Fin.sum_univ_three, hsum]
  have hdet : (((M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 * (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 -
      (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 * (M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℝ) : ℂ) =
      (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ)) : ℂ) := by
    congr 1
    rw [e0, e0, e1, e1]
    linear_combination (M 0 0 * M 1 1 - M 0 1 * M 1 0) * hab
  have hz : ((((M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 : ℝ) : ℂ) + Complex.I * (((M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 : ℝ) : ℂ)) -
        Complex.I * ((((M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 : ℝ) : ℂ) + Complex.I * (((M * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 : ℝ) : ℂ)) =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) - Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) := by
    rw [e0, e0, e1, e1]
    push_cast
    linear_combination (-((M 0 1 : ℂ) * ((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) +
      ((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * (M 1 1 : ℂ) * Complex.I)) * Complex.I_sq
  rw [hS]
  simp only []
  rw [hg, hdet, hz, e2, e2, mul_pow]
  ring

theorem archWeightCharℝ_coe (m : ℕ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) + Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m := by
  have h1 : ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) = ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) ^ m := by
    show (((archWeightOneℝ ⟨κ, hκ⟩) ^ (m : ℤ) : ℂˣ) : ℂ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have h2 : ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) = firstRowℂ κ := rfl
  rw [h1, h2]
  congr 1
  apply Complex.ext <;> simp [firstRowℂ]

theorem archWeightCharℝ_coe_inv (m : ℕ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    (((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ))⁻¹ =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) - Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m := by
  obtain ⟨-, -, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ hκ
  rw [archWeightCharℝ_coe, ← inv_pow]
  congr 1
  refine inv_eq_of_mul_eq_one_right ?_
  have : ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ)) ^ 2 + ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ 2 = 1 := by
    exact_mod_cast hab
  linear_combination this - ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ 2 * Complex.I_sq

end Ws23K6A

open Ws23K6A AutomorphicForm.StandardKernel in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
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
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (p : ℝ → ℝ → ℂ) (m δ : ℕ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => p (M 0 2) (M 1 2) * (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        (((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m) *
        gaussian3 M)
    (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S
        (g * archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ)))
      = ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂ))⁻¹ * jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g := by

  have hdetκ : (κ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff ℝ).1 hκ).1
  have hRM : realMat (g * ιh κ) = realMat g * embedMat2 (κ : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [realMat_mul, realMat_ιh]
  have hdet3 : (realMat (g * ιh κ)).det = (realMat g).det := by
    rw [hRM, Matrix.det_mul, det_embedMat2, hdetκ, mul_one]
  set c : ℂ := ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) - Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m with hc
  have hSE := colHarmonic_mul_embed p m δ S hS hκ
  show jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S (g * ιh κ) = _
  have hint : (fun e : Fin 2 → Fin 2 → ℝ => jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S (g * ιh κ) e) =
      fun e : Fin 2 → Fin 2 → ℝ => c * jacquetIntegrand3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g e := by
    funext e
    simp only [jacquetIntegrand3]
    rw [hRM, godementInner3_mul_right psiInf S _ c hSE]
    ring
  rw [archWeightCharℝ_coe_inv m hκ, jacquetVector3_eq, jacquetVector3_eq, hdet3, hint, integral_const_mul]
  ring

#print axioms solution

end S_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_colHarmonic_gaussian3 (solution)
