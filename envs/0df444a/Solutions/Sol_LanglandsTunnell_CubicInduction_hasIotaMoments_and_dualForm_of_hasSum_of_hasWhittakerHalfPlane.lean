-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/88ec717a-9aa7-5ddd-a41e-de4feacb0a2a

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

section

open IsDedekindDomain NumberField AutomorphicForm
open scoped Matrix

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "transposeInv3 whittaker3 dualForm detNorm HasIotaMoments HasWhittakerHalfPlane mirabolicTranslate AdelicGL embedMat2 iotaGL iota MirabolicIndex mirabolicRep"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Estimates

private theorem zpow_le_zpow_add_zpow_neg {x : ℝ} (hx : 0 < x) {k n : ℤ} (hk : -n ≤ k) (hk' : k ≤ n) :
    x ^ k ≤ x ^ n + x ^ (-n) := by
  rcases le_total 1 x with hx1 | hx1
  · exact (zpow_le_zpow_right₀ hx1 hk').trans (le_add_of_nonneg_right (zpow_pos hx _).le)
  · exact (zpow_le_zpow_right_of_le_one₀ hx hx1 hk).trans (le_add_of_nonneg_left (zpow_pos hx _).le)

private theorem coe_nnnorm_le_tsum_of_hasSum {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) :
    (‖a‖₊ : ENNReal) ≤ ∑' i, (‖f i‖₊ : ENNReal) := by
  by_cases hs : Summable fun i => ‖f i‖₊
  · rw [← ENNReal.coe_tsum hs, ← h.tsum_eq]
    exact ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hs)
  · have htop : (∑' i, (‖f i‖₊ : ENNReal)) = ⊤ :=
      not_ne_iff.mp fun h' => hs (ENNReal.tsum_coe_ne_top_iff_summable.mp h')
    rw [htop]
    exact le_top

end Estimates

section MirabolicAlongIota

private theorem iota_globalPoints_mirabolicRep_mul (i : MirabolicIndex ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g) = mirabolicTranslate i * iota (𝓞 ℚ) ℚ g := by
  rw [map_mul]
  rfl

end MirabolicAlongIota

section TransposeInverse

variable {A : Type*} [CommRing A]

private def transposeInv2 (g : GL (Fin 2) A) : GL (Fin 2) A where
  val := ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
  inv := ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

@[scoped simp] private theorem coe_transposeInv2 (g : GL (Fin 2) A) :
    ((transposeInv2 g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ :=
  rfl

private theorem coe_transposeInv2_inv (g : GL (Fin 2) A) :
    (((transposeInv2 g)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ :=
  rfl

private theorem transposeInv2_transposeInv2 (g : GL (Fin 2) A) : transposeInv2 (transposeInv2 g) = g :=
  Units.ext (by
    show ((g : Matrix (Fin 2) (Fin 2) A)ᵀ)ᵀ = (g : Matrix (Fin 2) (Fin 2) A)
    exact Matrix.transpose_transpose _)

private theorem transposeInv2_mul (g h : GL (Fin 2) A) :
    transposeInv2 (g * h) = transposeInv2 g * transposeInv2 h :=
  Units.ext (by
    show ((((g * h)⁻¹ : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A)ᵀ =
      ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ * ((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

private theorem transposeInv2_one : transposeInv2 (1 : GL (Fin 2) A) = 1 :=
  Units.ext (by
    show (((1 : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ = (1 : Matrix (Fin 2) (Fin 2) A)
    rw [inv_one, Units.val_one, Matrix.transpose_one])

private def transposeInv2Equiv : GL (Fin 2) A ≃* GL (Fin 2) A where
  toFun := transposeInv2
  invFun := transposeInv2
  left_inv := transposeInv2_transposeInv2
  right_inv := transposeInv2_transposeInv2
  map_mul' := transposeInv2_mul

@[scoped simp] private theorem transposeInv2Equiv_apply (g : GL (Fin 2) A) : transposeInv2Equiv g = transposeInv2 g :=
  rfl

private theorem transposeInv2Equiv_symm : (transposeInv2Equiv (A := A)).symm = transposeInv2Equiv :=
  MulEquiv.ext fun _ => rfl

private theorem det_transposeInv2 (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (transposeInv2 g) = (Matrix.GeneralLinearGroup.det g)⁻¹ :=
  Units.ext (by
    show (((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ).det =
      ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).det
    exact Matrix.det_transpose _)

private theorem embedMat2_transpose (M : Matrix (Fin 2) (Fin 2) A) : embedMat2 Mᵀ = (embedMat2 M)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

private theorem transposeInv3_iotaGL (h : GL (Fin 2) A) : transposeInv3 (iotaGL h) = iotaGL (transposeInv2 h) :=
  Units.ext (by
    show (embedMat2 ((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))ᵀ =
      embedMat2 (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ)
    exact (embedMat2_transpose _).symm)

end TransposeInverse

section Adelic

private theorem transposeInv3_iota (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    transposeInv3 (iota (𝓞 ℚ) ℚ g) = iota (𝓞 ℚ) ℚ (transposeInv2 g) :=
  transposeInv3_iotaGL g

private theorem dualForm_iota (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    dualForm Φ (iota (𝓞 ℚ) ℚ g) = Φ (iota (𝓞 ℚ) ℚ (transposeInv2 g)) := by
  unfold dualForm
  rw [transposeInv3_iota]

private theorem transposeInv3_transposeInv3 {F : Type*} [CommRing F] (g : GL (Fin 3) F) :
    transposeInv3 (transposeInv3 g) = g :=
  Units.ext (by
    show ((g : Matrix (Fin 3) (Fin 3) F)ᵀ)ᵀ = (g : Matrix (Fin 3) (Fin 3) F)
    exact Matrix.transpose_transpose _)

private theorem dualForm_dualForm (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : dualForm (dualForm Φ) = Φ := by
  funext g
  unfold dualForm
  rw [transposeInv3_transposeInv3]

private theorem ideleNorm_inv (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : TateGlobal.ideleNorm ℚ x⁻¹ =
    (TateGlobal.ideleNorm ℚ x)⁻¹ := by
  have h1 : TateGlobal.ideleNorm ℚ x * TateGlobal.ideleNorm ℚ x⁻¹ = 1 := by
    rw [← TateGlobal.ideleNorm_mul, mul_inv_cancel]
    unfold TateGlobal.ideleNorm
    rw [map_one, NNReal.coe_one]
  exact eq_inv_of_mul_eq_one_right h1

private theorem detNorm_transposeInv2 (g : AdelicGL2 (𝓞 ℚ) ℚ) : detNorm (transposeInv2 g) = (detNorm g)⁻¹ := by
  unfold detNorm
  rw [det_transposeInv2, ideleNorm_inv]

end Adelic

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

section

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped Matrix

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "transposeInv3 whittaker3 dualForm detNorm HasIotaMoments HasWhittakerHalfPlane mirabolicTranslate AdelicGL embedMat2 iotaGL iota MirabolicIndex mirabolicRep"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section ContinuousTransposeInverse

variable {A : Type*} [CommRing A] [TopologicalSpace A]

private theorem continuous_transposeInv2 : Continuous (transposeInv2 : GL (Fin 2) A → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 2) A => ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)ᵀ
    exact Units.continuous_val.matrix_transpose

private def transposeInv2ContinuousEquiv : GL (Fin 2) A ≃ₜ* GL (Fin 2) A :=
  { transposeInv2Equiv with
    continuous_toFun := continuous_transposeInv2
    continuous_invFun := continuous_transposeInv2 }

@[scoped simp] private theorem transposeInv2ContinuousEquiv_apply (g : GL (Fin 2) A) :
    transposeInv2ContinuousEquiv g = transposeInv2 g :=
  rfl

private theorem coe_transposeInv2ContinuousEquiv :
    ⇑(transposeInv2ContinuousEquiv (A := A)) = transposeInv2 :=
  rfl

private theorem transposeInv2ContinuousEquiv_trans_self :
    (transposeInv2ContinuousEquiv (A := A)).trans transposeInv2ContinuousEquiv = ContinuousMulEquiv.refl _ :=
  ContinuousMulEquiv.ext fun g => transposeInv2_transposeInv2 g

end ContinuousTransposeInverse
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

section RationalPoints

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem transposeInv2_map (f : R →+* S) (q : GL (Fin 2) R) :
    transposeInv2 (Matrix.GeneralLinearGroup.map f q) = Matrix.GeneralLinearGroup.map f (transposeInv2 q) :=
  Units.ext (by
    show (((q⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f)ᵀ =
      (((q⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ).map f
    exact Matrix.transpose_map.symm)

end RationalPoints
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

section Adelic

private theorem transposeInv2_globalPoints (q : GL (Fin 2) ℚ) :
    transposeInv2 (globalPoints (𝓞 ℚ) ℚ q) = globalPoints (𝓞 ℚ) ℚ (transposeInv2 q) :=
  transposeInv2_map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) q

private theorem transposeInv2_mem_range_globalPoints {x : AdelicGL2 (𝓞 ℚ) ℚ} (hx : x ∈ (globalPoints (𝓞 ℚ) ℚ).range) :
    transposeInv2 x ∈ (globalPoints (𝓞 ℚ) ℚ).range := by
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hx
  exact MonoidHom.mem_range.mpr ⟨transposeInv2 q, (transposeInv2_globalPoints q).symm⟩

private def rangeTransposeInv2 : (globalPoints (𝓞 ℚ) ℚ).range ≃ (globalPoints (𝓞 ℚ) ℚ).range where
  toFun γ := ⟨transposeInv2 γ, transposeInv2_mem_range_globalPoints γ.2⟩
  invFun γ := ⟨transposeInv2 γ, transposeInv2_mem_range_globalPoints γ.2⟩
  left_inv γ := Subtype.ext (transposeInv2_transposeInv2 (γ : AdelicGL2 (𝓞 ℚ) ℚ))
  right_inv γ := Subtype.ext (transposeInv2_transposeInv2 (γ : AdelicGL2 (𝓞 ℚ) ℚ))

private theorem coe_rangeTransposeInv2 (γ : (globalPoints (𝓞 ℚ) ℚ).range) :
    ((rangeTransposeInv2 γ : (globalPoints (𝓞 ℚ) ℚ).range) : AdelicGL2 (𝓞 ℚ) ℚ) = transposeInv2 γ :=
  rfl

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private theorem isHaarMeasure_mu2 : Measure.IsHaarMeasure (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ

private theorem regular_mu2 : Measure.Regular (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  unfold NumberField.AdelicHaar.adelicGLHaar
  exact Measure.regular_haarMeasure

private theorem mulEquivHaarChar_transposeInv2 :
    mulEquivHaarChar (transposeInv2ContinuousEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  have hsq : mulEquivHaarChar (transposeInv2ContinuousEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ) *
      mulEquivHaarChar (transposeInv2ContinuousEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    rw [← mulEquivHaarChar_trans, transposeInv2ContinuousEquiv_trans_self, mulEquivHaarChar_refl]
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).mp (by rw [sq]; exact hsq)

private theorem map_transposeInv2_mu2 : Measure.map transposeInv2 (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
    = (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  haveI := isHaarMeasure_mu2
  haveI := regular_mu2
  have h := mulEquivHaarChar_smul_map (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
    (transposeInv2ContinuousEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ)
  rwa [mulEquivHaarChar_transposeInv2, one_smul, coe_transposeInv2ContinuousEquiv] at h

private theorem measurePreserving_transposeInv2 :
    MeasurePreserving (transposeInv2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.adelicGLHaar
        (Fin 2) (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  ⟨continuous_transposeInv2.measurable, map_transposeInv2_mu2⟩

private theorem isFundamentalDomain_image_transposeInv2 {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range (transposeInv2 '' D) (NumberField.AdelicHaar.adelicGLHaar (Fin 2)
        (𝓞 ℚ) ℚ) := by
  exact hD.image_of_equiv (transposeInv2Equiv : AdelicGL2 (𝓞 ℚ) ℚ ≃* AdelicGL2 (𝓞 ℚ) ℚ).toEquiv
    measurePreserving_transposeInv2.quasiMeasurePreserving rangeTransposeInv2 fun γ x => by
      show transposeInv2 (transposeInv2 (γ : AdelicGL2 (𝓞 ℚ) ℚ) * x) = (γ : AdelicGL2 (𝓞 ℚ) ℚ) * transposeInv2 x
      rw [transposeInv2_mul, transposeInv2_transposeInv2]

end Adelic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

section

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "transposeInv3 whittaker3 dualForm detNorm HasIotaMoments HasWhittakerHalfPlane mirabolicTranslate AdelicGL embedMat2 iotaGL iota MirabolicIndex mirabolicRep"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Moments

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private theorem detNorm_pos (g : AdelicGL2 (𝓞 ℚ) ℚ) : 0 < detNorm g :=
  TateGlobal.ideleNorm_pos _

private theorem preimage_transposeInv2_eq_image (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    transposeInv2 ⁻¹' D = transposeInv2 '' D :=
  (congrFun (Set.image_eq_preimage_of_inverse (g := (transposeInv2 : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ))
    transposeInv2_transposeInv2 transposeInv2_transposeInv2) D).symm

private theorem isFundamentalDomain_preimage_transposeInv2 {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)) :
    IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range (transposeInv2 ⁻¹' D) (NumberField.AdelicHaar.adelicGLHaar (Fin 2)
        (𝓞 ℚ) ℚ) := by
  rw [preimage_transposeInv2_eq_image]
  exact isFundamentalDomain_image_transposeInv2 hD

private def transposeInv2MeasurableEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ᵐ AdelicGL2 (𝓞 ℚ) ℚ :=
  (transposeInv2ContinuousEquiv : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* AdelicGL2 (𝓞 ℚ) ℚ).toHomeomorph.toMeasurableEquiv

private theorem coe_transposeInv2MeasurableEquiv : ⇑transposeInv2MeasurableEquiv = transposeInv2 :=
  rfl

private theorem map_transposeInv2MeasurableEquiv_mu2 : Measure.map transposeInv2MeasurableEquiv
    (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  rw [coe_transposeInv2MeasurableEquiv]
  exact map_transposeInv2_mu2

private theorem lintegral_comp_transposeInv2 (F : AdelicGL2 (𝓞 ℚ) ℚ → ENNReal) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :
    ∫⁻ g in D, F g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = ∫⁻ h in transposeInv2 ⁻¹' D, F
        (transposeInv2 h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  calc ∫⁻ g in D, F g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)
      = ∫⁻ g in D, F g ∂(Measure.map transposeInv2MeasurableEquiv (NumberField.AdelicHaar.adelicGLHaar (Fin 2)
          (𝓞 ℚ) ℚ)) := by
        rw [map_transposeInv2MeasurableEquiv_mu2]
    _ = ∫⁻ g, F g
          ∂(Measure.map transposeInv2MeasurableEquiv ((NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
              (transposeInv2MeasurableEquiv ⁻¹' D))) := by
        rw [transposeInv2MeasurableEquiv.measurableEmbedding.restrict_map]
    _ = ∫⁻ h in transposeInv2 ⁻¹' D, F (transposeInv2 h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2)
        (𝓞 ℚ) ℚ) := lintegral_map_equiv F transposeInv2MeasurableEquiv

private theorem exists_forall_lintegral_nnnorm_mul_ofReal_zpow_lt_top (Φ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ g))
    (hhp : HasWhittakerHalfPlane W) :
    ∃ σ₀ : ℝ, ∀ n : ℤ, σ₀ ≤ n → ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
      ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ n)
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) < ⊤ := by
  obtain ⟨σ₀, h⟩ := hhp
  refine ⟨σ₀, fun n hn D hD => lt_of_le_of_lt (lintegral_mono fun g => ?_) (h n hn D hD)⟩
  simp only [iota_globalPoints_mirabolicRep_mul, Real.rpow_intCast]
  exact mul_le_mul_left (coe_nnnorm_le_tsum_of_hasSum (hexp _)) _

private theorem lintegral_nnnorm_mul_ofReal_zpow_neg_eq (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (n : ℤ) :
    ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ (-n))
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
      ∫⁻ h in transposeInv2 ⁻¹' D,
        (‖dualForm Φ (iota (𝓞 ℚ) ℚ h)‖₊ : ENNReal) * ENNReal.ofReal (detNorm h ^ n)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  rw [lintegral_comp_transposeInv2]
  refine lintegral_congr fun h => ?_
  rw [detNorm_transposeInv2, inv_zpow', neg_neg, dualForm_iota]

private theorem measurableSet_one_le_detNorm (hcont : Continuous detNorm) :
    MeasurableSet {g : AdelicGL2 (𝓞 ℚ) ℚ | 1 ≤ detNorm g} :=
  measurableSet_le measurable_const hcont.measurable

private theorem zpow_add_zpow_neg_le_two_mul_zpow {x : ℝ} (hx1 : 1 ≤ x) {N : ℕ} {n : ℤ} (hn : (N : ℤ) ≤ n) :
    x ^ (N : ℤ) + x ^ (-(N : ℤ)) ≤ 2 * x ^ n := by
  rw [two_mul]
  exact add_le_add (zpow_le_zpow_right₀ hx1 hn) (zpow_le_zpow_right₀ hx1 (by omega))

private theorem zpow_add_zpow_neg_le_two_mul_zpow_neg {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {N : ℕ} {n : ℤ}
    (hn : (N : ℤ) ≤ n) : x ^ (N : ℤ) + x ^ (-(N : ℤ)) ≤ 2 * x ^ (-n) := by
  rw [two_mul]
  exact add_le_add (zpow_le_zpow_right_of_le_one₀ hx hx1 (by omega)) (zpow_le_zpow_right_of_le_one₀ hx hx1 (by omega))

private theorem nnnorm_mul_ofReal_le_two_mul {a : ENNReal} {p q : ℝ} (hpq : p ≤ 2 * q) :
    a * ENNReal.ofReal p ≤ 2 * (a * ENNReal.ofReal q) := by
  rw [mul_left_comm]
  refine mul_le_mul_right ((ENNReal.ofReal_le_ofReal hpq).trans (le_of_eq ?_)) a
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

private theorem hasIotaMoments_of_hasSum_of_hasWhittakerHalfPlane (Φ W W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ g))
    (hexp' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Φ g))
    (hhp : HasWhittakerHalfPlane W) (hhp' : HasWhittakerHalfPlane W')
    (hE : MeasurableSet {g : AdelicGL2 (𝓞 ℚ) ℚ | 1 ≤ detNorm g}) : HasIotaMoments Φ := by
  obtain ⟨σ₀, hplus⟩ := exists_forall_lintegral_nnnorm_mul_ofReal_zpow_lt_top Φ W hexp hhp
  obtain ⟨σ₀', hplus'⟩ := exists_forall_lintegral_nnnorm_mul_ofReal_zpow_lt_top (dualForm Φ) W' hexp' hhp'
  intro D hD N
  obtain ⟨n, hnN, hnσ, hnσ'⟩ : ∃ n : ℤ, (N : ℤ) ≤ n ∧ σ₀ ≤ n ∧ σ₀' ≤ n := by
    refine ⟨max (N : ℤ) (max ⌈σ₀⌉ ⌈σ₀'⌉), le_max_left _ _, ?_, ?_⟩
    · have h1 : ⌈σ₀⌉ ≤ max (N : ℤ) (max ⌈σ₀⌉ ⌈σ₀'⌉) := (le_max_left _ _).trans (le_max_right _ _)
      exact (Int.le_ceil σ₀).trans (by exact_mod_cast h1)
    · have h1 : ⌈σ₀'⌉ ≤ max (N : ℤ) (max ⌈σ₀⌉ ⌈σ₀'⌉) := (le_max_right _ _).trans (le_max_right _ _)
      exact (Int.le_ceil σ₀').trans (by exact_mod_cast h1)
  have hA := hplus n hnσ D hD
  have hB : ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ (-n))
      ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) < ⊤ := by
    rw [lintegral_nnnorm_mul_ofReal_zpow_neg_eq]
    exact hplus' n hnσ' _ (isFundamentalDomain_preimage_transposeInv2 hD)
  rw [← lintegral_inter_add_diff _ D hE]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · calc ∫⁻ g in D ∩ {g | 1 ≤ detNorm g}, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) *
            ENNReal.ofReal (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2)
                (𝓞 ℚ) ℚ)
        ≤ ∫⁻ g in D ∩ {g | 1 ≤ detNorm g},
            2 * ((‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ n))
                ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
          refine lintegral_mono_ae ((ae_restrict_mem₀ (hD.nullMeasurableSet.inter hE.nullMeasurableSet)).mono
            fun g hg => ?_)
          exact nnnorm_mul_ofReal_le_two_mul (zpow_add_zpow_neg_le_two_mul_zpow hg.2 hnN)
      _ = 2 * ∫⁻ g in D ∩ {g | 1 ≤ detNorm g},
            (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ n) ∂(NumberField.AdelicHaar.adelicGLHaar
                (Fin 2) (𝓞 ℚ) ℚ) :=
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ ≤ 2 * ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ n)
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
          mul_le_mul_right (lintegral_mono_set Set.inter_subset_left) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top hA
  · calc ∫⁻ g in D \ {g | 1 ≤ detNorm g}, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) *
            ENNReal.ofReal (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2)
                (𝓞 ℚ) ℚ)
        ≤ ∫⁻ g in D \ {g | 1 ≤ detNorm g},
            2 * ((‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ (-n)))
                ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
          refine lintegral_mono_ae ((ae_restrict_mem₀ (hD.nullMeasurableSet.diff hE.nullMeasurableSet)).mono
            fun g hg => ?_)
          exact nnnorm_mul_ofReal_le_two_mul
            (zpow_add_zpow_neg_le_two_mul_zpow_neg (detNorm_pos g) (not_le.mp hg.2).le hnN)
      _ = 2 * ∫⁻ g in D \ {g | 1 ≤ detNorm g},
            (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ (-n)) ∂(NumberField.AdelicHaar.adelicGLHaar
                (Fin 2) (𝓞 ℚ) ℚ) :=
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
      _ ≤ 2 * ∫⁻ g in D, (‖Φ (iota (𝓞 ℚ) ℚ g)‖₊ : ENNReal) * ENNReal.ofReal (detNorm g ^ (-n))
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
          mul_le_mul_right (lintegral_mono_set Set.diff_subset) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top hB

private theorem hasIotaMoments_and_dualForm_of_measurableSet (Φ W W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ g))
    (hexp' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Φ g))
    (hhp : HasWhittakerHalfPlane W) (hhp' : HasWhittakerHalfPlane W')
    (hE : MeasurableSet {g : AdelicGL2 (𝓞 ℚ) ℚ | 1 ≤ detNorm g}) :
    HasIotaMoments Φ ∧ HasIotaMoments (dualForm Φ) :=
  ⟨hasIotaMoments_of_hasSum_of_hasWhittakerHalfPlane Φ W W' hexp hexp' hhp hhp' hE,
    hasIotaMoments_of_hasSum_of_hasWhittakerHalfPlane (dualForm Φ) W' W hexp' (by rwa [dualForm_dualForm]) hhp' hhp hE⟩

end Moments
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane.LanglandsTunnell.CubicInduction in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (mirabolicTranslate i * g))
      (Φ g))
    (hexp' : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum
      (fun i : MirabolicIndex ℚ =>
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ) (mirabolicTranslate i * g))
      (dualForm Φ g))
    (hhp : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ))
    (hhp' : HasWhittakerHalfPlane (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ))) :
    HasIotaMoments Φ ∧ HasIotaMoments (dualForm Φ) := by
  exact hasIotaMoments_and_dualForm_of_measurableSet Φ
    (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ)
    (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm Φ)) hexp hexp' hhp hhp'
    (measurableSet_one_le_detNorm (TateGlobal.continuous_ideleNorm_det ℚ))

end S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_hasIotaMoments_and_dualForm_of_hasSum_of_hasWhittakerHalfPlane (solution)
