-- Prove2me | solution 1 for HcInf.cay_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:15:09.271549+00:00
-- url     : https://prove2.me/submissions/5e0e0634-8cfe-4d7a-939a-21e5ea89a966

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (X : lieU P Q) (hX : X ∈ D0 P Q) :
    ∃ g : UpqT P Q, UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat) := by
  set Y : Mat := ((X : lieU P Q) : Mat) with hY
  have hXm : Yᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * Y = 0 := X.2
  have hB : IsUnit ((1 + 1) - Y).det := hX
  have hBH : IsUnit ((1 + 1) - Y)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hB.star
  have hJY : Yᴴ * HcS.UG.Jpq P Q = -(HcS.UG.Jpq P Q * Y) := eq_neg_of_add_eq_zero_left hXm
  have h1 : ((1 + 1) + Y)ᴴ * HcS.UG.Jpq P Q = HcS.UG.Jpq P Q * ((1 + 1) - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_one, add_mul,
      add_mul, hJY, mul_sub, mul_add]
    noncomm_ring
  have h2 : HcS.UG.Jpq P Q * ((1 + 1) + Y) = ((1 + 1) - Y)ᴴ * HcS.UG.Jpq P Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, sub_mul,
      add_mul, hJY, mul_add]
    noncomm_ring
  have hcomm : ((1 + 1) - Y) * ((1 + 1) + Y) = ((1 + 1) + Y) * ((1 + 1) - Y) := by noncomm_ring
  obtain ⟨G, hG⟩ : ∃ G : Mat, G = ((1 + 1) + Y) * ((1 + 1) - Y)⁻¹ := ⟨_, rfl⟩
  have hU : Gᴴ * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q := by
    calc Gᴴ * HcS.UG.Jpq P Q * G
        = (((1 + 1) - Y)ᴴ)⁻¹ * ((((1 + 1) + Y)ᴴ * HcS.UG.Jpq P Q) * ((1 + 1) + Y)) *
            ((1 + 1) - Y)⁻¹ := by
          rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
      _ = (((1 + 1) - Y)ᴴ)⁻¹ * HcS.UG.Jpq P Q * (((1 + 1) - Y) * ((1 + 1) + Y)) *
            ((1 + 1) - Y)⁻¹ := by
          rw [h1]
          simp only [Matrix.mul_assoc]
      _ = (((1 + 1) - Y)ᴴ)⁻¹ * (HcS.UG.Jpq P Q * ((1 + 1) + Y)) *
            (((1 + 1) - Y) * ((1 + 1) - Y)⁻¹) := by
          rw [hcomm]
          simp only [Matrix.mul_assoc]
      _ = HcS.UG.Jpq P Q := by
          rw [h2, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, ← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hBH, Matrix.one_mul]
  have hJ : IsUnit (HcS.UG.Jpq P Q).det := by
    rw [HcS.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one,
      one_mul, mul_one]
    exact IsUnit.pow _ isUnit_neg_one
  have hGd : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hd := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at hd
    exact hJ.ne_zero hd.symm
  have hcT : HcS.UG.cT (starRingEnd ℂ) G = Gᴴ := by
    ext i j
    simp [HcS.UG.cT, Matrix.conjTranspose_apply]
  refine ⟨(⟨Matrix.nonsingInvUnit G hGd, ?_⟩ : HcS.UG.Upq P Q), ?_⟩
  · show HcS.UG.cT (starRingEnd ℂ) G * HcS.UG.Jpq P Q * G = HcS.UG.Jpq P Q
    rw [hcT, hU]
  · show G * ((1 + 1) - Y) = (1 + 1) + Y
    rw [hG, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
end HcInf
