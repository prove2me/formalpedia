-- Prove2me | solution 1 for HcInf.cayley_inverse_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:24:23.389187+00:00
-- url     : https://prove2.me/submissions/3ca11c89-0c6a-4543-a1ca-65c3f0f5dab3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
import Theorems.Thm_HcInf_two_eq
import Theorems.Thm_HcInf_cayInv_eq

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
namespace HcInf
theorem _root_.solution : CayInvIff := by
  intro P Q g X h
  set G := UpqT.mat g with hG
  set Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
  rw [two_eq] at h
  have h4 : (G + 1) * ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y) =
      (4 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    rw [add_mul, one_mul, h, show (4 : ℂ) = 2 + 2 by norm_num, add_smul]
    abel
  have hB : (G + 1) * ((1 / 4 : ℂ) • ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - Y)) = 1 := by
    rw [Matrix.mul_smul, h4, smul_smul]
    norm_num
  have hu : IsUnit (G + 1).det := Matrix.isUnit_det_of_right_inverse hB
  have hGY : G * Y = (2 : ℂ) • G - ((2 : ℂ) • (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) + Y) := by
    rw [← h, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hXY : (G + 1) * Y = (2 : ℂ) • (G - 1) := by
    rw [add_mul, one_mul, hGY, smul_sub]
    abel
  have hc : cayCand P Q g = Y := by
    show (1 + 1) * (G + 1)⁻¹ * (G - 1) = Y
    have eY : Y = (G + 1)⁻¹ * ((G + 1) * Y) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [eY, hXY, Matrix.mul_smul, two_eq, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [cayInv_eq]
  exact Subtype.ext hc
end HcInf
