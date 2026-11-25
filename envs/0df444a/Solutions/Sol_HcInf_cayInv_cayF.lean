-- Prove2me | solution 1 for HcInf.cayInv_cayF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:14.047429+00:00
-- url     : https://prove2.me/submissions/18748620-821c-4d2e-a41b-c0bebfcb0594

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_chart_units
import Theorems.Thm_HcInf_cayF_spec
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
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (X : lieU P Q) (hX : X ∈ D0 P Q) : cayInv P Q (cayF P Q X) = X := by
  rw [cayInv_eq]
  apply Subtype.ext
  show (1 + 1) * (UpqT.mat (cayF P Q X) + 1)⁻¹ * (UpqT.mat (cayF P Q X) - 1) =
    ((X : lieU P Q) : Mat)
  have hs := cayF_spec X hX
  set Y : Mat := ((X : lieU P Q) : Mat)
  set G := UpqT.mat (cayF P Q X)
  obtain ⟨h4, -, hB⟩ := chart_units G Y hs
  have hinv : (G + 1)⁻¹ = (4 : ℂ)⁻¹ • ((1 + 1) - Y) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, h4, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have hGm : (G - 1) * ((1 + 1) - Y) = Y + Y := by
    rw [sub_mul, hs, one_mul]
    abel
  have hG1 : G - 1 = (Y + Y) * ((1 + 1) - Y)⁻¹ := by
    rw [← hGm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  have hc : ((1 + 1) - Y) * (Y + Y) = (Y + Y) * ((1 + 1) - Y) := by noncomm_ring
  have h4Y : (1 + 1 : Mat) * (Y + Y) = (4 : ℂ) • Y := by
    rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]
    noncomm_ring
  rw [hinv, hG1]
  calc (1 + 1) * ((4 : ℂ)⁻¹ • ((1 + 1) - Y)) * ((Y + Y) * ((1 + 1) - Y)⁻¹)
      = (4 : ℂ)⁻¹ • ((1 + 1) * ((((1 + 1) - Y) * (Y + Y)) * ((1 + 1) - Y)⁻¹)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (4 : ℂ)⁻¹ • ((1 + 1) * (Y + Y)) := by
        rw [hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = Y := by
        rw [h4Y, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
end HcInf
