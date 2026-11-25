-- Prove2me | solution 1 for HcInf.tauL_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:27.97269+00:00
-- url     : https://prove2.me/submissions/b1262ae3-9891-4adb-8de2-2dfef516c375

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Theorems.Thm_HcInf_nH_eq
import Theorems.Thm_HcInf_cayInv_rel


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
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hu : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det) :
    ((tauL h x : lieU P Q) : Mat) =
      (1 + 1) - (4 : ℂ) • (((1 + 1) - (x : Mat)) * (nH h (x : Mat))⁻¹) := by
  have hrel := cayInv_rel (h * cayF P Q x) hu
  have hN := nH_eq h x hx
  have hA : IsUnit (UpqT.mat (h * cayF P Q x) + 1).det := hu
  have hB : IsUnit ((1 + 1) - (x : Mat)).det := hx
  change UpqT.mat (h * cayF P Q x) * ((1 + 1) - ((tauL h x : lieU P Q) : Mat)) =
    (1 + 1) + ((tauL h x : lieU P Q) : Mat) at hrel
  have h4 : (4 : ℂ) • (1 : Mat) = (1 + 1) + (1 + 1) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hAτ : (UpqT.mat (h * cayF P Q x) + 1) * ((tauL h x : lieU P Q) : Mat) =
      (UpqT.mat (h * cayF P Q x) + 1) * (1 + 1) - (4 : ℂ) • (1 : Mat) := by
    have e : UpqT.mat (h * cayF P Q x) * ((tauL h x : lieU P Q) : Mat) =
        UpqT.mat (h * cayF P Q x) * (1 + 1) - ((1 + 1) + ((tauL h x : lieU P Q) : Mat)) := by
      rw [← hrel, mul_sub]
      abel
    rw [add_mul, one_mul, e, add_mul, one_mul, h4]
    abel
  have hτ : ((tauL h x : lieU P Q) : Mat) = (1 + 1) - (4 : ℂ) • (UpqT.mat (h * cayF P Q x) + 1)⁻¹ := by
    calc ((tauL h x : lieU P Q) : Mat)
        = (UpqT.mat (h * cayF P Q x) + 1)⁻¹ *
            ((UpqT.mat (h * cayF P Q x) + 1) * ((tauL h x : lieU P Q) : Mat)) := by
          rw [← mul_assoc, Matrix.nonsing_inv_mul _ hA, one_mul]
      _ = (UpqT.mat (h * cayF P Q x) + 1)⁻¹ *
            ((UpqT.mat (h * cayF P Q x) + 1) * (1 + 1) - (4 : ℂ) • (1 : Mat)) := by rw [hAτ]
      _ = (1 + 1) - (4 : ℂ) • (UpqT.mat (h * cayF P Q x) + 1)⁻¹ := by
          rw [mul_sub, ← mul_assoc, Matrix.nonsing_inv_mul _ hA, one_mul, Matrix.mul_smul, mul_one]
  have hinv : (UpqT.mat (h * cayF P Q x) + 1)⁻¹ = ((1 + 1) - (x : Mat)) * (nH h (x : Mat))⁻¹ := by
    rw [hN, Matrix.mul_inv_rev, ← mul_assoc, Matrix.mul_nonsing_inv _ hB, one_mul]
  rw [hτ, hinv]
end HcInf
