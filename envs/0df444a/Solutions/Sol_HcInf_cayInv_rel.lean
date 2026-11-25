-- Prove2me | solution 1 for HcInf.cayInv_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:28:57.376948+00:00
-- url     : https://prove2.me/submissions/2f52ef12-db66-4343-be63-e0ec049e2a90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
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
theorem _root_.solution (g : UpqT P Q) (hu : IsUnit (UpqT.mat g + 1).det) :
    UpqT.mat g * ((1 + 1) - ((cayInv P Q g : lieU P Q) : Mat)) = (1 + 1) + ((cayInv P Q g : lieU P Q) : Mat) := by
  rw [cayInv_eq]
  show UpqT.mat g * ((1 + 1) - cayCand P Q g) = (1 + 1) + cayCand P Q g
  unfold cayCand
  set G := UpqT.mat g
  set A := (G + 1)⁻¹
  have hAG : A * G = 1 - A := by
    have h := Matrix.nonsing_inv_mul _ hu
    rw [mul_add, mul_one] at h
    rw [← h]
    abel
  have hGA : G * A = 1 - A := by
    have h := Matrix.mul_nonsing_inv _ hu
    rw [add_mul, one_mul] at h
    rw [← h]
    abel
  have e1 : (1 + 1) * A * (G - 1) = (1 + 1) - (1 + 1) * A - (1 + 1) * A := by
    rw [Matrix.mul_assoc, mul_sub, hAG]
    noncomm_ring
  rw [e1]
  have e2 : G * ((1 + 1) - ((1 + 1) - (1 + 1) * A - (1 + 1) * A)) = G * A + G * A + G * A + G * A := by
    noncomm_ring
  rw [e2, hGA]
  noncomm_ring
end HcInf
