-- Prove2me | solution 1 for HcInf.cayF_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:52.323414+00:00
-- url     : https://prove2.me/submissions/a33f581d-7224-4f66-8c3d-5e9c3a90fc2b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_cayF_spec
import Theorems.Thm_HcInf_mem_cayley_domain_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
section Chart
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
private theorem upqT_eq_of_mat_eq {g h : UpqT P Q} (e : UpqT.mat g = UpqT.mat h) : g = h :=
  Subtype.ext (Units.ext e)
end Chart
end HcInf
end
end

set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (g : UpqT P Q) (X : lieU P Q)
    (h : UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) = (1 + 1) + ((X : lieU P Q) : Mat)) :
    cayF P Q X = g := by
  have hX := mem_cayley_domain_of g X h
  have hB : IsUnit ((1 + 1) - ((X : lieU P Q) : Mat)).det := hX
  have he := (cayF_spec X hX).trans h.symm
  apply upqT_eq_of_mat_eq
  calc UpqT.mat (cayF P Q X)
      = UpqT.mat (cayF P Q X) * ((1 + 1) - ((X : lieU P Q) : Mat)) *
          ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
    _ = UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Mat)) * ((1 + 1) - ((X : lieU P Q) : Mat))⁻¹ := by
        rw [he]
    _ = UpqT.mat g := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
end HcInf
