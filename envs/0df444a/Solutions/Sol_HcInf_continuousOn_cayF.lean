-- Prove2me | solution 1 for HcInf.continuousOn_cayF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:34.822005+00:00
-- url     : https://prove2.me/submissions/09938af4-4f20-4b9e-8753-d352f4506556

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Theorems.Thm_HcInf_cayF_mat
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
private theorem continuous_inv_of_det_ne_zero {α : Type*} [TopologicalSpace α] {f : α → Mat}
    (hf : Continuous f) (hd : ∀ x, (f x).det ≠ 0) : Continuous fun x => (f x)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate
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
theorem _root_.solution : ContinuousOn (cayF P Q) (D0 P Q) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : Continuous fun x : D0 P Q => UpqT.mat (cayF P Q x) := by
    have h : (fun x : D0 P Q => UpqT.mat (cayF P Q x)) = fun x : D0 P Q =>
        ((1 + 1) + ((x.1 : lieU P Q) : Mat)) * ((1 + 1) - ((x.1 : lieU P Q) : Mat))⁻¹ :=
      funext fun x => cayF_mat x.1 x.2
    rw [h]
    exact (continuous_const.add (continuous_subtype_val.comp continuous_subtype_val)).mul
      (continuous_inv_of_det_ne_zero (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val))
        fun x => isUnit_iff_ne_zero.1 x.2)
  have hinv : Continuous fun x : D0 P Q => (UpqT.mat (cayF P Q x))⁻¹ :=
    continuous_inv_of_det_ne_zero hval fun x => (Matrix.isUnits_det_units _).ne_zero
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hval, ?_⟩) _
  refine hinv.congr fun x => ?_
  exact (Matrix.coe_units_inv _).symm
end HcInf
