-- Prove2me | solution 1 for HcInf.cayley_inverse_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:55.832586+00:00
-- url     : https://prove2.me/submissions/0951b545-525e-46d7-9268-7c0d5c2aa665

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayleyInverseMeasurable
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
theorem _root_.solution : CayInvMeas := by
  intro P Q
  set O : Set (UpqT P Q) := {g | (UpqT.mat g + 1).det ≠ 0}
  have hmat : Continuous (UpqT.mat (P := P) (Q := Q)) := (isInducing_mat P Q).continuous
  have hdet : Continuous fun g : UpqT P Q => (UpqT.mat g + 1).det :=
    (hmat.add continuous_const).matrix_det
  have hO : IsOpen O := isOpen_ne_fun hdet continuous_const
  have hcand : Continuous fun g : O => cayCand P Q g := by
    have hm : Continuous fun g : O => UpqT.mat (g : UpqT P Q) := hmat.comp continuous_subtype_val
    have hd : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1).det :=
      hdet.comp continuous_subtype_val
    have hinv : Continuous fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹ := by
      have e : (fun g : O => (UpqT.mat (g : UpqT P Q) + 1)⁻¹) =
          fun g : O => ((UpqT.mat (g : UpqT P Q) + 1).det)⁻¹ • (UpqT.mat (g : UpqT P Q) + 1).adjugate := by
        funext g
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e]
      exact (hd.inv₀ fun g => g.2).smul (hm.add continuous_const).matrix_adjugate
    exact (continuous_const.matrix_mul hinv).matrix_mul (hm.sub continuous_const)
  have hcont : ContinuousOn (cayInv P Q) O := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    show Continuous fun g : O => cayInv P Q g
    have e : (fun g : O => cayInv P Q g) = fun g : O => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
      funext g
      exact cayInv_eq P Q g
    rw [e]
    exact Continuous.subtype_mk hcand _
  have hpw : O.piecewise (cayInv P Q) (fun _ => 0) = cayInv P Q := by
    funext g
    by_cases hg : g ∈ O
    · exact Set.piecewise_eq_of_mem _ _ _ hg
    · rw [Set.piecewise_eq_of_notMem _ _ _ hg]
      have hg' : ¬IsUnit (UpqT.mat g + 1).det := fun hu => hg hu.ne_zero
      rw [cayInv_eq]
      apply Subtype.ext
      show 0 = (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hg', Matrix.mul_zero, Matrix.zero_mul]
  rw [← hpw]
  classical
  exact hcont.measurable_piecewise continuousOn_const hO.measurableSet
end HcInf
