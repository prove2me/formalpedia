-- Prove2me | solution 1 for HcInf.continuousOn_cayInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:49.572625+00:00
-- url     : https://prove2.me/submissions/b89abf8b-f56a-4c56-a494-eb4a64a4acbe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PreimageSubsetImage
import Theorems.Thm_HcInf_continuous_mat


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
theorem _root_.solution : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
    funext g
    first
    | (unfold cayInv; rw [dif_pos (cayCand_mem P Q g)])
    | simp [cayInv, cayCand_mem]
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hg' : ∃ X ∈ D0 P Q, g.mat * (1 + 1 - (X : Mat)) = 1 + 1 + (X : Mat) := hg
  obtain ⟨X, -, hgX⟩ := hg'
  have h4 : (g.mat + 1) * (1 + 1 - (X : Mat)) = (4 : ℂ) • (1 : Mat) := by
    rw [add_mul, hgX, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
      one_smul]
    abel
  have hdet : IsUnit (g.mat + 1).det := by
    have h5 := congrArg Matrix.det h4
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h5
    have h' : IsUnit ((g.mat + 1).det * (1 + 1 - (X : Mat)).det) := by
      rw [h5]
      exact (Ne.isUnit (by norm_num : (4 : ℂ) ≠ 0)).pow _
    exact isUnit_of_mul_isUnit_left h'
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    refine (continuousAt_matrix_inv _ ?_).comp (hc.add continuousAt_const)
    obtain ⟨u, hu⟩ := hdet
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt
end HcInf
