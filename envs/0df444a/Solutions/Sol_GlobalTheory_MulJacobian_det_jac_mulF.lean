-- Prove2me | solution 1 for GlobalTheory.MulJacobian.det_jac_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:58:48.815674+00:00
-- url     : https://prove2.me/submissions/af375ea7-5362-460a-ab88-e1d519ea313e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
import Theorems.Thm_GlobalTheory_MulJacobian_mulF_eq_mulN
import Theorems.Thm_GlobalTheory_MulJacobian_const_invMat
import Theorems.Thm_GlobalTheory_MulJacobian_isUnit_det_of_const
import Theorems.Thm_GlobalTheory_MulJacobian_jac_mul_invMat
import Theorems.Thm_GlobalTheory_FormalMulN_const_mulN
import Theorems.Thm_GlobalTheory_GaugeAdjoint_constantCoeff_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open GlobalTheory GlobalTheory.MulJacobian
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.MulJacobian
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ),
    ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv R ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  intro R _ d G N
  have hφ : GP (mulN G N) := GlobalTheory.FormalMulN.const_mulN G N
  obtain ⟨a, ha⟩ := isUnit_det_of_const (invMat G) (const_invMat G)
  obtain ⟨b, hb⟩ := isUnit_det_of_const
    (Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l)) (fun i l => by
      rw [Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev (single_point_zero_constant hφ), const_invMat])
  have h := congrArg Matrix.det (jac_mul_invMat G N)
  rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, ← ha, ← hb] at h
  refine ⟨b * a⁻¹, ?_⟩
  rw [mulF_eq_mulN, Units.val_mul, ← mul_assoc, ← h, Units.mul_inv_cancel_right]
end GlobalTheory.MulJacobian
