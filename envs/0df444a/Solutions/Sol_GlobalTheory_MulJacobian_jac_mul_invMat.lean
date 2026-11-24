-- Prove2me | solution 1 for GlobalTheory.MulJacobian.jac_mul_invMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:41:32.758177+00:00
-- url     : https://prove2.me/submissions/0c114d7b-0a16-4227-ba55-0d7efc69a5b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
import Theorems.Thm_GlobalTheory_MulJacobian_dof_single
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalMulN_mulN_hom
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_pt
import Theorems.Thm_GlobalTheory_HomChain_dof_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open GlobalTheory GlobalTheory.MulJacobian
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.MulJacobian
theorem _root_.solution (G : FGLaw R d) (N : ℕ) :
    (Matrix.of fun i j : Fin d => pderiv R ((0 : Fin 1), j) (mulN G N i)) * invMat G =
      (N : PS R 1 d) • Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.FormalMulN.mulN_hom R d G N
  have hφ : GP (mulN G N) := h0
  ext1 i l
  have h := GlobalTheory.HomChain.dof_hom G G (mulN G N) h0 h1 (Pi.single l 1) (pt R d 0 i)
  have e1 : (dLin (mulN G N)).mulVec (Pi.single l 1) = Pi.single l (N : R) := by
    rw [h2, Matrix.smul_mulVec, Matrix.one_mulVec, ← Pi.single_smul, smul_eq_mul, mul_one]
  have e2 : ev (n := 1) ![mulN G N] (pt R d 0 i) = mulN G N i :=
    GlobalTheory.GaugeAdjoint.ev_pt (single_point_zero_constant hφ) 0 i
  have e3 : ∑ j, pderiv R ((0 : Fin 1), j) (pt R (n := 1) d 0 i) * invMat G j l = invMat G i l := by
    rw [Finset.sum_eq_single i]
    · simp [pt]
    · intro j _ hj
      rw [pt, pderiv_X_of_ne (by simpa using hj.symm), zero_mul]
    · simp
  rw [e1, e2, dof_single, dof_single, e3, GlobalTheory.ChartTrans.ev_C_mul _ (single_point_zero_constant hφ), map_one, one_mul,
    map_natCast] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  exact h
end GlobalTheory.MulJacobian
