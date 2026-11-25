-- Prove2me | solution 1 for GlobalTheory.nabValN_boxSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:56:18.408713+00:00
-- url     : https://prove2.me/submissions/dbd9b8f3-989b-4e77-9531-72e877b10697

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_rename_eq
import Theorems.Thm_GlobalTheory_NabCol_inColHom_apply
import Theorems.Thm_GlobalTheory_NabCol_inCol_C
import Theorems.Thm_GlobalTheory_NabCol_dmonN_prod
import Theorems.Thm_GlobalTheory_NabCol_fo_col
import Theorems.Thm_GlobalTheory_NabCol_cc_inCol
import Theorems.Thm_GlobalTheory_NabCol_sum_support_eq
import Theorems.Thm_GlobalTheory_NabCol_sum_support_rename
import Theorems.Thm_GlobalTheory_NabCol_expS_sum
import Theorems.Thm_GlobalTheory_FormalConnection_invariantDerivations_commute_formal_connection
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory
open NabCol
namespace GlobalTheory
theorem _root_.solution : NabColSt := by
  intro R _ d O _ _ B k _ _ _ h w0 hh q n f Λ Ix _ _ e cp u u' hcp hu P
  have hL0 : constantCoeff (B.hL k h w0) = 0 := by
    refine gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (fun i => ?_) (gp_pt 0))) _ hh
    simp only [FB.actK]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, B.A.const, map_zero]
  have hq0 : constantCoeff ((q : k) • B.hL k h w0) = 0 := by rw [smul_eq_C_mul, map_mul, hL0, mul_zero]
  have hsm : ∀ b : Fin n, (q : k) • ev (n := n) ![pt k d b] (B.hL k h w0) = inCol b ((q : k) • B.hL k h w0) := by
    intro b
    rw [smul_eq_C_mul, smul_eq_C_mul, ← inColHom_apply, map_mul, inColHom_apply, inColHom_apply, inCol_C]
    rfl
  have hprod : boxSer f * FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b] (B.hL k h w0)) =
      ∏ b, inCol b (f b * FB.expS k ((q : k) • B.hL k h w0)) := by
    rw [Finset.smul_sum, Finset.sum_congr rfl fun b _ => hsm b,
      expS_sum _ _ (fun b => by rw [cc_inCol, hq0]), boxSer, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [rename_eq, ← inColHom_apply b (_ * _), map_mul, inColHom_apply, inColHom_apply]
    congr 1
    exact (gt_ev_expS _ (gp b) _ hq0).symm
  unfold nabValN DpolyN
  rw [hprod]
  simp only [map_sum, map_mul, constantCoeff_C]
  rw [sum_support_rename e (fun m => constantCoeff (DmonN (B.FK k) cp u' m
    (∏ b, inCol b (f b * FB.expS k ((q : k) • B.hL k h w0)))))]
  refine Finset.sum_congr rfl fun mo _ => ?_
  congr 1
  rw [dmonN_prod, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [cc_inCol, fo_col (B.FK k) (fun v w g => FormalConnection.invariantDerivations_commute_formal_connection R d O k B v w g) e cp u u' hcp hu]
  unfold FB.nabVal DpolyOf
  simp only [map_sum, map_mul, constantCoeff_C]
  rw [sum_support_eq (fun m => constantCoeff (DmonOf (B.FK k) u m (f b * FB.expS k ((q : k) • B.hL k h w0))))]
  have hb : (MvPolynomial.monomial (colM mo b) 1 : MvPolynomial Λ k) = MvPolynomial.basisMonomials Λ k (colM mo b) := by
    simp
  rw [hb, Module.Basis.constr_basis]
end GlobalTheory
