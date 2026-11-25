-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dof_dy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:49.225794+00:00
-- url     : https://prove2.me/submissions/38b29643-bdeb-4f51-a468-ee51fdb8ea7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_dof_almost_additive
import Theorems.Thm_GlobalTheory_GaugeInt_dz_defL
import Theorems.Thm_GlobalTheory_GaugeInt_int_C
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_addOf_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_const_pderiv_pderiv
import Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_pderiv_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_formalComp_zero_left_point
import Theorems.Thm_GlobalTheory_QuadDeriv_formalSubst_single_of_formalSubst_two
import Theorems.Thm_GlobalTheory_QuadDeriv_pderiv_pt_self
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt


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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hl : DI φ (defL F g)) {u v : Fin d → k} (hu : ∀ i, u i ∈ φ.range)
    (hv : ∀ i, v i ∈ φ.range) (hβ : dotProduct u ((bilinPart k g).mulVec v) ∈ φ.range) :
    Dof F u (dy v g) ∈ IntS φ 1 d := by
  have hF := iF.gp
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) -
      C (Matrix.vecMul u (bilinPart k g) j) ∈ IntS φ 1 d := by
    intro j
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
        formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1]
      have := dz_defL iF g hl (ip_pt 0) (ip_pt 1) j
      rwa [addOf_pt] at this)
    convert h using 3
    simp only [Matrix.vecMul, dotProduct, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
    simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite, bilinPart]
  rw [Matrix.dotProduct_mulVec, dotProduct_comm] at hβ
  have h := add_mem (sum_mem (t := Finset.univ) fun j _ => mul_mem (int_C (hv j)) (hb j))
    (int_C (n := 1) (d := d) hβ)
  convert h using 1
  rw [dy, GE.dof_sum]
  simp only [GE.dof_C_mul, mul_sub, Finset.sum_sub_distrib, ← map_mul, ← map_sum, dotProduct]
  ring
end GlobalTheory.GaugeDiv
