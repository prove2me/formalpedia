-- Prove2me | solution 1 for GlobalTheory.CuspCentre.zMatE_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:23.389213+00:00
-- url     : https://prove2.me/submissions/713cb217-9762-45e1-bdfd-010f5807f2a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Theorems.Thm_P2M_GlobalTheory_CuspCentre_cc_mul__aa1f1980283c
import Theorems.Thm_P2M_GlobalTheory_CuspCentre_cc_sum__4ddf663c3fbe
import Theorems.Thm_GlobalTheory_CuspCentre_herm_add_r
import Theorems.Thm_GlobalTheory_CuspCentre_herm_comb_r
import Theorems.Thm_GlobalTheory_CuspCentre_herm_swap
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspCentre
theorem _root_.solution (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) (u v : Fin r → E) :
    herm X.Gm (FJ.zMatE X cu.e β *ᵥ u) (FJ.zMatE X cu.e β *ᵥ v) = herm X.Gm u v := by
  simp only [zMatE_mulVec, herm_add_l, herm_add_r, herm_comb_l, herm_comb_r, cu.iso, mul_zero,
    Finset.sum_const_zero, add_zero, cc_sum', cc_mul', hβ _ _, ← herm_swap, Finset.sum_mul]
  rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  ring
end GlobalTheory.CuspCentre
