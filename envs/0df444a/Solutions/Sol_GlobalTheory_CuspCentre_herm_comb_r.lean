-- Prove2me | solution 1 for GlobalTheory.CuspCentre.herm_comb_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:04:48.7633+00:00
-- url     : https://prove2.me/submissions/85b2ad61-733c-4494-a708-bb05e7152ccd

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
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (x : Fin r → E) : herm G x (∑ a, c a • e a) = ∑ a, cc (c a) * herm G x (e a) := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cc_sum', cc_mul', Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end GlobalTheory.CuspCentre
