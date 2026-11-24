-- Prove2me | solution 1 for GlobalTheory.CuspCentre.zMatE_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:21:58.51439+00:00
-- url     : https://prove2.me/submissions/afc192ca-cd5e-4301-a8cc-0431ff960e46

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
import Theorems.Thm_P2M_GlobalTheory_CuspCentre_cc_cc__0ed1f9e3c908
import Theorems.Thm_GlobalTheory_CuspCentre_herm_comb_r
import Theorems.Thm_GlobalTheory_CuspCentre_herm_nondeg
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
theorem _root_.solution (X : Data E r) (cu : FJ.CuspFD X ρ) :
    Function.Injective (FJ.zMatE X cu.e) := by
  intro β β' h
  have h1 : ∀ v a, ∑ b, β a b * herm X.Gm v (cu.e b) = ∑ b, β' a b * herm X.Gm v (cu.e b) := by
    intro v a
    have h2 := congrArg (· *ᵥ v) h
    simp only [zMatE_mulVec, add_right_inj] at h2
    exact Fintype.linearIndependent_iffₛ.1 cu.ind _ _ h2 a
  ext a b
  have h3 : ∑ b, cc (β a b - β' a b) • cu.e b = 0 := by
    refine herm_nondeg X _ fun v => ?_
    simp only [herm_comb_r, cc_cc', sub_mul, Finset.sum_sub_distrib, h1 v a, sub_self]
  have h4 : cc (β a b - β' a b) = 0 := Fintype.linearIndependent_iff.1 cu.ind _ h3 b
  rw [← sub_eq_zero, ← cc_cc' (β a b - β' a b), h4, cc_zero']
end GlobalTheory.CuspCentre
