-- Prove2me | solution 1 for GlobalTheory.TanDeriv.derivAt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:41:34.816412+00:00
-- url     : https://prove2.me/submissions/f33e1722-e609-4dc3-af9e-cf5f3c68fdc8

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuli
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_TanMod_unit_of_smT_zero
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
noncomputable section
open GlobalTheory GlobalTheory.TanDeriv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]
variable [IsCommMonObj G]
namespace GlobalTheory.TanDeriv
theorem _root_.solution {m : ℕ} (b : Fin m → TanSp x0 G) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ G.left)
    (hw : w = (∑ i, a i • b i).pt.left) (U : G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (hv : ∀ i, ⊤ ≤ (show Sp (DualNumber S) ⟶ G.left from (b i).pt.left) ⁻¹ᵁ U) (f : Γ(G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (R := DualNumber S) (b i).pt.left U (hv i) f).snd := by
  subst hw
  have h1 : ⊤ ≤ (show Sp S ⟶ G.left from (1 : Over.mk x0 ⟶ G).left) ⁻¹ᵁ U :=
    (unit_of_smT_zero x0 _ (∑ i, a i • b i).tan) ▸ comp_top_le _ _ U h
  have key := map_sum (derivAt U h1 f) (fun i => a i • b i) Finset.univ
  simp only [map_smul, smul_eq_mul] at key
  exact key
end GlobalTheory.TanDeriv
