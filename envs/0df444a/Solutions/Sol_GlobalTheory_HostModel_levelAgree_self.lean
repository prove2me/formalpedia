-- Prove2me | solution 1 for GlobalTheory.HostModel.levelAgree_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:21.331502+00:00
-- url     : https://prove2.me/submissions/5278f9cd-85be-4197-bf60-53c0d3d2c23c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_HostModel_equiv_refl_witP
import Theorems.Thm_GlobalTheory_HostModel_eq_of_genRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
namespace GlobalTheory.HostModel
theorem _root_.solution (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) :
    LevelAgree (arcIn c k bF) (witP c k bF) (witIso c k bF) (witIso c k bF) e e := by
  intro F _ _ _ _ u hF _ n _ _ q₀ q₁ q₂ _ hy₁ hy₂ h₁ h₂
  rw [eq_of_genRel c k bF F hF e _ q₀ q₁ q₂ (hy₁.trans hy₂.symm) h₁ h₂]
  exact equiv_refl_witP c k bF F q₂
end GlobalTheory.HostModel
