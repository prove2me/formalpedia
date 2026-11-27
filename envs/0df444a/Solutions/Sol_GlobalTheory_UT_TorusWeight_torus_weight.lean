-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.torus_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:09.248656+00:00
-- url     : https://prove2.me/submissions/5d7021f1-f958-4188-a276-f49dc1e45ec5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_GlobalTheory_UT_TorusWeight_txFrame_of_one
import Theorems.Thm_GlobalTheory_UT_TorusWeight_phiRel_tor
import Theorems.Thm_GlobalTheory_UT_CoefBasic_coef_basic
import Theorems.Thm_GlobalTheory_UT_SymFrame_main
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ, p.y = 0 → IsTor τ p.g → ∀ w, TXFrame N p w → FrmOne w ∧ ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N p w s s' ↔ ∀ α j, (s'.s α).f j = DegPre.constBF D.toPre F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  intro hL R _ _ _ I hI D A G _ _ _ U F _ _ _ N hN p τ hy hτ w hw
  obtain ⟨w₀, hw₀⟩ := (CoefBasic.coef_basic R D.toPre F N p.g).2.1 hτ.1
  have h₁ : FrmOne w := ⟨hw.1, fun z J hJ =>
    ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p).2 w w₀ hw (txFrame_of_one D.tau_bimult p hy hτ hw₀) z J hJ).trans (hw₀.2 z J hJ)⟩
  exact ⟨h₁, phiRel_tor hL.1.globalFns p hy hτ h₁⟩
end GlobalTheory.UT.TorusWeight
