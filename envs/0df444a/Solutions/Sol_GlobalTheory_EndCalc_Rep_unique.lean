-- Prove2me | solution 1 for GlobalTheory.EndCalc.Rep.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:17.658117+00:00
-- url     : https://prove2.me/submissions/c161539b-1d03-4d39-bfe0-cada0a57d7e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
open FreeAbelianGroup
variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.EndCalc
namespace Rep
theorem _root_.solution {s s' : FreeAbelianGroup (T₀ ⟶ D.P.A)} {v v' : Vals D T₀} (h : Rep s v) (h' : Rep s' v')
    (hs : Function.Surjective T₀.hom.appTop.hom) (e : 𝟙_ _ ⟶ T₀) (hF : s = s')
    (h₀ : ∀ y J, Good D.P.L y J → v _ e y J = v' _ e y J) {T} (ρ : T ⟶ T₀) {z J} (hJ : Good D.P.L z J) :
    v T ρ z J = v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', c'⟩ := h'
  subst hF
  exact (c T ρ z J hJ).symm.trans ((gen_unique' D.P.isLB (fun U _ h => (f' U h).trans (f U h).symm) T₀.hom e.left
    (Over.w e) hs ht ht' (fun y I hI => (c _ e y I hI).trans ((h₀ y I hI).trans (c' _ e y I hI).symm))
    _ ρ.left z J hJ).trans (c' T ρ z J hJ))
end Rep
end GlobalTheory.EndCalc
