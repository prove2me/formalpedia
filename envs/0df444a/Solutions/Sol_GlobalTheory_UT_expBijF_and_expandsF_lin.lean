-- Prove2me | solution 1 for GlobalTheory.UT.expBijF_and_expandsF_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:56.974306+00:00
-- url     : https://prove2.me/submissions/f0618a96-c82a-4681-be73-c343615c9fd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpBijFAndExpandsFLin
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsF_lin
import Theorems.Thm_GlobalTheory_expansion_bijective_over_fields
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
open GlobalTheory GlobalTheory.UT
namespace GlobalTheory.UT
theorem _root_.solution : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w₀ : W0 U.toUnifPre) (t t' t'' : SecA A F k) (s s' : Fam D.toPre F k) (c : F), U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀ t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → U.ExpandsF F k w₀ t'' (c • s + s') := by
  intro hL R _ _ _ I _ D A G _ _ _ U
  refine ⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩
  intro F _ _ k w₀ t t' t'' s s' c h h' e
  have key := GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'
  have ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b := by
    rintro ⟨a, _⟩ ⟨b, _⟩ hab
    obtain rfl : a = b := funext hab
    rfl
  exact (congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key
end GlobalTheory.UT
