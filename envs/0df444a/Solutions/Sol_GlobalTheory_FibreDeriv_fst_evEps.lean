-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.fst_evEps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:54.334624+00:00
-- url     : https://prove2.me/submissions/73bab669-288c-4e08-bad5-4c3364055b68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution (v : Sp (DualNumber ℂ) ⟶ X) (x : Sp ℂ ⟶ X)
    (hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    (evEps v U h f).fst = valAt' x U f := by
  subst hx
  rw [← valAt'_appLE _ v U ⊤ h f le_top, valAt'_eq_valAt _ le_top]
  have := congrArg (fun k => k.hom ((v.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this.symm
end GlobalTheory.FibreDeriv
