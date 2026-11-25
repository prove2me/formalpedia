-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.unit_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:14.529274+00:00
-- url     : https://prove2.me/submissions/e23397db-57b5-4812-824c-6f776baafbbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
attribute [local instance] heisGrp
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {T : Over (Sp (ZMod 3))} [IsIso T.hom] (u : Γ((T ⊗ heisScheme (Sp (ZMod 3))).left, ⊤)ˣ) :
    u = 1 ∨ u = -1 := by
  have : IsIso (snd T (heisScheme (Sp (ZMod 3)))).left :=
    inferInstanceAs (IsIso (pullback.snd T.hom (heisScheme (Sp (ZMod 3))).hom))
  let i : (T ⊗ heisScheme (Sp (ZMod 3))).left ≅ Spec (CommRingCat.of (MvPolynomial (Fin 3) (ZMod 3))) :=
    asIso (snd T (heisScheme (Sp (ZMod 3)))).left ≪≫ AffineSpace.SpecIso (Fin 3) (CommRingCat.of (ZMod 3))
  have : IsIso i.hom.appTop := inferInstanceAs (IsIso (i.hom.app ⊤))
  let e : MvPolynomial (Fin 3) (ZMod 3) ≃+* Γ((T ⊗ heisScheme (Sp (ZMod 3))).left, ⊤) :=
    ((Scheme.ΓSpecIso _).symm ≪≫ asIso i.hom.appTop).commRingCatIsoToRingEquiv
  obtain ⟨r, hr, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 (u.isUnit.map e.symm)
  have h' : u.val = e (MvPolynomial.C r) := by rw [← h, RingEquiv.apply_symm_apply]
  have : r = 1 ∨ r = -1 := by
    have : ∀ r : ZMod 3, r ≠ 0 → r = 1 ∨ r = -1 := by decide
    exact this r hr.ne_zero
  rcases this with rfl | rfl
  · exact Or.inl (Units.ext (by simpa using h'))
  · exact Or.inr (Units.ext (by simpa using h'))
end GlobalTheory.WeilNoncomm
