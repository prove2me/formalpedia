-- Prove2me | solution 1 for GlobalTheory.weilIs_unique_fieldPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:34.836414+00:00
-- url     : https://prove2.me/submissions/e6109b12-d585-4958-b17b-2fec1dc3da40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Theorems.Thm_GlobalTheory_unitRes_top_injective
import Theorems.Thm_GlobalTheory_unitOn_injective_of_commRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_commIsOf_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (n : ℤ) (x y : Over.mk t ⟶ G) (c c' : kˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x y (unitOn c') → c = c' := by
  intro S G _ L hL k _ t n x y c c' h h'
  let p : (Over.mk t).left := (⊥ : PrimeSpectrum k)
  have top : ∀ V : (Over.mk t).left.Opens, p ∈ V → V = ⊤ := fun V hV =>
    eq_top_iff.2 fun q _ => by
      have : q = p := Subsingleton.elim (α := PrimeSpectrum k) q p
      exact this ▸ hV
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := top V hV
  obtain rfl := top V' hV'
  exact unitOn_injective_of_commRing (unitRes_top_injective
    (H1.commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)))
end GlobalTheory
