-- Prove2me | solution 1 for GlobalTheory.detCond_iff_of_sabMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:44.831442+00:00
-- url     : https://prove2.me/submissions/7ddfe96e-b010-49cd-b9bb-9c7463d145f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Theorems.Thm_GlobalTheory_lieMult_iff_of_isGrpPullback

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), Nonempty (SABMap t' t f) →
    ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (ρ : k), DetCond D t'.act x ρ ↔ DetCond D t.act (x ≫ f) ρ := by
  rintro E _ _ _ H D S S' t t' f ⟨m⟩ k _ x ρ
  refine forall_congr' fun τ => ?_
  rw [lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.p,
    lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.q]
end GlobalTheory
