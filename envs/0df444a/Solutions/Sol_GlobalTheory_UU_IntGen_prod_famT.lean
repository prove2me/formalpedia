-- Prove2me | solution 1 for GlobalTheory.UU.IntGen.prod_famT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:34:12.965958+00:00
-- url     : https://prove2.me/submissions/77de3001-2b7a-471b-ac82-a95fd6c3038c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.IntGen
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.UU.IntGen
theorem _root_.solution {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd T D.P.A) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl
end GlobalTheory.UU.IntGen
