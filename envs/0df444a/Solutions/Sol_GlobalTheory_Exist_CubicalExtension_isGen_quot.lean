-- Prove2me | solution 1 for GlobalTheory.Exist.CubicalExtension.isGen_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:10.681318+00:00
-- url     : https://prove2.me/submissions/094b5121-6541-4def-b877-6124deeaab9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_mem_qchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div_g
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.CubicalExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace GlobalTheory.Exist.CubicalExtension
theorem _root_.solution {j : A ⟶ X'} (s : ∀ a i, Γ(A, qchart L L' F j a i)ˣ)
    (h : ∀ (y : A) a a' i i', F (j y) ∈ L.U a → F (j y) ∈ L.U a' → j y ∈ L'.U i → j y ∈ L'.U i' →
      gm (𝟙 A) y _ (s a i) = gm (j ≫ F) y _ (L.g a a') * (gm j y _ (L'.g i i'))⁻¹ * gm (𝟙 A) y _ (s a' i')) :
    LB.Gen.IsGen (L := (LB.div (L.pull F) L').pull j) ⟨fun J => s ((J PUnit.unit).1 PUnit.unit) (J PUnit.unit).2⟩ := by
  refine isGen_of_gm _ fun y J J' hJ hJ' => ?_
  have h₁ := (mem_qchart (a := (J PUnit.unit).1 PUnit.unit) (i := (J PUnit.unit).2)).1 hJ
  have h₂ := (mem_qchart (a := (J' PUnit.unit).1 PUnit.unit) (i := (J' PUnit.unit).2)).1 hJ'
  refine (h y _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  exact (gm_div_g j y _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2).symm
end GlobalTheory.Exist.CubicalExtension
