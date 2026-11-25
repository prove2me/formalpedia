-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.twoCharts_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:33.989168+00:00
-- url     : https://prove2.me/submissions/1444b2d7-d01a-4614-8e5c-1a1b7969af0e

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
import Theorems.Thm_GlobalTheory_WeilNoncomm_gm_sgn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {X Y : Scheme.{0}} (φ : Y ⟶ X) : LBIso (twoCharts Y) ((oneChart X).pull φ) := by
  refine ⟨⟨fun p => sgn _ p.2⟩, (isGen_iff _).2 fun Z f z j j' (k k' : Bool) hj hj' hk hk' => ?_⟩
  have v : ∀ (j : PUnit) (k : Bool), gw (L := oneChart X) (L' := twoCharts Y) (F := φ)
      ⟨fun p => sgn _ p.2⟩ f z j k = sgn _ k := fun j k =>
    gm_sgn f z (((oneChart X).pull φ).U (fun _ => j) ⊓ ⊤) ⟨mem_pull.2 trivial, trivial⟩ k
  have g : gm f z ((twoCharts Y).U k ⊓ (twoCharts Y).U k') ((twoCharts Y).g k k') = sgn _ (xor k k') :=
    gm_sgn f z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ _
  have o : gm (f ≫ φ) z ((oneChart X).U j ⊓ (oneChart X).U j') ((oneChart X).g j j') = 1 := map_one _
  refine (v j k).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹) o g) (v j' k')).symm)
  cases k <;> cases k' <;> simp [sgn]
end GlobalTheory.WeilNoncomm
