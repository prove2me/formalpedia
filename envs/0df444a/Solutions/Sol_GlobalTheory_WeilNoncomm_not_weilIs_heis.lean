-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.not_weilIs_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:17.2455+00:00
-- url     : https://prove2.me/submissions/7d558fc9-64e6-4a14-a7d0-aa42032dfb53

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
import Theorems.Thm_GlobalTheory_WeilNoncomm_not_commIsOf_twoCharts
import Theorems.Thm_GlobalTheory_WeilNoncomm_heisPt_comp_mk
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
theorem _root_.solution {S : Scheme.{0}} (T : Over S) (p : T.left) (h2 : IsUnit (2 : Γ(T.left, ⊤)))
    (c : Γ(T.left, ⊤)ˣ) :
    ¬ WeilIs (heisScheme S) (twoCharts _) 1 (heisMk T 1 0 0) (heisMk T 0 1 0) c := by
  intro H
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := H p
  have ex : heisPt _ θx.pt = ⟨1, 0, 0⟩ := by rw [hx, heisPt_comp_mk, map_one, map_zero]
  have ey : heisPt _ θy.pt = ⟨0, 1, 0⟩ := by rw [hy, heisPt_comp_mk, map_one, map_zero]
  have nt : (1 : Γ((overRes V).left, ⊤)) ≠ 0 := by
    let z : (overRes V).left := (⟨p, hV⟩ : V.toScheme)
    exact fun e => one_ne_zero ((map_one _).symm.trans ((congrArg ((overRes V).left.presheaf.germ ⊤ z trivial).hom e).trans
      (map_zero _)))
  have u2 := h2.map (overResι V).left.appTop.hom
  rw [map_ofNat] at u2
  refine not_commIsOf_twoCharts _ θx θy _ (⟨p, hV⟩ : V.toScheme) u2 ?_ ?_ ?_ ?_ (H θx θy hx hy) <;> intro e <;>
    have e' := congrArg (heisPt _) e <;>
    simp [map_mul, ex, ey, Heis.mul_def, Heis.one_def, nt, nt.symm] at e'
end GlobalTheory.WeilNoncomm
