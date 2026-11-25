-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.not_commIsOf_twoCharts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:39.428797+00:00
-- url     : https://prove2.me/submissions/618ed8ad-af53-4852-ad41-6db4f2c95539

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
import Theorems.Thm_GlobalTheory_WeilNoncomm_loc_comm
import Theorems.Thm_GlobalTheory_WeilNoncomm_loc_twoCharts
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
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {T : Over S} (θx θy : ThetaGrp G (twoCharts G.left) 1 T) (c : Γ(T.left, ⊤)ˣ)
    (z : T.left) (h2 : IsUnit (2 : Γ(T.left, ⊤))) (h₁ : θy.pt * θx.pt ≠ 1) (hx : θy.pt * θx.pt ≠ θx.pt)
    (hy : θy.pt * θx.pt ≠ θy.pt) (hxy : θy.pt * θx.pt ≠ θx.pt * θy.pt) : ¬ CommIsOf G (twoCharts G.left) 1 θx θy c := by
  intro H
  obtain ⟨J, hJ, hJ'⟩ : ∃ J : (T.left ⟶ G.left) → Bool, J (θy.pt * θx.pt).left = true ∧
      ∀ {a : T ⟶ G}, θy.pt * θx.pt ≠ a → J a.left = false := by
    classical
    exact ⟨fun ψ => decide (ψ = (θy.pt * θx.pt).left), decide_eq_true rfl, fun h => decide_eq_false fun e =>
      h (Over.OverMorphism.ext e.symm)⟩
  have k₁ := loc_comm G z H (fun _ => false) (fun _ => trivial)
  have k₂ := loc_comm G z H J (fun _ => trivial)
  rw [hJ, hJ' h₁, hJ' hx, hJ' hy, hJ' hxy, loc_twoCharts] at k₂
  have k₃ : -loc G z θy θx.pt false false = loc G z θy θx.pt false false := mul_left_cancel (k₂.trans k₁.symm)
  have k₅ : (-1 : (T.left.presheaf.stalk z)ˣ) = 1 := mul_eq_right.1 ((neg_one_mul _).trans k₃)
  have k₇ : (-1 : T.left.presheaf.stalk z) = 1 := congrArg Units.val k₅
  have k₈ := h2.map (T.left.presheaf.germ ⊤ z trivial).hom
  rw [map_ofNat, show (2 : T.left.presheaf.stalk z) = 0 by linear_combination -k₇] at k₈
  exact not_isUnit_zero k₈
end GlobalTheory.WeilNoncomm
