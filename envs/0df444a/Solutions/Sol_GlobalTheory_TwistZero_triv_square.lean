-- Prove2me | solution 1 for GlobalTheory.TwistZero.triv_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:32.844124+00:00
-- url     : https://prove2.me/submissions/6b55fd12-d0ec-4747-99bf-c35d737e6bb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_GlobalTheory_TwistZero_Triv_congr
import Theorems.Thm_GlobalTheory_TwistZero_triv_of_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_exists_sec_of_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_spec_pt_eq


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero
variable {k : Type} [Field k]
namespace GlobalTheory.TwistZero
theorem _root_.solution (hsq : SquareSt) (P : PolAV (Sp k)) (x₁ x₂ : baseOver (Sp k) ⟶ P.A) :
    Triv P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Sp k)) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Sp k) P (baseOver (Sp k)) x₁ x₂ (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Sp k) ⊗ P.A).left)
    ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Sp k)) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine Triv.congr P.isLB ?_ (triv_of_sec P.isLB (pullSec s e) fun y J hJ => ?_)
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ
end GlobalTheory.TwistZero
