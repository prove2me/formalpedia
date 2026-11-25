-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.eq_zero_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:54.608836+00:00
-- url     : https://prove2.me/submissions/7692b7d5-b4a7-41d5-b9a0-e43eb3b370f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution [IsIntegral Y] (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (h : sval s (𝟙 Y) y J = 0) (j : K → L.ι) : s.f j = 0 := by
  have inj : ∀ (i : K → L.ι) (w : Y), w ∈ LB.wchart L φ i → gs (𝟙 Y) w (LB.wchart L φ i) (s.f i) = 0 → s.f i = 0 :=
    fun i w hw e => germ_injective_of_isIntegral Y (U := LB.wchart L φ i) w hw
      (((gs_eq (𝟙 Y) w _ hw _).symm.trans e).trans (map_zero _).symm)
  have hm := hJ.mem φ (𝟙 Y)
  have h0 := inj _ y hm h
  by_cases hj : (LB.wchart L φ j : Set Y).Nonempty
  · obtain ⟨w, hw, hw'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen
      (LB.wchart L φ (fun k => J (𝟙 Y ≫ φ k))).isOpen hj ⟨y, hm⟩
    refine inj j w hw ((sec_trans s (𝟙 Y) w hw hw').trans ?_)
    rw [h0]
    exact (congrArg _ ((gs_eq (𝟙 Y) w _ hw' _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))).trans
      (MulZeroClass.mul_zero _)
  · exact fn_ext fun w hw => absurd ⟨w, hw⟩ hj
end GlobalTheory.ThetaScalar
