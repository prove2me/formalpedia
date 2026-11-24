-- Prove2me | solution 1 for GlobalTheory.TwistZero.mem_nonzeroLocus_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:27.094878+00:00
-- url     : https://prove2.me/submissions/062e0b24-490b-4525-97ee-2ae0ce2958e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval


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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TwistZero
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    r z ∈ nonzeroLocus s ↔ IsUnit (sval s r z J) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact isUnit_sval s r z hJ k hk
  · intro h
    have hm := hJ.mem φ r
    have hu := (congrArg IsUnit (gs_eq r z _ hm (s.f (fun k => J (r ≫ φ k))))).mp h
    have hz := (Z.mem_basicOpen _ z hm).2 hu
    exact Opens.mem_iSup.2 ⟨fun k => J (r ≫ φ k),
      (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r (s.f (fun k => J (r ≫ φ k)))) z).2 hz⟩
end GlobalTheory.TwistZero
