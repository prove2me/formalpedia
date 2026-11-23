-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.sval_of_secIsMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:58.261083+00:00
-- url     : https://prove2.me/submissions/c8d62107-542e-4245-88c1-03e144fb94ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_gs_scal

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndivisibleSection
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {p : Y ⟶ Sp R} {a : R}
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : SecIsMul p a s t) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval s r z J = cst (r ≫ p) z a * sval t r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [h (fun k => J (r ≫ φ k))]
  exact (gs_mul _ _ _ hm _ _).trans (congrArg (· * _) (gs_scal p r z _ hm _))
end GlobalTheory.IndivisibleSection
