-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.exists_pull_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:28.327077+00:00
-- url     : https://prove2.me/submissions/e04331ca-3e1b-4cda-9b84-657a500af229

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec


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
theorem _root_.solution (hL : L.IsLB) {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (e : FormEq (fun k => h ≫ φ k) ε φ' ε') : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s', hs'⟩ := exists_sec hL e (pullSec L φ ε s h)
  exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ)⟩
end GlobalTheory.IndivisibleSection
