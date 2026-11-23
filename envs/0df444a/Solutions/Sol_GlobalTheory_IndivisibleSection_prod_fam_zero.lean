-- Prove2me | solution 1 for GlobalTheory.IndivisibleSection.prod_fam_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:43.768843+00:00
-- url     : https://prove2.me/submissions/58fe6c6c-c90c-43dc-90cd-7d669dca0b09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsGeneratorOfBasis
import Theorems.Thm_GlobalTheory_IndivisibleSection_c_zero_eq_one

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
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.IndivisibleSection
theorem _root_.solution {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (D.famφB 0 k) ^ DegPre.famε 1 k = h (𝟙 _) := by
  unfold DegPre.famφB DegPre.famε
  rw [c_zero_eq_one, Fin.prod_univ_four]
  have e2 : toUnit D.P.A ≫ (1 : 𝟙_ _ ⟶ D.P.A) = toUnit D.P.A ≫ η := by
    change toUnit D.P.A ≫ (toUnit _ ≫ η) = _
    rw [← Category.assoc, toUnit_unique (toUnit D.P.A ≫ toUnit _) (toUnit D.P.A)]
  have e1 : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ 1) = 𝟙 D.P.A := by
    rw [e2]
    exact mul_one (𝟙 D.P.A)
  rw [e1, e2]
  simp
end GlobalTheory.IndivisibleSection
