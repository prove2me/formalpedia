-- Prove2me | solution 1 for GlobalTheory.cubeRel_scalars_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:06.089655+00:00
-- url     : https://prove2.me/submissions/894cad85-b11a-4057-a9be-93f23d2ca77e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvenQuadraticPosOfFiniteNonpos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubeRelScalarsMemMaximalIdeal
import Theorems.Thm_GlobalTheory_exists_dvr_fraction_order
import Theorems.Thm_GlobalTheory_even_quadratic_pos_of_finite_nonpos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx
end GlobalTheory
