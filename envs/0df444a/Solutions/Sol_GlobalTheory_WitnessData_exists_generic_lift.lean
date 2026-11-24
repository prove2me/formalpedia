-- Prove2me | solution 1 for GlobalTheory.WitnessData.exists_generic_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:15.023587+00:00
-- url     : https://prove2.me/submissions/4823c074-21d3-4a51-b345-a6eb20105a9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataIsoOfTwoWitnesses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WitnessData
namespace GlobalTheory.WitnessData
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {Wo : (Spec (CommRingCat.of R)).Opens}
    (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) : ∃ g : (TK R).left ⟶ (TW Wo).left, g ≫ Wo.ι = jK R :=
  ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    show jK R y ∈ Wo
    rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩
end GlobalTheory.WitnessData
