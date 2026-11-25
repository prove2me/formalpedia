-- Prove2me | solution 1 for GlobalTheory.DescTheta.evalAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:02:35.968903+00:00
-- url     : https://prove2.me/submissions/ecebe7be-13f1-4d7f-ad52-03a25214a62a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_DescTheta_mem_basicOpen_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
namespace GlobalTheory.DescTheta
theorem _root_.solution {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U)
    (a : Γ(X, U)) (z : Sp k) : evalAt ζ U h a ≠ 0 ↔ ζ z ∈ X.basicOpen a := by
  have e := mem_basicOpen_appLE ζ h a z
  rw [basicOpen_eq_of_affine'] at e
  have hz : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime k _ z.asIdeal z.isPrime
  have e2 : z ∈ PrimeSpectrum.basicOpen (evalAt ζ U h a) ↔ evalAt ζ U h a ≠ 0 := by
    change evalAt ζ U h a ∉ z.asIdeal ↔ _
    rw [hz, Ideal.mem_bot]
  rw [← e2]
  exact e.trans (and_iff_right trivial)
end GlobalTheory.DescTheta
