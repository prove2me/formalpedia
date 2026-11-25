-- Prove2me | solution 1 for GlobalTheory.T.integralFamily_prescribedTerm_unit_at_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:26.852388+00:00
-- url     : https://prove2.me/submissions/cae05263-b4d7-49ea-9bf7-86d84cc13a1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Theorems.Thm_GlobalTheory_integralFamily_at_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) → ∀ p : (Spec (CommRingCat.of R)), p ∈ W → ∀ (k : ℕ), 1 ≤ k → ∀ (ρ : D.toPre.X) (s : D.toPre.SecB k ρ), ∃ r : R, r ∉ p.asIdeal ∧ ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ j, (f ρ).f j = resTop _ (scal D.toPre.P.A.hom r) * (s).f j) ∧ ∀ β, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (f β).f j = 0 := by
  first | exact @GlobalTheory.integralFamily_at_prime | exact GlobalTheory.integralFamily_at_prime | (intros; apply GlobalTheory.integralFamily_at_prime <;> assumption)
end _root_.GlobalTheory.T
