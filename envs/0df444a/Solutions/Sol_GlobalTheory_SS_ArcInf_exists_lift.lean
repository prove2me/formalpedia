-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:19.541593+00:00
-- url     : https://prove2.me/submissions/ba199510-e5ee-4fb9-a606-bdf3131ffb2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
variable {k : Type} [Field k]
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution {F : Type} [CommRing F] [Algebra k F] (ρ : PowerSeries k →ₐ[k] F)
    (h : IsUnit (ρ PowerSeries.X)) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] F, ∀ x, σ (algebraMap (PowerSeries k) _ x) = ρ x := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    have h0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    obtain ⟨u, hu⟩ := hn.symm
    show IsUnit (ρ y)
    rw [← hu, map_mul, map_pow]
    exact (h.pow n).mul (u.isUnit.map ρ)
  exact ⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩
end GlobalTheory.SS.ArcInf
