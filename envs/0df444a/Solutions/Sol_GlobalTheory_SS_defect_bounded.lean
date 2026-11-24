-- Prove2me | solution 1 for GlobalTheory.SS.defect_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:45.746129+00:00
-- url     : https://prove2.me/submissions/ebc48c28-ee88-49ba-803b-d463178a49b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DefectBounded
import Theorems.Thm_GlobalTheory_SS_exists_pow_factor_free

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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  intro R _ _ _ π _ B _ _ _ hsm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, n, s, t, hts⟩ := exists_pow_factor_free (S := Localization.Away (algebraMap R B π))
    (M' := Ω[Localization.Away (algebraMap R B π)⁄R]) (algebraMap R B π)
    (KaehlerDifferential.map R R B (Localization.Away (algebraMap R B π)))
  refine ⟨c, fun R' _ _ _ a => ?_⟩
  letI := a.toRingHom.toAlgebra
  intro w hw
  obtain ⟨⟨r, hr⟩, hrw⟩ := hw
  have hsw : s.baseChange R' w = 0 := by
    have h0 : r • s.baseChange R' w = 0 := by
      have hrw' : r • w = 0 := hrw
      rw [← LinearMap.map_smul, hrw', map_zero]
    exact (smul_eq_zero.mp h0).resolve_left (nonZeroDivisors.ne_zero hr)
  have hcomp : (t.baseChange R') (s.baseChange R' w) = (algebraMap R B π ^ c) • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hts, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hsw, map_zero] at hcomp
  have hπ : algebraMap R R' π = algebraMap B R' (algebraMap R B π) := (a.commutes π).symm
  rw [hπ, ← map_pow, algebraMap_smul, ← hcomp]
end GlobalTheory.SS
