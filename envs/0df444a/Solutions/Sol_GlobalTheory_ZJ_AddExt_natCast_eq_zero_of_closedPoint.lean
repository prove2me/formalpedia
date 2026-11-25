-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.natCast_eq_zero_of_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:53.926975+00:00
-- url     : https://prove2.me/submissions/2b1be4ca-497e-47af-b5cc-dca07e14ff96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (u : Sp K ⟶ Sp (OO p))
    (hu : ∀ x, u x = cPt p) : (p : K) = 0 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective u
  have h1 : (p : OO p) ∈ IsLocalRing.maximalIdeal (OO p) := by
    rw [Valuation.mem_maximalIdeal_iff]
    have : ((p : OO p) : PadicAlgCl p) = p := by simp
    rw [this, PadicAlgCl.valuation_p, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h2 := congrArg PrimeSpectrum.asIdeal (hu (⊥ : PrimeSpectrum K))
  have h3 : (p : OO p) ∈ Ideal.comap φ.hom (⊥ : Ideal K) := by
    have : Ideal.comap φ.hom (⊥ : Ideal K) = IsLocalRing.maximalIdeal (OO p) := h2
    rw [this]; exact h1
  simpa using h3
end GlobalTheory.ZJ.AddExt
