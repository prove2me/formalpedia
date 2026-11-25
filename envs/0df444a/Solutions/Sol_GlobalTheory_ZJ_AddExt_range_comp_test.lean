-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.range_comp_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:28:06.823893+00:00
-- url     : https://prove2.me/submissions/42bd39eb-e62b-498c-9bee-9aaa89057da6

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
theorem _root_.solution {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) {K : Type}
    [Field K] (u : Sp K ⟶ Sp (OO p)) (hu : ∀ x, u x = cPt p) :
    Set.range (u ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
  have := τ.j_loc
  have h : ∀ x, (u ≫ spMap τ.j) x = IsLocalRing.closedPoint τ.V := fun x => by
    rw [Scheme.Hom.comp_apply, hu]
    exact IsLocalRing.comap_closedPoint τ.j
  ext z
  exact ⟨fun ⟨x, hx⟩ => hx ▸ h x, fun hz => ⟨(⊥ : PrimeSpectrum K), (h _).trans hz.symm⟩⟩
end GlobalTheory.ZJ.AddExt
