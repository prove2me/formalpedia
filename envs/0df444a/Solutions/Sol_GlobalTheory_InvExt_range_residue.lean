-- Prove2me | solution 1 for GlobalTheory.InvExt.range_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:45.819648+00:00
-- url     : https://prove2.me/submissions/120a632d-0736-4c16-8fc1-c9ef2080bd84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure

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
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    {K : Type} [Field K] (v : Sp K ⟶ Sp (kb p)) :
    Set.range (v ≫ rPt p ≫ spMap τ.j) = {IsLocalRing.closedPoint τ.V} := by
  have := τ.j_loc
  have h : ∀ x : Sp K, (v ≫ rPt p ≫ spMap τ.j) x = IsLocalRing.closedPoint τ.V := by
    intro x
    have hx : v x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
    exact (congrArg (spMap τ.j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint τ.j)
  ext x
  exact ⟨fun ⟨z, hz⟩ => hz ▸ h z, fun hx => ⟨IsLocalRing.closedPoint K, (h _).trans hx.symm⟩⟩
end GlobalTheory.InvExt
