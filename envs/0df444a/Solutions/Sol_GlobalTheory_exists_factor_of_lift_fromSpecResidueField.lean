-- Prove2me | solution 1 for GlobalTheory.exists_factor_of_lift_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:32.837098+00:00
-- url     : https://prove2.me/submissions/9f3e5191-0a73-4de9-87c5-fd6fc55bf1ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints
import Theorems.Thm_GlobalTheory_exists_factor_fromSpecResidueField
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y W : Scheme.{0}} (h : Y ⟶ W) (w : W)
    (ξ : Spec (W.residueField w) ⟶ Y) (hξ : ξ ≫ h = W.fromSpecResidueField w)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ Y)
    (ha : a (IsLocalRing.closedPoint K) = ξ (IsLocalRing.closedPoint (W.residueField w))) :
    ∃ σ : W.residueField w ⟶ .of K, Spec.map σ ≫ ξ = a := by
  obtain ⟨σ, hσ⟩ := exists_factor_fromSpecResidueField a ha
  generalize hy : ξ (IsLocalRing.closedPoint (W.residueField w)) = y at σ hσ
  obtain ⟨φ, hφ⟩ := exists_factor_fromSpecResidueField (K := W.residueField w) ξ hy
  obtain ⟨ψ, hψ⟩ := exists_factor_fromSpecResidueField (K := Y.residueField y)
    (Y.fromSpecResidueField y ≫ h) (x := w) (by
      refine (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg h (Scheme.fromSpecResidueField_apply y _)).trans ?_)
      rw [← hy, ← Scheme.Hom.comp_apply, hξ]
      exact Scheme.fromSpecResidueField_apply w _)
  have h1 : ψ ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono (W.fromSpecResidueField w), Spec.map_comp, Category.assoc, hψ,
      ← Category.assoc, hφ, hξ, Spec.map_id]
    exact (Category.id_comp _).symm
  have h2 : φ ≫ ψ = 𝟙 _ := by
    ext z
    apply φ.hom.injective
    exact congr($h1 (φ z))
  refine ⟨ψ ≫ σ, ?_⟩
  rw [← hσ, ← hφ, ← Spec.map_comp_assoc, ← Category.assoc φ, h2, Category.id_comp]
end GlobalTheory
