-- Prove2me | solution 1 for GlobalTheory.specAlgebraMap_comp_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:11.757021+00:00
-- url     : https://prove2.me/submissions/d99c7eda-e574-4834-ab66-c6bf50c1b710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {X X' S S' : Scheme.{u}}
variable (p : X ⟶ S) [UniversallyClosed p] [IsSeparated p] (r : Spec (.of V) ⟶ S)
  (y : Spec (.of K) ⟶ X) (h : y ≫ p = specAlgebraMap V K ≫ r)
variable {V' K' : Type u} [CommRing V'] [IsDomain V'] [ValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']
omit [IsDomain V] [ValuationRing V] [IsFractionRing V K] [IsDomain V'] [ValuationRing V']
  [IsFractionRing V' K']
namespace GlobalTheory
theorem _root_.solution (ψ : V →+* V') (χ : K →+* K')
    (w : χ.comp (algebraMap V K) = (algebraMap V' K').comp ψ) :
    specAlgebraMap V' K' ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom χ) ≫ specAlgebraMap V K := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, w]
end GlobalTheory
