-- Prove2me | solution 1 for GlobalTheory.graphClosure.flat_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:03.566018+00:00
-- url     : https://prove2.me/submissions/d12b8c20-e482-4f6b-ae94-343fc6aec5cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_flat_of_schemeDominant_of_isBezout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {S Z₁ Z₂ U T T' : Scheme.{u}} (f₁ : Z₁ ⟶ S) (f₂ : Z₂ ⟶ S) (u : U ⟶ Z₁) (φ : U ⟶ Z₂)
  (h : u ≫ f₁ = φ ≫ f₂)
namespace GlobalTheory
namespace graphClosure
theorem _root_.solution {O : CommRingCat.{u}} [IsDomain O] [ValuationRing O]
    (f₁ : Z₁ ⟶ Spec O) (f₂ : Z₂ ⟶ Spec O) (u : U ⟶ Z₁) (φ : U ⟶ Z₂) (h : u ≫ f₁ = φ ≫ f₂)
    [QuasiCompact u] [QuasiSeparated f₂] [Flat (u ≫ f₁)] :
    Flat (graphClosure.fst f₁ f₂ u φ h ≫ f₁) :=
  have : Flat (graphClosure.incl f₁ f₂ u φ h ≫ graphClosure.fst f₁ f₂ u φ h ≫ f₁) := by simpa
  flat_of_schemeDominant_of_isBezout (graphClosure.incl f₁ f₂ u φ h) _
end graphClosure
end GlobalTheory
