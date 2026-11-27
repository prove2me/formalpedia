-- Prove2me | solution 1 for GlobalTheory.graphClosure.opensRange_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:37.798813+00:00
-- url     : https://prove2.me/submissions/0c773649-f3ae-4a8d-bc75-4242fe406350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_graphClosure_range_incl

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
open GlobalTheory.graphClosure
namespace GlobalTheory.graphClosure
theorem _root_.solution [IsOpenImmersion u] [QuasiCompact u] [IsSeparated f₂] :
    (incl f₁ f₂ u φ h).opensRange = fst f₁ f₂ u φ h ⁻¹ᵁ u.opensRange :=
  Opens.ext (range_incl f₁ f₂ u φ h)
end GlobalTheory.graphClosure
