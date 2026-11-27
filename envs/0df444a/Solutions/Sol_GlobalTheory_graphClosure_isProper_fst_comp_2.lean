-- Prove2me | solution 2 for GlobalTheory.graphClosure.isProper_fst_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:36.144208+00:00
-- url     : https://prove2.me/submissions/bc0ae751-b4e0-428f-bea7-57632be70331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

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
theorem _root_.solution [IsProper f₁] [IsProper f₂] : IsProper (fst f₁ f₂ u φ h ≫ f₁) :=
  inferInstance
end GlobalTheory.graphClosure
