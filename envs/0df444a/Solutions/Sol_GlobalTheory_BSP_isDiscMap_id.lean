-- Prove2me | solution 1 for GlobalTheory.BSP.isDiscMap_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:00:17.972906+00:00
-- url     : https://prove2.me/submissions/76d3d3d0-192a-4e58-91ec-69ac15fb144a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
namespace GlobalTheory.BSP
namespace _root_.GlobalTheory.BSP
theorem _root_.solution :
    _root_.GlobalTheory.BSP.IsDiscMap (RingHom.id A) (RingHom.id (_root_.GlobalTheory.BSP.Disc l u ρ)) :=
  ⟨fun _ => rfl, fun _ => le_rfl⟩
end _root_.GlobalTheory.BSP
end GlobalTheory.BSP
