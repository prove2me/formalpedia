-- Prove2me | solution 1 for GlobalTheory.SmGL.leviEmb_mem_parabLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:52.004828+00:00
-- url     : https://prove2.me/submissions/e48e130d-5d65-4261-a2d7-acb974bd05c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_mem_parabLower_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈ _root_.GlobalTheory.SmGL.parabLower R e :=
  (_root_.GlobalTheory.SmGL.mem_parabLower_iff R).2 fun _ _ i j hab =>
    _root_.GlobalTheory.SmGL.leviEmb_apply_ne R e g hab.ne i j
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
