-- Prove2me | solution 1 for GlobalTheory.SmGL.leviEmb_mem_normalizer_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.128183+00:00
-- url     : https://prove2.me/submissions/d72bd82c-ff6b-40fc-b22a-877558395518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_parab_le_normalizer
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_parabLower

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
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRadLower R e : Set (GL n R)) :=
  _root_.GlobalTheory.SmGL.parab_le_normalizer R (_root_.GlobalTheory.SmGL.opp e)
    (_root_.GlobalTheory.SmGL.leviEmb_mem_parabLower R e g)
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
