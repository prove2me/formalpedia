-- Prove2me | solution 1 for GlobalTheory.SmGL.leviEmb_mem_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:01.196127+00:00
-- url     : https://prove2.me/submissions/0e6a81e0-eb86-4791-9bfe-63917652ee36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_parab_le_normalizer

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
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRad R e : Set (GL n R)) :=
  _root_.GlobalTheory.SmGL.parab_le_normalizer R e
    (_root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g)
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
