-- Prove2me | solution 1 for GlobalTheory.SmGL.coe_mem_unipRad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:29.019435+00:00
-- url     : https://prove2.me/submissions/aa3b2cea-d4b2-483f-b727-c33fa0874cce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower

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
theorem _root_.solution {e : (Σ a, m a) ≃ n}
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    (p : GL n R) ∈ _root_.GlobalTheory.SmGL.unipRad R e ↔ _root_.GlobalTheory.SmGL.leviProj R e p = 1 :=
  (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).trans MonoidHom.mem_ker
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
