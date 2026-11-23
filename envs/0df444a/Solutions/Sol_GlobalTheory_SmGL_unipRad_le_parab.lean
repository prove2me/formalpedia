-- Prove2me | solution 1 for GlobalTheory.SmGL.unipRad_le_parab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:56.432289+00:00
-- url     : https://prove2.me/submissions/897032cb-bb3e-4de4-8dc8-9a8a121e8e34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad

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
theorem _root_.solution (e : (Σ a, m a) ≃ n) :
    _root_.GlobalTheory.SmGL.unipRad R e ≤ _root_.GlobalTheory.SmGL.parab R e := fun _ hg =>
  (_root_.GlobalTheory.SmGL.mem_unipRad.1 hg).1
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
