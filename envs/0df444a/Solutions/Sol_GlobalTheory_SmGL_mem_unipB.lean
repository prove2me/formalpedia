-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_unipB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:13.29884+00:00
-- url     : https://prove2.me/submissions/6797da39-cdfa-47fc-81cc-a059be956cd9

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
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n]
    [LinearOrder n] {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipB R n ↔
      (∀ i j, j < i → (g : Matrix n n R) i j = 0) ∧ ∀ i, (g : Matrix n n R) i i = 1 := by
  show g ∈ _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.points n) ↔ _
  rw [_root_.GlobalTheory.SmGL.mem_unipRad]
  refine and_congr _root_.GlobalTheory.SmGL.mem_parab ⟨fun h i => ?_, fun h a i j => ?_⟩
  · exact (h i () ()).trans (one_apply_eq ())
  · cases i
    cases j
    exact (h a).trans (one_apply_eq ()).symm
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
