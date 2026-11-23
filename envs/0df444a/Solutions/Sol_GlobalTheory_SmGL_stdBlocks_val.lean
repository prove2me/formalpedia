-- Prove2me | solution 1 for GlobalTheory.SmGL.stdBlocks_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:03.194389+00:00
-- url     : https://prove2.me/submissions/b800ced6-223c-4784-b941-85169e23ab07

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
theorem _root_.solution {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N)
    (a : Fin s) (i : Fin (d a)) :
    (_root_.GlobalTheory.SmGL.stdBlocks d h ⟨a, i⟩ : ℕ) =
      ∑ b : Fin a, d (Fin.castLE a.2.le b) + i := by
  simp [_root_.GlobalTheory.SmGL.stdBlocks, finSigmaFinEquiv_apply]
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
