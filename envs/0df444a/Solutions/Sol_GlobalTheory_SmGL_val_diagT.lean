-- Prove2me | solution 1 for GlobalTheory.SmGL.val_diagT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:41.958487+00:00
-- url     : https://prove2.me/submissions/44817441-bb21-4857-a98c-a7c385788fbd

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
theorem _root_.solution (t : n → Rˣ) :
    (_root_.GlobalTheory.SmGL.diagT R n t : Matrix n n R) = diagonal fun i => (t i : R) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq]
    exact (_root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.points n)
      (_root_.GlobalTheory.SmGL.leviTorus R n t) i () ()).trans
        (by simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar])
  · rw [diagonal_apply_ne _ h]
    exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.points n)
      (_root_.GlobalTheory.SmGL.leviTorus R n t) h () ()
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
