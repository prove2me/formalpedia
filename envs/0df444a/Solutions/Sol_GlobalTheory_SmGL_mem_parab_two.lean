-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_parab_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:37.354795+00:00
-- url     : https://prove2.me/submissions/42030d55-b445-4ea6-afa2-f23b479c2237

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
omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution {e : a ⊕ b ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two e) ↔
      ∀ (j : b) (i : a), (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · intro h j i
    exact h true false j i (by decide)
  · intro h x y i j hxy
    rcases x with _ | _ <;> rcases y with _ | _
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · exact h i j
    · exact absurd hxy (by decide)
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
