-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_parabLower_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:48.604805+00:00
-- url     : https://prove2.me/submissions/668b6e01-cd53-43ce-83e9-0536dc3c988e

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
    g ∈ _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) ↔
      ∀ (i : a) (j : b), (g : Matrix n n R) (e (.inl i)) (e (.inr j)) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_iff]
  constructor
  · intro h i j
    exact h false true i j (by decide)
  · intro h x y i j hxy
    rcases x with _ | _ <;> rcases y with _ | _
    · exact absurd hxy (by decide)
    · exact h i j
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
