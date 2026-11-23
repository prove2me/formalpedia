-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_parabLower_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:56.203612+00:00
-- url     : https://prove2.me/submissions/757f72f5-8d3e-4507-9546-f0ec25f4ce22

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
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parabLower R e ↔ ∀ a b (i : m a) (j : m b), a < b →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  unfold _root_.GlobalTheory.SmGL.parabLower
  rw [_root_.GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h (OrderDual.toDual a) (OrderDual.toDual b) i j hab
  · intro h a b i j hab
    exact h (OrderDual.ofDual a) (OrderDual.ofDual b) i j hab
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
