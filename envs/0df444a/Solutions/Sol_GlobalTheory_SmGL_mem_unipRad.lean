-- Prove2me | solution 1 for GlobalTheory.SmGL.mem_unipRad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:45.536548+00:00
-- url     : https://prove2.me/submissions/a8400800-cbfe-4f81-8141-73b7b49369e2

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
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipRad R e ↔ g ∈ _root_.GlobalTheory.SmGL.parab R e ∧ ∀ a (i j : m a),
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j := by
  rw [_root_.GlobalTheory.SmGL.unipRad, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun a i j => ?_⟩
    have h := congr_arg (fun x : _root_.GlobalTheory.SmGL.Levi R m =>
      ((x a : GL (m a) R) : Matrix (m a) (m a) R) i j) (MonoidHom.mem_ker.1 hp)
    simpa using h
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    funext a
    ext i j
    simp [h]
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
