-- Prove2me | solution 1 for GlobalTheory.SmGL.parab_le_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:23.582492+00:00
-- url     : https://prove2.me/submissions/c099349d-ce5b-41dd-99ea-7143398fc3b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab
import Theorems.Thm_GlobalTheory_SmGL_coe_mem_unipRad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.SmGL
section Blocks
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
private lemma conj_mem_unipRad_of_mem_parab {e : (Σ a, m a) ≃ n} {p u : GL n R}
    (hp : p ∈ _root_.GlobalTheory.SmGL.parab R e) (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    p * u * p⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e := by
  have hu' := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  let P : _root_.GlobalTheory.SmGL.parab R e := ⟨p, hp⟩
  let U : _root_.GlobalTheory.SmGL.parab R e := ⟨u, hu'⟩
  have hU : _root_.GlobalTheory.SmGL.leviProj R e U = 1 :=
    (_root_.GlobalTheory.SmGL.coe_mem_unipRad R U).1 hu
  show ((P * U * P⁻¹ : _root_.GlobalTheory.SmGL.parab R e) : GL n R) ∈ _
  rw [_root_.GlobalTheory.SmGL.coe_mem_unipRad, map_mul, map_mul, map_inv, hU,
    mul_one, mul_inv_cancel]
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Blocks
end GlobalTheory.SmGL
end
end

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
    _root_.GlobalTheory.SmGL.parab R e ≤
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRad R e : Set (GL n R)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact conj_mem_unipRad_of_mem_parab R hp
  · intro h
    have := conj_mem_unipRad_of_mem_parab R (inv_mem hp) h
    simpa [mul_assoc] using this
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
