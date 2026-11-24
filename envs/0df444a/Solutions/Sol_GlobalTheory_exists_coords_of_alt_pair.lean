-- Prove2me | solution 1 for GlobalTheory.exists_coords_of_alt_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:04.04759+00:00
-- url     : https://prove2.me/submissions/417e8853-2f59-487c-a163-4c202b3fe2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealPairOfVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {v w : V} (hv : v ≠ 0) (hw : B w v = 1) (u : V) : ∃ p q : F, p • v + q • w = u := by
  have hli : LinearIndependent F ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : B (s • v + t • w) v = 0 := by rw [h]; simp
    have ht : t = 0 := by simpa [hB, hw] using h1
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hv, rfl⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hr : Set.range ![v, w] = {v, w} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hr] at hsp
  have hu : u ∈ Submodule.span F ({v, w} : Set V) := by rw [hsp]; trivial
  exact Submodule.mem_span_pair.mp hu
end GlobalTheory
