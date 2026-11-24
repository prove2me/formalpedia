-- Prove2me | solution 1 for GlobalTheory.exists_coords_of_alt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:03.346412+00:00
-- url     : https://prove2.me/submissions/3e5701f6-b459-4eec-b4da-d8f7faff4cca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealGeneratesDualVector

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
    {x x' : V} (h : B x x' ≠ 0) (v : V) : ∃ c c' : F, v = c • x + c' • x' := by
  have hanti : B x' x = - B x x' := by
    have h1 := hB (x + x')
    simp only [map_add, LinearMap.add_apply, hB] at h1
    linear_combination h1
  have hli : LinearIndependent F ![x, x'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun u => B u x') hst
    have h2 := congrArg (fun u => B x u) hst
    simp [hB] at h1 h2
    exact ⟨h1.resolve_right h, h2.resolve_right h⟩
  have hsp : Submodule.span F (Set.range ![x, x']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hv : v ∈ Submodule.span F (Set.range ![x, x']) := by rw [hsp]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hv
  obtain ⟨a, b, hab⟩ := hv
  exact ⟨a, b, hab.symm⟩
end GlobalTheory
