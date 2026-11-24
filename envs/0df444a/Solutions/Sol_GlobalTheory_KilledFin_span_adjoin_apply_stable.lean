-- Prove2me | solution 1 for GlobalTheory.KilledFin.span_adjoin_apply_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:32:31.302841+00:00
-- url     : https://prove2.me/submissions/605ee603-587d-40a8-9393-73825aa677ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAlgebraOrbitOfAnnihilated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.KilledFin
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.KilledFin
theorem _root_.solution (s : Set (Module.End ℂ V)) (ψ : V) (u : Module.End ℂ V)
    (hu : u ∈ Algebra.adjoin ℂ s) (v : V)
    (hv : v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V)))) :
    u v ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
      (Algebra.adjoin ℂ s : Set (Module.End ℂ V))) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨u * z, Subalgebra.mul_mem _ hu hz, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
end GlobalTheory.KilledFin
