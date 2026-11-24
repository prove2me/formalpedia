-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpLower.sum_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:21.471386+00:00
-- url     : https://prove2.me/submissions/b32c42a4-39ff-4274-9131-4e1dc8699fee

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset
namespace GlobalTheory.CompanionTheory.GapOpLower
theorem _root_.solution {k : Type} [Field k] [Fintype k] {n : ℕ}
    (R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ) :
    ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ a, ∑ b, ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
          * R a b := by
  calc ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = ∑ x : Fin (n + 1) → k, ∑ a, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ⬝ᵥ x = 1
        · simp [ha, Finset.sum_filter]
        · simp [ha]
    _ = ∑ a, ∑ x : Fin (n + 1) → k, ∑ b, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x : Fin (n + 1) → k, if (a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1) then R a b else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
end GlobalTheory.CompanionTheory.GapOpLower
