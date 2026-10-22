-- Prove2me | solution 1 for MazurTransfer.original_finite_free_hopf_arithmetic_point_rank
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T19:03:09.316004+00:00
-- url     : https://prove2.me/submissions/3339fe17-83a7-4378-91fd-8b1e2cb51ed3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: derive rank from a given arithmetic point equivalence of the same finite-free Hopf algebra, preserving the complete original characteristic-zero Cartier theorem and all universes.
Named downstream consumer: cyclotomic Hopf classification of the same selected integral character quotient.
-/
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
noncomputable section
universe u v w x
namespace MazurTransfer.OriginalFiniteFreeHopfArithmeticPointRankBoundary20261020
end MazurTransfer.OriginalFiniteFreeHopfArithmeticPointRankBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: derive rank from a GIVEN algebraically closed arithmetic
point label of the SAME finite-free Hopf algebra, using the complete
Anthropic FLT characteristic-zero Cartier theorem at its exact pin.
Named downstream consumer: actual selected nineteen character quotient ranks.
-/

noncomputable section
namespace MazurTransfer.OriginalFiniteFreeHopfArithmeticPointRankProof20261020
variable {R : Type u} [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Free R H]
variable (K : Type w) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K]
variable {M : Type x} (e : WithConv (H →ₐ[R] K) ≃ M)

include e in
theorem finrank_eq_arithmetic_card : Module.finrank R H = Nat.card M := by
  have hw : Nat.card (WithConv (H →ₐ[R] K)) = Nat.card (H →ₐ[R] K) :=
    Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩
  exact (HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R H K).symm.trans
    (hw.symm.trans (Nat.card_congr e))

end MazurTransfer.OriginalFiniteFreeHopfArithmeticPointRankProof20261020

theorem solution : ∀ {R : Type u} [CommRing R] (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] (K : Type w) [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] {M : Type x} (e : WithConv (H →ₐ[R] K) ≃ M), Module.finrank R H = Nat.card M := by
  exact MazurTransfer.OriginalFiniteFreeHopfArithmeticPointRankProof20261020.finrank_eq_arithmetic_card
#print axioms solution
