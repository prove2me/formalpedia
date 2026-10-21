-- Prove2me | solution 1 for MazurTransfer.original_representation_canonical_distrib_mul_action
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T01:58:50.251806+00:00
-- url     : https://prove2.me/submissions/e0fae795-0060-4256-bdd5-4ac820661975

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the action of the same fixed representation is definitionally its original linear operators.
Named downstream consumer: selected ordered arithmetic character quotients in the finite-flat Hopf quotient construction.
-/
import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
noncomputable section

open MazurTransfer.RepresentationCanonicalDistribMulAction
universe u v w
namespace MazurTransfer.OriginalRepresentationCanonicalDistribMulActionProof20261020Boundary
end MazurTransfer.OriginalRepresentationCanonicalDistribMulActionProof20261020Boundary
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: expose the action of a FIXED representation as a
DistribMulAction, definitionally its original linear operators.
Named downstream consumer: selected ordered arithmetic character
quotients in the finite-flat Hopf quotient construction.
-/

namespace MazurTransfer.OriginalRepresentationCanonicalDistribMulActionProof20261020
variable {k : Type u} [Semiring k] {G : Type v} [Monoid G]
variable {V : Type w} [AddCommMonoid V] [Module k V]



variable (ρ : Representation k G V)
theorem ofRepresentation_smul (g : G) (v : V) :
    letI : DistribMulAction G V := ofRepresentation ρ
    g • v = ρ g v := rfl

end MazurTransfer.OriginalRepresentationCanonicalDistribMulActionProof20261020

theorem solution : (∀ {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type w} [AddCommMonoid V] [Module k V] (ρ : Representation k G V) (g : G) (v : V), letI : DistribMulAction G V := ofRepresentation ρ; g • v = ρ g v) := by
  exact MazurTransfer.OriginalRepresentationCanonicalDistribMulActionProof20261020.ofRepresentation_smul
#print axioms solution
