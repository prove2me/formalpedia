-- Prove2me | solution 1 for GlobalTheory.CoeffExt.finrank_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:31.532452+00:00
-- url     : https://prove2.me/submissions/aa752486-3acb-4875-8405-ee32fa82a9c3

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
namespace GlobalTheory.CoeffExt
theorem _root_.solution {O O' : Type} [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W']
    [IsScalarTower O O' W'] {ι : Type} [Fintype ι] (b : Basis ι O O') (E : W' ≃ₗ[O] (ι → W))
    (S' : Submodule O' W') (S : Submodule O W) [Module.Free O' ↥S'] [Module.Free O ↥S]
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : finrank O' ↥S' = finrank O ↥S := by
  have : Nontrivial O := (algebraMap O O').domain_nontrivial
  have : Module.Free O O' := Module.Free.of_basis b
  have : Nonempty ι := b.index_nonempty
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eS : ↥(S'.restrictScalars O) ≃ₗ[O] (ι → ↥S) := subEquiv E (S'.restrictScalars O) S hS
  have hpi : finrank O (ι → ↥S) = Fintype.card ι * finrank O ↥S :=
    (Finsupp.linearEquivFunOnFinite O ↥S ι).finrank_eq.symm.trans (finrank_finsupp O ↥S)
  have t := Module.finrank_mul_finrank O O' ↥S'
  have t' : finrank O ↥S' = finrank O (ι → ↥S) := eS.finrank_eq
  rw [Module.finrank_eq_card_basis b, t', hpi] at t
  exact Nat.eq_of_mul_eq_mul_left hn t
end GlobalTheory.CoeffExt
