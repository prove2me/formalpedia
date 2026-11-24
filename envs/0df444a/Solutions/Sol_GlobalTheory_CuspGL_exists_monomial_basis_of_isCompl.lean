-- Prove2me | solution 1 for GlobalTheory.CuspGL.exists_monomial_basis_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:00.842573+00:00
-- url     : https://prove2.me/submissions/3b10591d-9a86-4b47-a1f5-5453e323e0fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantEqTopOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisOfImprimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsMonomialBasisAbelianByPrimePower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {k : Type} [Field k] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (U U' : Submodule k V) (h : IsCompl U U')
    (hU : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V))
    (hU' : ∃ (n : ℕ) (b : Module.Basis (Fin n) k U'), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  obtain ⟨n, b, hb⟩ := hU
  obtain ⟨n', b', hb'⟩ := hU'
  let B := (b.prod b').map (Submodule.prodEquivOfIsCompl U U' h)
  have h1 : ∀ i, B (Sum.inl i) = (b i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  have h2 : ∀ i, B (Sum.inr i) = (b' i : V) := by
    intro i
    simp [B, Module.Basis.prod_apply]
  refine ⟨n + n', B.reindex finSumFinEquiv, fun g i => ?_⟩
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i
  · obtain ⟨j, c, hj⟩ := hb g i
    refine ⟨finSumFinEquiv (Sum.inl j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h1, hj]
  · obtain ⟨j, c, hj⟩ := hb' g i
    refine ⟨finSumFinEquiv (Sum.inr j), c, ?_⟩
    simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, h2, hj]
end GlobalTheory.CuspGL
