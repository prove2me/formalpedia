-- Prove2me | solution 1 for GlobalTheory.CuspGL.primary_conj_of_finrank_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:25.191804+00:00
-- url     : https://prove2.me/submissions/437080f8-0b02-4902-ac02-7f66e6f28a1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ConjOfPrimaryFinrankKerPowEq
import Theorems.Thm_P2M_GlobalTheory_CuspGL_exists_conj_of_aeval__equiv_6dd8055a4950
import Theorems.Thm_GlobalTheory_T_exists_perm_of_sum_min_eq_positive_family
import Theorems.Thm_GlobalTheory_T_primary_endomorphism_cyclic_decomposition_finrank_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g g' : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → aeval g' (f ^ m) = 0 → (∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval g' (f ^ j)))) → ∃ e : V ≃ₗ[F] V, e.conj g = g' := by
  intro F _ V _ _ _ g g' f m hf hg hg' hk
  obtain ⟨d, e, he, ⟨φ⟩, hd⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g f m hf hg
  obtain ⟨d', e', he', ⟨φ'⟩, hd'⟩ := GlobalTheory.T.primary_endomorphism_cyclic_decomposition_finrank_ker F V g' f m hf hg'
  have hpos : 0 < f.natDegree := hf.natDegree_pos
  have hs : ∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i) := by
    intro j
    have := hk j
    rw [hd j, hd' j] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family d d' e e' he he' hs
  obtain rfl : e = fun i => e' (σ i) := funext fun i => (hσ i).symm
  exact exists_conj_of_aeval'_equiv g g' (φ.trans
    ((LinearEquiv.piCongrLeft F[X] (fun i => F[X] ⧸ Ideal.span {f ^ e' i}) σ).trans φ'.symm))
end GlobalTheory.CuspGL
