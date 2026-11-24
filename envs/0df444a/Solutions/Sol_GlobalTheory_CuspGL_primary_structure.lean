-- Prove2me | solution 1 for GlobalTheory.CuspGL.primary_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:22:04.228289+00:00
-- url     : https://prove2.me/submissions/185d14b3-59f4-4b56-8a2f-2fea019b9c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_PrimaryEndomorphismCyclicDecompositionFinrankKer
import Theorems.Thm_GlobalTheory_CuspGL_finrank_ker_lsmul_pow_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by
  intro F _ V _ _ _ g f m hf hm
  classical
  have hT : Module.IsTorsion' (Module.AEval' g) (Submonoid.powers f) := by
    rw [Submodule.isTorsion'_powers_iff]
    intro x
    refine ⟨m, ?_⟩
    apply (Module.AEval'.of g).symm.injective
    rw [Module.AEval.of_symm_smul, hm, zero_smul, map_zero]
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition hf hT
  let σ := Fintype.equivFin {i : Fin d // 0 < k i}
  let ψ : Module.AEval' g ≃ₗ[F[X]]
      ((i : Fin (Fintype.card {i : Fin d // 0 < k i})) → F[X] ⧸ Ideal.span {f ^ k (σ.symm i)}) :=
    φ ≪≫ₗ DirectSum.linearEquivFunOnFintype F[X] (Fin d) (fun i => F[X] ⧸ Ideal.span {f ^ k i}) ≪≫ₗ
      piDropTrivial (fun i => F[X] ⧸ Ideal.span {f ^ k i}) (fun i => 0 < k i) (fun i hi => by
        have : k i = 0 := by omega
        rw [Ideal.Quotient.subsingleton_iff, this, pow_zero, Ideal.span_singleton_one]) ≪≫ₗ
      LinearEquiv.piCongrLeft' F[X] (fun i : {i : Fin d // 0 < k i} => F[X] ⧸ Ideal.span {f ^ k i}) σ
  refine ⟨_, fun i => k (σ.symm i), fun i => (σ.symm i).2, ⟨ψ⟩, fun j => ?_⟩
  haveI : ∀ e : ℕ, Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) := fun e =>
    (AdjoinRoot.powerBasis (pow_ne_zero e hf.ne_zero)).finite
  rw [(kerAevalEquivPi g _ ψ (f ^ j)).finrank_eq, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => finrank_ker_lsmul_pow_quotient f hf.ne_zero _ j
end GlobalTheory.CuspGL
