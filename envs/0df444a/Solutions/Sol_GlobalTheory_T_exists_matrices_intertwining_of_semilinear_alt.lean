-- Prove2me | solution 1 for GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:47.08834+00:00
-- url     : https://prove2.me/submissions/bf17103e-6e5a-4bbf-9bc1-c32c42fc0f93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Theorems.Thm_GlobalTheory_exists_matrices_intertwining_of_semilinear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  first | exact @GlobalTheory.exists_matrices_intertwining_of_semilinear | exact GlobalTheory.exists_matrices_intertwining_of_semilinear | (intros; apply GlobalTheory.exists_matrices_intertwining_of_semilinear <;> assumption)
end _root_.GlobalTheory.T
