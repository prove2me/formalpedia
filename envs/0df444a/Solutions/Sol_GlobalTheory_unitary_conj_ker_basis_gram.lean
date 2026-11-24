-- Prove2me | solution 1 for GlobalTheory.unitary_conj_ker_basis_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:43.240676+00:00
-- url     : https://prove2.me/submissions/06ade0dd-4d08-4adb-892b-5e520ef063e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryConjMapsKerAevalBasisAndGram
import Theorems.Thm_GlobalTheory_ConjugateAlgebraLemmas_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first
  | exact @_root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | (apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main ..)
end GlobalTheory
