-- Prove2me | solution 1 for GlobalTheory.cech_kuenneth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:51.93663+00:00
-- url     : https://prove2.me/submissions/bc7ed33c-5b88-41e2-beb0-b371beabd1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_cube_kuenneth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (hA : ∀ p, Module.Finite K ((cechComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cechComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (trunc₂ (extTensor A B))).homology (n + 2)) ∧
      finrank K ((cubeComplex (trunc₂ (extTensor A B))).homology (n + 2)) = ∑ x ∈ antidiagonal n,
        finrank K ((cechComplex A).homology x.1) * finrank K ((cechComplex B).homology x.2) := by
  have h0 : ∀ {ι : Type} [LinearOrder ι] (A : Cube.{v} ι K),
      Subsingleton ((cubeComplex (trunc₁ A)).homology 0) := fun A =>
    ModuleCat.subsingleton_of_isZero
      ((exactAt_iff_isZero_homology _ _).1 (cubeComplex_trunc₁_exactAt_zero A))
  have hf : ∀ {ι : Type} [LinearOrder ι] (A : Cube.{v} ι K),
      (∀ p, Module.Finite K ((cechComplex A).homology p)) →
      ∀ p, Module.Finite K ((cubeComplex (trunc₁ A)).homology p) := fun A hA p => by
    cases p with
    | zero => have := h0 A; infer_instance
    | succ p => exact Module.Finite.equiv (truncHomologyIso A p).toLinearEquiv.symm
  obtain ⟨h1, h2⟩ := cube_kuenneth (trunc₁ A) (trunc₁ B) (hf A hA) (hf B hB) (n + 2)
  let E := (cubeHomologyMapIso (trunc₂ExtTensorIso A B) (n + 2)).toLinearEquiv
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  have := h0 A
  have := h0 B
  rw [E.finrank_eq, h2, Finset.Nat.antidiagonal_succ_succ', Finset.sum_cons, Finset.sum_cons,
    Finset.sum_map, Module.finrank_zero_of_subsingleton (M := (cubeComplex (trunc₁ A)).homology 0),
    Module.finrank_zero_of_subsingleton (M := (cubeComplex (trunc₁ B)).homology 0), zero_mul,
    mul_zero, zero_add, zero_add]
  exact Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·)
    (truncHomologyIso A x.1).toLinearEquiv.finrank_eq
    (truncHomologyIso B x.2).toLinearEquiv.finrank_eq
end GlobalTheory
