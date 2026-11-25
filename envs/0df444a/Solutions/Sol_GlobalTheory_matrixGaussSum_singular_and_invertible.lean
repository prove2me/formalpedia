-- Prove2me | solution 1 for GlobalTheory.matrixGaussSum_singular_and_invertible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:03.04151+00:00
-- url     : https://prove2.me/submissions/388d9dfa-af0e-48fd-afb5-d54472327b2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Theorems.Thm_GlobalTheory_matrixGaussSum_mul_unit
import Theorems.Thm_GlobalTheory_exists_gl_det_eq_mul_eq_of_det_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∀ a : Matrix (Fin r) (Fin r) k, a.det = 0 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) = 0) ∧ ∀ a : GL (Fin r) k, (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace ((a : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)))) = ((ξ (Matrix.GeneralLinearGroup.det a) : Rˣ) : R) * (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) := by
  intro k _ _ _ R _ _ ψ ξ r _ hξ
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, ξ t ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (MonoidHom.ext h)
    obtain ⟨g, hg, hag⟩ := exists_gl_det_eq_mul_eq_of_det_eq_zero k r a ha t
    have h := matrixGaussSum_mul_unit k R ψ ξ r a g
    rw [hag, hg] at h
    have h1 : ((ξ t : Rˣ) : R) ≠ 1 := fun h' => ht (Units.ext h')
    by_contra hS
    exact h1 (mul_right_cancel₀ hS (h.symm.trans (one_mul _).symm))
  · have h := matrixGaussSum_mul_unit k R ψ ξ r 1 a
    rwa [Matrix.one_mul] at h
end GlobalTheory
