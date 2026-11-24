-- Prove2me | solution 1 for GlobalTheory.laurent_degeneration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:33.071158+00:00
-- url     : https://prove2.me/submissions/2b7aaedc-905a-4a22-a8c2-df27b58ff25b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
import Theorems.Thm_GlobalTheory_laurent_degeneration_abstract
import Theorems.Thm_GlobalTheory_laurent_vector_normalise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  intro k _
  letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
  refine ⟨HahnSeries ℤ k, inferInstance, this, HahnSeries.single 1 1, ?_⟩
  intro a e V U _ _ t u
  have hs : ∀ (z : HahnSeries ℤ k) (n : ℤ),
      (HahnSeries.single (1 : ℤ) (1 : k) * z).coeff (n + 1) = z.coeff n := by
    intro z n
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  refine laurent_degeneration_abstract k (HahnSeries ℤ k) (HahnSeries.single 1 1)
    (fun z => z.coeff (-1) = 0) (laurentCoeffForm k 0) (laurentCoeffForm k 1) ?_ ?_ ?_
    (laurent_vector_normalise k) a e V U t u
  · intro z hz
    exact (hs z (-1)).trans hz
  · intro z
    exact hs z 0
  · show (1 : HahnSeries ℤ k).coeff 0 = 1
    simp
end GlobalTheory
