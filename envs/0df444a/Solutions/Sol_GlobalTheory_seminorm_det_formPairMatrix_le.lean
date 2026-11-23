-- Prove2me | solution 1 for GlobalTheory.seminorm_det_formPairMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:16.210654+00:00
-- url     : https://prove2.me/submissions/2bda6009-05a5-40fe-b5cd-affb90e56d3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_ringSeminorm_det_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}
namespace GlobalTheory
theorem _root_.solution {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) {r : ℝ} (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) :
    ν (formPairMatrix h e e').det ≤ p ! * r ^ (2 * p) := by
  have := ringSeminorm_det_le ν h1 (formPairMatrix h e e') (C := r ^ 2) fun i j =>
    (hcs _ _).trans (by
      rw [sq]
      exact mul_le_mul (he' i) (he j) (apply_nonneg μ _) ((apply_nonneg μ _).trans (he' i)))
  rwa [Fintype.card_fin, ← pow_mul] at this
end GlobalTheory
