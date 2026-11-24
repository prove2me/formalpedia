-- Prove2me | solution 1 for GlobalTheory.seminorm_formPerpVector_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:24.126875+00:00
-- url     : https://prove2.me/submissions/adee7fa1-64ee-4680-a173-58fb41720f74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_seminorm_perpVector_le

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
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (hcs : ∀ u v, ν (h u v) ≤ μ u * μ v)
    (e e' : Fin p → M) (g : M) {r : ℝ}
    (he : ∀ a, μ (e a) ≤ r) (he' : ∀ a, μ (e' a) ≤ r) (hg : μ g ≤ r) :
    μ (formPerpVector h e e' g) ≤ (p + 1)! * r ^ (2 * p + 1) := by
  have hr : 0 ≤ r := (apply_nonneg μ g).trans hg
  have key : ∀ u v, μ u ≤ r → μ v ≤ r → ν (h u v) ≤ r ^ 2 := fun u v hu hv =>
    (hcs u v).trans (by rw [sq]; exact mul_le_mul hu hv (apply_nonneg μ _) hr)
  have := seminorm_perpVector_le ν h1 μ hsmul (fun a => h.flip (e a)) e' g (C := r ^ 2)
    (fun a a' => key _ _ (he' a') (he a)) (fun a => key _ _ hg (he a)) he' hg
  rwa [← pow_mul, mul_assoc, ← pow_succ] at this
end GlobalTheory
