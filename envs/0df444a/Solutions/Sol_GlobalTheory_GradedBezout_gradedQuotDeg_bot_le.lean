-- Prove2me | solution 1 for GlobalTheory.GradedBezout.gradedQuotDeg_bot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:20.609201+00:00
-- url     : https://prove2.me/submissions/aca6ed2b-18fd-4802-b114-d6ebc3439458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_degree_le_of_eventually_eval_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
open GlobalTheory.GradedBezout
variable [GradedAlgebra 𝒜]
variable {𝒜}
variable {ι : Type*} [Finite ι] {x : ι → T} (hx : ∀ i, x i ∈ 𝒜 1)
  (hfin : Module.Finite (Algebra.adjoin K (Set.range x)) T)
include hx hfin
namespace GlobalTheory.GradedBezout
theorem _root_.solution {r : ℕ} {c : ℚ}
    (h : ∀ᶠ n : ℕ in atTop, (finrank K (𝒜 n) : ℚ) ≤ (c * n) ^ r) :
    gradedQuotDeg 𝒜 r ⊥ ≤ r.factorial * c ^ r := by
  have hb := Ideal.IsHomogeneous.bot 𝒜
  have h1 : ∀ᶠ n : ℕ in atTop, (gradedQuotHilbertPoly 𝒜 ⊥).eval (n : ℚ) ≤
      (monomial r (c ^ r) : ℚ[X]).eval (n : ℚ) := by
    filter_upwards [h, eventually_finrank hx hfin hb] with n hn hn'
    have := finrank_piece_add hx hfin ⊥ n
    rw [← hn', eval_monomial, ← mul_pow]
    exact le_trans (by exact_mod_cast (by omega)) hn
  have h2 := (degree_le_of_eventually_eval_nat (eventually_nonneg hx hfin hb) h1).trans
    (degree_monomial_le r _)
  have h3 := coeff_nonneg_of_eventually_eval_nat
    ((degree_sub_le _ _).trans (max_le (degree_monomial_le r (c ^ r)) h2)) (by
      filter_upwards [h1] with n hn
      rwa [eval_sub, sub_nonneg])
  rw [coeff_sub, coeff_monomial_same, sub_nonneg] at h3
  exact mul_le_mul_of_nonneg_left h3 (by positivity)
end GlobalTheory.GradedBezout
