-- Prove2me | solution 1 for GlobalTheory.GradedBezout.exists_nat_gradedQuotDeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:34.438674+00:00
-- url     : https://prove2.me/submissions/3d6895ac-e9cc-42c5-8b7b-f89c2ce123a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_exists_int_factorial_mul_coeff


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
theorem _root_.solution {I : Ideal T} (hI : I.IsHomogeneous 𝒜) {r : ℕ}
    (hr : (gradedQuotHilbertPoly 𝒜 I).degree ≤ r) : ∃ D : ℕ, gradedQuotDeg 𝒜 r I = D := by
  obtain ⟨z, hz⟩ := exists_int_factorial_mul_coeff hr (by
    filter_upwards [eventually_finrank hx hfin hI] with n hn
    exact ⟨finrank K (gradedQuotPiece 𝒜 I n), by rw [← hn]; simp⟩)
  have h0 : 0 ≤ (r.factorial : ℚ) * (gradedQuotHilbertPoly 𝒜 I).coeff r :=
    mul_nonneg (by positivity)
      (coeff_nonneg_of_eventually_eval_nat hr (eventually_nonneg hx hfin hI))
  rw [hz] at h0
  lift z to ℕ using (by exact_mod_cast h0)
  exact ⟨z, by simpa [gradedQuotDeg] using hz⟩
end GlobalTheory.GradedBezout
