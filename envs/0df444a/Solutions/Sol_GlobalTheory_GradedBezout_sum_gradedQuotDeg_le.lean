-- Prove2me | solution 1 for GlobalTheory.GradedBezout.sum_gradedQuotDeg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:40.39469+00:00
-- url     : https://prove2.me/submissions/d0ea0536-487b-44a4-a11e-95434ab9c677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_GradedBezout_sum_coeff_hilbertPoly_le
import Theorems.Thm_GlobalTheory_coeff_sub_comp_X_sub_C


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
theorem _root_.solution {P : Ideal T} [P.IsPrime] (hI : P.IsHomogeneous 𝒜) {e : ℕ}
    (he : ringKrullDim (T ⧸ P) = (e + 2 : ℕ)) {f : T} {a : ℕ} (hf : f ∈ 𝒜 a) (hfP : f ∉ P)
    (s : Finset (Ideal T)) (hs : ∀ Q ∈ s, Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    ∑ Q ∈ s, gradedQuotDeg 𝒜 e Q ≤ a * gradedQuotDeg 𝒜 (e + 1) P := by
  have hd := degree_hilbertPoly_eq_of_isPrime hx hfin hI (e := e + 1) he
  obtain ⟨h1, h2⟩ := coeff_sub_comp_X_sub_C (gradedQuotHilbertPoly 𝒜 P) (a : ℚ) e hd.le
  rw [← hilbertPoly_sup_of_isPrime hx hfin hI hf hfP] at h1 h2
  have h3 := sum_coeff_hilbertPoly_le hx hfin (isHomogeneous_sup_span hI hf) (e := e)
    ((degree_le_iff_coeff_zero _ _).2 fun m hm =>
      (degree_lt_iff_coeff_zero _ _).1 h1 m (by exact_mod_cast hm)) s hs
  simp only [gradedQuotDeg, ← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans_eq ?_
  rw [h2, Nat.factorial_succ]
  push_cast
  ring
end GlobalTheory.GradedBezout
