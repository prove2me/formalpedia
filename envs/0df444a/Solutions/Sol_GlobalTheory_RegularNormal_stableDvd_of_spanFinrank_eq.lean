-- Prove2me | solution 1 for GlobalTheory.RegularNormal.stableDvd_of_spanFinrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:39.012498+00:00
-- url     : https://prove2.me/submissions/fa7f6a02-bc95-420c-a7bf-b9cd1ae4702e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Theorems.Thm_GlobalTheory_RegularNormal_StableDvd_of_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal
open ReciprocityTheory.CA.AB.RegA
namespace GlobalTheory.RegularNormal
theorem _root_.solution (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) = n → StableDvd R := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R _ _ hn
  have : IsDomain R := IsRegularLocalRing.isDomain R
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · have h0 := IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq
    intro a b I hb _ _
    refine IsUnit.dvd ?_
    by_contra hu
    have : b ∈ maximalIdeal R := hu
    rw [h0] at this
    exact hb this
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (zero_mem _)
  have hquot := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hxp : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    exact IsRegularLocalRing.isDomain _
  refine StableDvd.of_quotient hxp (IH _ ?_ _ rfl)
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have h2 : Submodule.spanFinrank (maximalIdeal R)
      = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  omega
end GlobalTheory.RegularNormal
