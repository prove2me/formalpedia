-- Prove2me | solution 1 for GlobalTheory.isSmoothAt_of_finrank_cotangent_le_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:37.803314+00:00
-- url     : https://prove2.me/submissions/66e971f5-dfef-4ee3-9010-0c6082b088dc

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (k : Type*) [Field k] [PerfectField k]
    {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]
    {d : ℕ} (h₁ : (d : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m))
    (h₂ : Module.finrank (A ⧸ m) m.Cotangent ≤ d) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = d ∧
      Module.finrank (A ⧸ m) m.Cotangent = d ∧ Algebra.IsSmoothAt k m ∧
      Module.Free (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] ∧
      Module.finrank (Localization.AtPrime m) Ω[Localization.AtPrime m⁄k] = d := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have h₃ := finrank_cotangentSpace_le_finrank_cotangent m (Localization.AtPrime m)
  obtain ⟨h₄, h₅, h₆⟩ := isRegularLocalRing_of_finrank_cotangentSpace_le _ h₁ (h₃.trans h₂)
  have h₇ := formallySmooth_of_isRegularLocalRing_of_perfectField k (Localization.AtPrime m)
  have := formallyEtale_residueField_of_isMaximal k k m (Localization.AtPrime m)
  obtain ⟨h₈, h₉⟩ := free_and_finrank_kaehler_eq_finrank_cotangentSpace k (Localization.AtPrime m)
  exact ⟨h₄, h₅, h₂.antisymm (h₆ ▸ h₃), h₇, h₈, h₉.trans h₆⟩
end GlobalTheory
