-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_localizationAway_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:00.63907+00:00
-- url     : https://prove2.me/submissions/ebedc675-2b19-4cfc-a8f3-40008bcf3eeb

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
open AlgebraicGeometry CategoryTheory Topology
namespace GlobalTheory
theorem _root_.solution (K : Type u) [Field K] {C : Type u} [CommRing C]
    [IsDomain C] [Algebra K C] [Algebra.FiniteType K C] {g : C} (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim C := by
  have hle : Submonoid.powers g ≤ nonZeroDivisors C := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  have : FaithfulSMul C (Localization.Away g) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic C (Localization.Away g) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers g)
  obtain ⟨e, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq K C
  rw [h₁]
  exact ringKrullDim_eq_of_trdeg_eq K _ ((trdeg_eq_of_isAlgebraic_top K C _).trans h₂)
end GlobalTheory
