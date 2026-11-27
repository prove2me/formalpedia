-- Prove2me | solution 1 for GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:09.47705+00:00
-- url     : https://prove2.me/submissions/a795d646-ccd2-4da2-8c10-c86e32b31185

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
variable (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Type u} [CommRing A] [Algebra V A] [Algebra.FiniteType V A] [Module.Flat V A]
namespace GlobalTheory
theorem _root_.solution {ϖ : V} (hϖ : Irreducible ϖ) {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), ringKrullDim ((K ⊗[V] A) ⧸ p) = d)
    (x : Ideal (A ⧸ Ideal.span {algebraMap V A ϖ})) [x.IsMaximal]
    (hx : Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V (x.comap (Ideal.Quotient.mk _)) ∧
      (∃ f ∉ x.comap (Ideal.Quotient.mk _),
        Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent = d :=
  isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K (fun p hp ↦ (hd p hp).ge) _
    Ideal.Quotient.mk_surjective
    (Ideal.mk_ker.trans (map_maximalIdeal_eq_span_of_irreducible V hϖ).symm) x hx
end GlobalTheory
