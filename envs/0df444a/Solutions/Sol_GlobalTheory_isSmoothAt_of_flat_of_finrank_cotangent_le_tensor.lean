-- Prove2me | solution 1 for GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangent_le_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:11.557204+00:00
-- url     : https://prove2.me/submissions/08c77b0b-7f4e-4bed-8b35-e6261cad286b

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
theorem _root_.solution (k : Type*) [Field k] [Algebra V k]
    (hk : Function.Surjective (algebraMap V k)) {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), ringKrullDim ((K ⊗[V] A) ⧸ p) = d)
    (x : Ideal (k ⊗[V] A)) [x.IsMaximal]
    (hx : Module.finrank ((k ⊗[V] A) ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V
        (x.comap (Algebra.TensorProduct.includeRight : A →ₐ[V] k ⊗[V] A).toRingHom) ∧
      (∃ f ∉ x.comap (Algebra.TensorProduct.includeRight : A →ₐ[V] k ⊗[V] A).toRingHom,
        Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank ((k ⊗[V] A) ⧸ x) x.Cotangent = d :=
  isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K (fun p hp ↦ (hd p hp).ge) _
    (TensorProduct.mk_surjective V A k hk) (ker_includeRight_of_surjective V k hk) x hx
end GlobalTheory
