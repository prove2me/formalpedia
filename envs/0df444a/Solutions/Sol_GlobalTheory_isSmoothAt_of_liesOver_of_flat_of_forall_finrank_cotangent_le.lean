-- Prove2me | solution 1 for GlobalTheory.isSmoothAt_of_liesOver_of_flat_of_forall_finrank_cotangent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:28.092088+00:00
-- url     : https://prove2.me/submissions/346272cc-0ce8-49f5-baad-6625296d7c39

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
theorem _root_.solution {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A))
    (hx : ∀ x : Ideal B, x.IsMaximal → Module.finrank (B ⧸ x) x.Cotangent ≤ d)
    (q : Ideal A) [q.IsPrime] [q.LiesOver (maximalIdeal V)] :
    Algebra.IsSmoothAt V q ∧
      ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f) := by
  have hkq : RingHom.ker φ ≤ q := by
    rw [hker, Ideal.map_le_iff_le_comap]
    exact (q.over_def (maximalIdeal V)).le
  have hprime : (q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hkq
  obtain ⟨x, hxm, hqx⟩ := Ideal.exists_le_maximal _ hprime.ne_top
  obtain ⟨-, ⟨f, hf, hs⟩, -⟩ :=
    isSmoothAt_of_flat_of_finrank_cotangent_le_of_surjective V K hd φ hφ hker x (hx x hxm)
  have hfq : f ∉ q := fun h ↦ hf (Ideal.map_le_iff_le_comap.mp hqx h)
  refine ⟨?_, f, hfq, hs⟩
  have : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.IsStandardSmooth V (Localization.Away f) := hs.isStandardSmooth d
  exact (Algebra.basicOpen_subset_smoothLocus_iff (R := V) (f := f)).mpr inferInstance
    (show (⟨q, ‹_›⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen f from hfq)
end GlobalTheory
