-- Prove2me | solution 1 for GlobalTheory.eigenMult_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:05.536331+00:00
-- url     : https://prove2.me/submissions/544bbf6f-ddb8-4bb8-ab24-346892b1452a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
import Theorems.Thm_GlobalTheory_TraceSpread_map_trace
import Theorems.Thm_GlobalTheory_TraceSpread_finrank_iff_trace
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q n : ℕ) (R : Type) [CommRing R] [IsReduced R]
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R), r ^ 2 = -(H.d : R) →
    Dense {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K)
      (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)), RingHom.ker f = P.asIdeal ∧
      (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q)} →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K)
      (M' : 𝓞 E →+* Module.End K (Fin n → K)), (∀ a c, f ∘ M a c = M' a (f ∘ c)) →
      ∀ τ : 𝓞 E →+* K,
        (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
        (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q) := by
  intro E _ _ _ H p q n R _ _ M r hr hdense K _ _ _ f M' hfM
  let X : 𝓞 E → R := fun a => 2 * r * LinearMap.trace R _ (M a) -
    ((p + q) * r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : R) +
      (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : R))
  have hfX : ∀ (K₁ : Type) [Field K₁] (f₁ : R →+* K₁)
      (M₁ : 𝓞 E →+* Module.End K₁ (Fin n → K₁)), (∀ a c, f₁ ∘ M a c = M₁ a (f₁ ∘ c)) →
      ∀ a, f₁ (X a) = 2 * f₁ r * LinearMap.trace K₁ _ (M₁ a) -
        ((p + q) * f₁ r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K₁) +
          (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K₁)) := by
    intro K₁ _ f₁ M₁ h₁ a
    simp only [X, map_sub, map_add, map_mul, map_natCast, map_intCast, map_ofNat]
    rw [_root_.GlobalTheory.TraceSpread.map_trace f₁ (M a) (M₁ a) (h₁ a)]
  have hX : ∀ a, X a = 0 := by
    intro a
    have hsub : {P : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
        (_ : CharZero K) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K)),
        RingHom.ker f = P.asIdeal ∧ (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ τ : 𝓞 E →+* K,
          (τ H.rt = f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = p) ∧
          (τ H.rt ≠ f r → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub M' τ) = q)} ⊆
        PrimeSpectrum.zeroLocus {X a} := by
      rintro P ⟨K₁, _, _, _, f₁, M₁, hker, hcomp, hmult⟩
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, ← hker,
        RingHom.mem_ker, hfX K₁ f₁ M₁ hcomp a]
      have hs : f₁ r ^ 2 = -(H.d : K₁) := by rw [← map_pow, hr, map_neg, map_natCast]
      have := (_root_.GlobalTheory.TraceSpread.finrank_iff_trace H p q M₁ (f₁ r) hs).mp hmult a
      rw [this]; ring
    have hall := closure_minimal hsub (PrimeSpectrum.isClosed_zeroLocus _)
    rw [hdense.closure_eq] at hall
    have hnil : IsNilpotent (X a) := nilpotent_iff_mem_prime.mpr fun J hJ => by
      have := hall (Set.mem_univ ⟨J, hJ⟩)
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at this
      exact this
    exact hnil.eq_zero
  have hs : f r ^ 2 = -(H.d : K) := by rw [← map_pow, hr, map_neg, map_natCast]
  refine (_root_.GlobalTheory.TraceSpread.finrank_iff_trace H p q M' (f r) hs).mpr fun a => ?_
  have h₀ := hfX K f M' hfM a
  rw [hX a, map_zero] at h₀
  linear_combination -h₀
end _root_.GlobalTheory
