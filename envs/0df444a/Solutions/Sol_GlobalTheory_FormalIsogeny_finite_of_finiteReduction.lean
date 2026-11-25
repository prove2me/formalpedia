-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_of_finiteReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:43.10915+00:00
-- url     : https://prove2.me/submissions/5d4024c2-c1b4-43ef-9839-d1310d746801

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_maximalIdeal_iff_constantCoeff
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_finite_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
variable [Finite τ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) (h : FiniteReduction fun j => φ (X j)) :
    φ.toRingHom.Finite := by
  have h1 := h.finite_quotient
  have key : ∀ (A : Type _) [CommRing A] [Algebra R A] [Algebra A (MvPowerSeries σ R)]
      [IsScalarTower R A (MvPowerSeries σ R)] (I : Ideal A) [IsPrecomplete I A],
      I.map (algebraMap A (MvPowerSeries σ R)) = Ideal.span (Set.range fun j => φ (X j)) →
      Module.Finite A (MvPowerSeries σ R) := by
    intro A _ _ _ _ I _ hI
    have : IsHausdorff (I.map (algebraMap A (MvPowerSeries σ R))) (MvPowerSeries σ R) := by
      refine IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top ?_)
      rw [hI, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact mem_maximalIdeal_iff_constantCoeff.2 (h0 j)
    have : Module.Finite A (MvPowerSeries σ R ⧸ I.map (algebraMap A (MvPowerSeries σ R))) := by
      rw [hI]
      exact .of_restrictScalars_finite R _ _
    exact finite_of_finite_quotient_map I
  refine @key (MvPowerSeries τ R) _ _ φ.toRingHom.toAlgebra
    (@IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ _ φ.toRingHom.toAlgebra _ fun r => (φ.commutes r).symm)
    (Ideal.span (Set.range X)) _ ?_
  rw [Ideal.map_span, ← Set.range_comp]
  rfl
end GlobalTheory.FormalIsogeny
