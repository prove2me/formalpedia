-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.flat_injective_basis_of_finiteReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:06:07.890281+00:00
-- url     : https://prove2.me/submissions/b73dd2d0-4e98-4b0f-b2d7-9834ece2507e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_isRegularLocalRing_mvPowerSeries
import Theorems.Thm_GlobalTheory_FormalIsogeny_ringKrullDim_mvPowerSeries
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finiteReduction
import Theorems.Thm_GlobalTheory_FormalIsogeny_isLocalHom_of_constantCoeff_mem
import Theorems.Thm_GlobalTheory_FormalIsogeny_flat_injective_basis_of_finite

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
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {σ τ : Type*} [Finite σ] [Finite τ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) (h : FiniteReduction fun j => φ (X j))
    (hc : Nat.card τ ≤ Nat.card σ) :
    φ.toRingHom.Flat ∧ Function.Injective φ ∧
      @Module.Free (MvPowerSeries τ R) (MvPowerSeries σ R) _ _ φ.toRingHom.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → MvPowerSeries σ R),
        ∀ g, ∃! c : Fin n → MvPowerSeries τ R, g = ∑ i, φ (c i) * e i := by
  have := isRegularLocalRing_mvPowerSeries R σ
  have := isRegularLocalRing_mvPowerSeries R τ
  have := isLocalHom_of_constantCoeff_mem φ h0
  refine flat_injective_basis_of_finite φ.toRingHom (finite_of_finiteReduction φ h0 h) ?_
  rw [ringKrullDim_mvPowerSeries, ringKrullDim_mvPowerSeries]
  gcongr
end GlobalTheory.FormalIsogeny
