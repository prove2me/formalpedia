-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.exists_pow_le_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:54.856738+00:00
-- url     : https://prove2.me/submissions/e8f01b7d-a814-4b61-8cd1-fa247ca749c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {k : Type*} [Field k] {J : Ideal (MvPowerSeries σ k)}
    (h : Module.Finite k (MvPowerSeries σ k ⧸ J)) : ∃ N, Ideal.span (Set.range X) ^ N ≤ J := by
  have : IsArtinianRing (MvPowerSeries σ k ⧸ J) := IsArtinianRing.of_finite k _
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MvPowerSeries σ k ⧸ J)
  have h1 : (Ideal.span (Set.range X)).map (Ideal.Quotient.mk J) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Ideal.mem_jacobson_bot.2 fun y => ?_
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : IsUnit (X i * g + 1 : MvPowerSeries σ k) := by simp [isUnit_iff_constantCoeff]
    simpa using this.map (Ideal.Quotient.mk J)
  refine ⟨N, ?_⟩
  have h2 := Ideal.pow_right_mono h1 N
  rwa [hN, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_le_iff_le_comap,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h2
end GlobalTheory.FormalIsogeny
