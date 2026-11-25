-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:08.936894+00:00
-- url     : https://prove2.me/submissions/afc9191f-33a5-4ae3-8284-5870f147c670

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_germIdeal_eq_span
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff_le_order
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
theorem _root_.solution {J : Ideal (MvPowerSeries σ R)} {N : ℕ}
    (h : Ideal.span (Set.range X) ^ N ≤ J) : Module.Finite R (MvPowerSeries σ R ⧸ J) := by
  refine Module.Finite.of_surjective (((Ideal.Quotient.mkₐ R J).comp
    (MvPolynomial.coeToMvPowerSeries.algHom R)).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ R N).subtype) fun y => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨⟨truncTotal (N + 1) g, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
    (Nat.le_of_lt_succ (totalDegree_truncTotal_lt _ N.succ_ne_zero))⟩, ?_⟩
  refine Ideal.Quotient.eq.2 (h ?_)
  rw [← germIdeal_eq_span, mem_germIdeal_pow_iff_le_order]
  refine nat_le_order fun d hd => ?_
  simp [coeff_truncTotal _ (Nat.lt_succ_of_lt hd)]
end GlobalTheory.FormalIsogeny
