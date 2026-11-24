-- Prove2me | solution 1 for GlobalTheory.ThetaCone.eq_zero_or_eq_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:59.963514+00:00
-- url     : https://prove2.me/submissions/c6925efd-822c-4624-98b9-bff1dd99cf30

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaCone
theorem _root_.solution [FiniteDimensional ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : ∀ z, f z * g z = 0) :
    (∀ z, f z = 0) ∨ ∀ z, g z = 0 := by
  by_cases hf0 : ∀ z, f z = 0
  · exact Or.inl hf0
  right
  simp only [not_forall] at hf0
  obtain ⟨a, ha⟩ := hf0

  have hev : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne ha] with z hz
    exact (mul_eq_zero.mp (h z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hg Set.univ
  have hzero := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ a) hev
  exact fun z => hzero (Set.mem_univ z)
end GlobalTheory.ThetaCone
