-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.fiber_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:56.073538+00:00
-- url     : https://prove2.me/submissions/bbd1b4b1-08a6-4337-adc7-6143cee1ecde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_ind_mem
import Theorems.Thm_GlobalTheory_SplitWeil_HaarFactor_integrable_of_SB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : X₀ × A → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ z : X₀ × A, G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out))
    (x : X₀) : ∫ a, G (x, a) ∂μ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
  have he := integrable_of_SB μ (ind_mem hUo hUc)
  have hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  calc ∫ a, G (x, a) ∂μ
      = ∫ a, ∑ q ∈ T, G (x, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (a - q.out) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun a => hT (x, a))
    _ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
      rw [integral_finset_sum _ fun q _ => (he.comp_sub_right _).const_mul _]
      simp only [integral_const_mul, hshift, ← Finset.sum_mul]
end GlobalTheory.SplitWeil.HaarFactor
