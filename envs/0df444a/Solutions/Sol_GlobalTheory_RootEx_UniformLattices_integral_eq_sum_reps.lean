-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.integral_eq_sum_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:38.459258+00:00
-- url     : https://prove2.me/submissions/48cf2e24-9f5a-4e57-8f0d-8a282ee93f94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
    {D B : AddSubgroup V} (hBD : B ≤ D) (hB : IsOpen (B : Set V)) (hBc : IsCompact (B : Set V))
    {T : Finset V} (hT : IsReps D B T) (f : V → ℂ) (h0 : ∀ β, β ∉ D → f β = 0)
    (h1 : ∀ β, ∀ b ∈ B, f (β + b) = f β) :
    ∫ β, f β ∂m = ((m.real (B : Set V) : ℝ) : ℂ) * ∑ t ∈ T, f t := by
  have hm : ∀ t : V, MeasurableSet ((fun β => -t + β) ⁻¹' (B : Set V)) := fun t =>
    (hB.preimage (by fun_prop)).measurableSet
  have e : ∀ β, f β = ∑ t ∈ T, ((fun β => -t + β) ⁻¹' (B : Set V)).indicator (fun _ => f t) β := by
    intro β
    by_cases hβ : β ∈ D
    · obtain ⟨t, ⟨ht, hb⟩, hu⟩ := hT.2 β hβ
      rw [Finset.sum_eq_single_of_mem t ht, Set.indicator_of_mem (by simpa [neg_add_eq_sub] using hb),
        ← h1 t _ hb, add_sub_cancel]
      intro t' ht' hne
      exact Set.indicator_of_notMem (fun h => hne (hu t' ⟨ht', by simpa [neg_add_eq_sub] using h⟩)) _
    · rw [h0 β hβ]
      refine (Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (fun h => hβ ?_) _).symm
      simpa using add_mem (hT.1 t ht) (hBD h)
  rw [integral_congr_ae (Eventually.of_forall e), integral_finset_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hm t), Measure.real, measure_preimage_add, Complex.real_smul]
    rfl
  · intro t _
    refine (integrable_indicator_iff (hm t)).2 (integrableOn_const ?_)
    rw [measure_preimage_add]
    exact hBc.measure_lt_top.ne
end GlobalTheory.RootEx.UniformLattices
