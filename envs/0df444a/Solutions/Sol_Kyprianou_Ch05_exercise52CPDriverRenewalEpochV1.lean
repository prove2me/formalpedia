-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPDriverRenewalEpochV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:14:21.168175+00:00
-- url     : https://prove2.me/submissions/49f3c43f-22a1-467a-8db7-fb2e51da7e73

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Compound Poisson marks are independent renewal spacings. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hPos : F (Iic 0) = 0)
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    IsRenewalEpochProcess Q marks F := by
  classical
  have hi' := iIndepFun.precomp (g := (Sum.inr : ℕ → ℕ ⊕ ℕ))
    Sum.inr_injective hd.indep
  have hi : iIndepFun marks Q := hi'
  have hzero : F ({0} : Set ℝ) = 0 :=
    measure_mono_null (by intro z hz; have h : z = 0 := hz; simpa [h]) hPos
  refine ⟨hd.measurable_mark, fun n => (hd.law_mark n).map_eq,
    measure_mono_null Iio_subset_Iic_self hPos, ?_, ?_⟩
  · rw [hzero]
    exact zero_ne_one
  · intro n A B hA hB
    have hdis : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
    have hpair := iIndepFun.indepFun_finset (Finset.range n) {n}
      hdis hi hd.measurable_mark
    let phi : ((i : ↥(Finset.range n)) → ℝ) → ℝ := fun z => ∑ i, z i
    let psi : ((i : ↥({n} : Finset ℕ)) → ℝ) → ℝ := fun z =>
      z ⟨n, Finset.mem_singleton_self n⟩
    have hphi : Measurable phi := Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hpsi : Measurable psi := measurable_pi_apply _
    have he : phi ∘ (fun w (i : ↥(Finset.range n)) => marks i w) =
        renewalEpoch marks n := by
      funext w
      change (∑ i : ↥(Finset.range n), marks i w) = ∑ i ∈ Finset.range n, marks i w
      exact Finset.sum_attach (Finset.range n) (fun i => marks i w)
    have hn : psi ∘ (fun w (i : ↥({n} : Finset ℕ)) => marks i w) =
        marks n := rfl
    have h := hpair.comp hphi hpsi
    rw [he, hn] at h
    have hEq := h.measure_inter_preimage_eq_mul A B hA hB
    rw [← (hd.law_mark n).map_eq, Measure.map_apply (hd.measurable_mark n) hB]
    exact hEq
