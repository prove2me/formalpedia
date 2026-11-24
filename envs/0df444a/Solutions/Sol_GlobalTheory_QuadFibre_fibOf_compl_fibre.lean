-- Prove2me | solution 1 for GlobalTheory.QuadFibre.fibOf_compl_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:44:59.035818+00:00
-- url     : https://prove2.me/submissions/e4ce6883-303a-4e06-8c06-17029ddf0abb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AveragedFibreMeasureComplFibreEqZero
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_ne
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ t : K, GlobalTheory.QuadFibre.fibOf μ ν q U s t (q ⁻¹' {t})ᶜ = 0 := by
  intro K V _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ q hq hh U s hs t
  obtain ⟨hUo, hUc, h1, hmul, hinv, hn, hsc, hsq⟩ := hs
  by_cases ht : t = 0
  · subst ht; rw [fibOf_zero]; rfl
  have hm : Measurable (fun x : V => s (t / q x) • x) := by
    have h1 : Measurable (fun x : V => s (t / q x)) :=
      hsc.measurable.comp (measurable_const.div hq.measurable)
    exact h1.smul measurable_id
  have hA : MeasurableSet (q ⁻¹' {t})ᶜ :=
    ((isClosed_singleton.preimage hq).measurableSet).compl
  rw [fibOf_ne _ _ _ _ _ ht, Measure.smul_apply, Measure.map_apply hm hA,
    Measure.restrict_apply (hm hA)]
  convert smul_zero _
  convert measure_empty (μ := μ)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, u, hu, hx2⟩
  apply hx1
  have hu0 : u ≠ 0 := by
    intro h
    have := hn u hu
    rw [h] at this
    simp at this
  have hx2' : q x = t * u := by simpa using hx2.symm
  have h3 : t / q x = u⁻¹ := by rw [hx2']; field_simp
  show q (s (t / q x) • x) = t
  rw [hh, h3, hsq _ (hinv u hu), hx2']
  field_simp
end GlobalTheory.QuadFibre
