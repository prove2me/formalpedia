-- Prove2me | solution 1 for Kyprianou.Ch04.poissonWindowNonnegativeIntegrableAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:28:28.584556+00:00
-- url     : https://prove2.me/submissions/baf8c528-7d31-4401-aca2-1668a7550ee6

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
import Theorems.Thm_Kyprianou_Ch04_poissonZeroTimeSliceV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Nonnegative integrable marks have a pathwise integrable physical integral on every compact clock. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (g : ℝ → ℝ)
    (hg : Measurable g) (hn : ∀ x, 0 ≤ g x) (hi : Integrable g ν) :
    ∀ᵐ w ∂P, ∀ T : NNReal,
      IntegrableOn (fun z : ℝ × ℝ => g z.2) (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) (N.N w) := by
  have hpos (n : ℕ) : ∀ᵐ w ∂P,
      IntegrableOn (fun z : ℝ × ℝ => g z.2)
        (Ioc (0 : ℝ) ((n+1 : ℕ) : ℝ) ×ˢ univ) (N.N w) := by
    let T : NNReal := (n+1 : ℕ)
    let A := Ioc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    let R : Ω → Measure (ℝ × ℝ) := fun w => (N.N w).restrict A
    have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
    have hm : Measurable R := Measure.measurable_of_measurable_coe R fun s hs => by
      simpa only [R,Measure.restrict_apply hs] using N.measurable_eval (hs.inter hA)
    have h := (Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1 P ν N
      g hg hn T (by dsimp [T]; positivity)).2 hi
    have hme := (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp (hg.comp measurable_snd))).comp hm
    have hfin := ae_lt_top hme h.ne
    filter_upwards [hfin] with w hw
    change (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (g z.2) ∂(R w)) < ⊤ at hw
    have hi' : Integrable (fun z : ℝ × ℝ => g z.2) (R w) :=
      ⟨(hg.comp measurable_snd).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z : ℝ × ℝ => hn z.2)).2 hw⟩
    simpa [R,A,T,IntegrableOn] using hi'
  filter_upwards [ae_all_iff.mpr hpos,(Kyprianou.Ch04.poissonZeroTimeSliceV1 P ν N).2]
    with w hw hz
  intro T
  obtain ⟨n,hnT⟩ := exists_nat_ge T
  have hEq : (N.N w).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) =
      (N.N w).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ univ) := by
    apply Measure.restrict_congr_set
    have hnull : ∀ᵐ z ∂(N.N w), z ∉ ({0} : Set ℝ) ×ˢ (univ : Set ℝ) :=
      ae_iff.mpr (by simpa only [not_not, setOf_mem_eq] using hz)
    filter_upwards [hnull] with z hz'
    have hne : z.1 ≠ 0 := by simpa using hz'
    apply propext
    change z ∈ Icc (0 : ℝ) (T : ℝ) ×ˢ univ ↔ z ∈ Ioc (0 : ℝ) (T : ℝ) ×ˢ univ
    simp [mem_prod,mem_Icc,mem_Ioc,le_iff_lt_or_eq,hne,Ne.symm hne]
  unfold IntegrableOn
  rw [hEq]
  exact (hw n).mono_set (prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast
    (hnT.trans (by simp : (n : NNReal) ≤ ((n+1 : ℕ) : NNReal))))) subset_rfl)
