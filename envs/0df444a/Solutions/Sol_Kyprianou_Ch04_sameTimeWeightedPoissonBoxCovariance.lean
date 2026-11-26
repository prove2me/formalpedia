-- Prove2me | solution 1 for Kyprianou.Ch04.sameTimeWeightedPoissonBoxCovariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:13.899895+00:00
-- url     : https://prove2.me/submissions/85a88d68-e49a-4c52-9700-aceae6039988

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_weightedOverlapCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_signedWeightProductIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Same-window weighted covariance equals the variance on the intersection. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (a t : NNReal) (hat : a ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F a] W) (hWi : Integrable W P) :
    (∫ ω, W ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω *
      N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ B) ω ∂P) =
    (∫ ω, W ω ∂P) *
      (referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  let I := Set.Ioc (a : ℝ) (t : ℝ)
  let C := fun D : Set ℝ => fun ω => N.compensated (I ×ˢ D) ω
  let U := A \ B
  let V := A ∩ B
  let Z := B \ A
  have hsub (D E : Set ℝ) (h : D ⊆ E) :
      I ×ˢ D ⊆ I ×ˢ E := fun z hz => ⟨hz.1, h hz.2⟩
  have hUf := ne_top_of_le_ne_top hAf (measure_mono (hsub U A Set.sdiff_subset))
  have hVf := ne_top_of_le_ne_top hAf (measure_mono (hsub V A Set.inter_subset_left))
  have hZf := ne_top_of_le_ne_top hBf (measure_mono (hsub Z B Set.sdiff_subset))
  have hU : MeasurableSet U := hA.diff hB
  have hV : MeasurableSet V := hA.inter hB
  have hZ : MeasurableSet Z := hB.diff hA
  have dUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 hy.2
  have dUZ : Disjoint U Z := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 hy.1
  have dVZ : Disjoint V Z := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.2 hx.1
  have dprod (D E : Set ℝ) (h : Disjoint D E) :
      Disjoint (I ×ˢ D) (I ×ˢ E) :=
    Set.disjoint_left.mpr (fun z hz hz' => Set.disjoint_left.mp h hz.2 hz'.2)
  have uA : (I ×ˢ U) ∪ (I ×ˢ V) = I ×ˢ A := by
    ext z
    simp only [U, V, Set.mem_union, Set.mem_prod, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have uB : (I ×ˢ V) ∪ (I ×ˢ Z) = I ×ˢ B := by
    ext z
    simp only [V, Z, Set.mem_union, Set.mem_prod, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hX : C A =ᵐ[P] fun ω => C U ω + C V ω := by
    simpa only [uA, C] using Kyprianou.Ch04.compensatedDisjointUnionAE N
      (A := I ×ˢ U) (B := I ×ˢ V) (measurableSet_Ioc.prod hU) (measurableSet_Ioc.prod hV)
      (dprod U V dUV) hUf hVf
  have hY : C B =ᵐ[P] fun ω => C V ω + C Z ω := by
    simpa only [uB, C] using Kyprianou.Ch04.compensatedDisjointUnionAE N
      (A := I ×ˢ V) (B := I ×ˢ Z) (measurableSet_Ioc.prod hV) (measurableSet_Ioc.prod hZ)
      (dprod V Z dVZ) hVf hZf
  have hs (D : Set ℝ) (hm : MeasurableSet D)
      (hf : referenceIntensity ν (I ×ˢ D) ≠ ⊤) :=
    Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
      P ν F N hFuture a t hat D hm hf W hW hWi
  have hm (D : Set ℝ) (hD : MeasurableSet D) : AEStronglyMeasurable (C D) P :=
    ((ENNReal.measurable_toReal.comp
      (N.measurable_eval (measurableSet_Ioc.prod hD))).sub_const _).aestronglyMeasurable
  have hprod (D E : Set ℝ) (hD : MeasurableSet D) (hE : MeasurableSet E)
      (hDf : referenceIntensity ν (I ×ˢ D) ≠ ⊤)
      (hEf : referenceIntensity ν (I ×ˢ E) ≠ ⊤) :=
    Kyprianou.Ch04.signedWeightProductIntegrable P W (C D) (C E)
      hWi.aestronglyMeasurable (hm D hD) (hm E hE)
      (hs D hD hDf).1 (hs E hE hEf).1
  have hz (D E : Set ℝ) (hD : MeasurableSet D) (hE : MeasurableSet E)
      (hd : Disjoint D E) (hDf : referenceIntensity ν (I ×ˢ D) ≠ ⊤)
      (hEf : referenceIntensity ν (I ×ˢ E) ≠ ⊤) :=
    Kyprianou.Ch04.sameTimeWeightedPoissonBoxCrossZero P ν F N hFuture
      a t hat D E hD hE hd hDf hEf W hW hWi
  change (∫ ω, W ω * C A ω * C B ω ∂P) = _
  rw [Kyprianou.Ch04.weightedOverlapCovarianceExpansion P W (C A) (C B) (C U) (C V) (C Z)
    hX hY (hprod U V hU hV hUf hVf) (hprod U Z hU hZ hUf hZf)
    (hprod V Z hV hZ hVf hZf) (hs V hV hVf).1
    (hz U V hU hV dUV hUf hVf) (hz U Z hU hZ dUZ hUf hZf)
    (hz V Z hV hZ dVZ hVf hZf)]
  exact (hs V hV hVf).2
