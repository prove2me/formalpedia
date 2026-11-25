-- Prove2me | solution 1 for Kyprianou.Ch04.sameTimeWeightedPoissonBoxCrossZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:59:40.506381+00:00
-- url     : https://prove2.me/submissions/678d3b8a-bba3-49bf-a2b1-e3a0f26143eb

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pastWeightedPoissonBoxSquareMoment
import Theorems.Thm_Kyprianou_Ch04_compensatedDisjointUnionAE
import Theorems.Thm_Kyprianou_Ch04_signedWeightSquarePolarization
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Disjoint mark cells sharing a time interval are orthogonal with signed past weights. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B)
    (hAfin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBfin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F u] W) (hWi : Integrable W P) :
    (∫ ω, W ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ A) ω *
      N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω ∂P) = 0 := by
  let I := Set.Ioc (u : ℝ) (t : ℝ)
  have hdisj : Disjoint (I ×ˢ A) (I ×ˢ B) :=
    Set.disjoint_left.mpr (fun z hz hz' => Set.disjoint_left.mp hd hz.2 hz'.2)
  have hu : referenceIntensity ν (I ×ˢ (A ∪ B)) =
      referenceIntensity ν (I ×ˢ A) + referenceIntensity ν (I ×ˢ B) := by
    rw [Set.prod_union, measure_union hdisj (measurableSet_Ioc.prod hB)]
  have hufin : referenceIntensity ν (I ×ˢ (A ∪ B)) ≠ ⊤ := by
    rw [hu]
    exact ENNReal.add_ne_top.mpr ⟨hAfin,hBfin⟩
  obtain ⟨hiA, heA⟩ := Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
    P ν F N hFuture u t hut A hA hAfin W hW hWi
  obtain ⟨hiB, heB⟩ := Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
    P ν F N hFuture u t hut B hB hBfin W hW hWi
  obtain ⟨hiC, heC⟩ := Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
    P ν F N hFuture u t hut (A ∪ B) (hA.union hB) hufin W hW hWi
  let X := fun ω => N.compensated (I ×ˢ A) ω
  let Y := fun ω => N.compensated (I ×ˢ B) ω
  let Z := fun ω => N.compensated (I ×ˢ (A ∪ B)) ω
  have hAdd : Z =ᵐ[P] (fun ω => X ω + Y ω) := by
    simpa only [Z, X, Y, Set.prod_union] using
      Kyprianou.Ch04.compensatedDisjointUnionAE N
        (measurableSet_Ioc.prod hA) (measurableSet_Ioc.prod hB) hdisj hAfin hBfin
  have hVar : (∫ ω, W ω * (Z ω)^2 ∂P) =
      (∫ ω, W ω * (X ω)^2 ∂P) + (∫ ω, W ω * (Y ω)^2 ∂P) := by
    rw [show (∫ ω, W ω * (Z ω)^2 ∂P) = _ from heC,
      show (∫ ω, W ω * (X ω)^2 ∂P) = _ from heA,
      show (∫ ω, W ω * (Y ω)^2 ∂P) = _ from heB]
    change (∫ ω, W ω ∂P) * (referenceIntensity ν (I ×ˢ (A ∪ B))).toReal = _
    rw [hu, ENNReal.toReal_add hAfin hBfin, mul_add]
  exact Kyprianou.Ch04.signedWeightSquarePolarization P W X Y Z hiA hiB hiC hAdd hVar
