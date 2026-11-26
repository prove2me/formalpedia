-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49CounterexampleFromSpikeExtensionV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:54:10.56122+00:00
-- url     : https://prove2.me/submissions/58237240-8de5-4d6c-801c-65eb136ed7e6

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedLevyV3
import Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedMarginalLawV3
import Theorems.Thm_Kyprianou_Ch04_exercise49EmbeddedAsymptoticsV3
import Theorems.Thm_Kyprianou_Ch04_exercise49NullSumSpikeNoRepV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : ℝ)
    (hDrift : drift = triplet.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSub : ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)))
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop)
    {E : Type} [MeasurableSpace E] (a : E → NNReal)
    (ha : ∀ e, 0 < a e) (hBad : ¬ MeasurableSet {e | a e ≤ 1}) :
    ¬ certificate_ex4_9_iii := by
  classical
  intro hCert
  let j : Ω → Ω ⊕ E := Sum.inl
  have hj : MeasurableEmbedding j :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs => hs.inl_image⟩
  let Q : Measure (Ω ⊕ E) := P.map j
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hj.measurable.aemeasurable
  let Y (t : NNReal) : Ω ⊕ E → ℝ := Sum.elim (X t)
    (fun e => if t = a e then -1 else 0)
  have hY0 : Y 0 = fun _ => 0 := by
    funext w
    cases w with
    | inl w => exact congrFun hLevy.start_zero w
    | inr e => simp [Y,ne_of_lt (ha e)]
  have hAgree (t : NNReal) (w : Ω) : Y t (j w) = X t w := rfl
  have hY := exercise49EmbeddedLevyV3 P j hj X Y hLevy hY0 hAgree
  have hLaw (t : NNReal) (theta : ℝ) :
      charFun (Q.map (Y t)) theta =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent triplet theta) := by
    rw [show Q.map (Y t) = P.map (X t) from exercise49EmbeddedMarginalLawV3 P j hj X Y hLevy hAgree t]
    exact hTriplet t theta
  obtain ⟨hn,hi⟩ := exercise49EmbeddedAsymptoticsV3 P j hj X Y hAgree hNotSub hInfinity
  unfold certificate_ex4_9_iii at hCert
  obtain ⟨_,_,f,hf,hfEq,_⟩ := hCert Q Y hY triplet hLaw hBV drift hDrift hd hn hi
  apply exercise49NullSumSpikeNoRepV3 Y a ha hBad (fun _ _ => rfl)
  exact ⟨f,hf,by simpa only [zero_add] using hfEq⟩
