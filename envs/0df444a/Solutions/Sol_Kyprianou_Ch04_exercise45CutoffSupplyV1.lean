-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffSupplyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:24:20.439455+00:00
-- url     : https://prove2.me/submissions/f41b5fa1-6a98-414c-9e61-bce5bfa3c081

import Theorems.Thm_Kyprianou_Ch04_exercise45CutoffLeftVersionV1
import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Ω → ℝ) (hLevy : IsLevyProcess X P)
    (triplet : LevyKhintchineTriple) [SigmaFinite triplet.levyMeasure]
    (Q : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure)
    (hQLaw : ∀ᵐ w ∂P, Q.N w = pathJumpMeasure X Xleft w)
    (hQ0 : ∀ w, Q.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0),
    let B := {x : ℝ | 1 ≤ |x|}
    let A (e : ℝ) := {x : ℝ | e < |x| ∧ |x| < 1}
    let V (t : NNReal) (w : Ω) := triplet.drift * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(Q.N w)
    let Y (e : ℝ) (t : NNReal) (w : Ω) := V t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ A e, z.2 ∂(Q.N w)) -
      (t : ℝ) * ∫ x in A e, x ∂triplet.levyMeasure
    ∃ L : ℝ → NNReal → Ω → ℝ,
      (∀ e w, 0 < e → e < 1 → Y e 0 w = X 0 w) ∧
      (∀ e : ℝ, 0 < e → e < 1 → ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
        Tendsto (fun s => Y e s w) (nhdsWithin t (Iio t)) (nhds (L e t w))) := by
  intro Ω m P hP X Xleft hLevy triplet hSigma Q hQLaw hQ0 B A V Y
  have hzero (w : Ω) (C : Set ℝ) :
      (∫ z in Icc (0 : ℝ) 0 ×ˢ C, z.2 ∂(Q.N w)) = 0 := by
    have hz : Q.N w (Icc (0 : ℝ) 0 ×ˢ C) = 0 :=
      measure_mono_null (by intro z hz; exact ⟨by simpa using hz.1,mem_univ _⟩) (hQ0 w)
    rw [Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
  have hInit : ∀ e w, 0 < e → e < 1 → Y e 0 w = X 0 w := by
    intro e w _ _
    rw [hLevy.start_zero]
    simp only [Y,V,NNReal.coe_zero,mul_zero,zero_mul,hzero,zero_add,add_zero,sub_zero]
  have hL (e : ℝ) (he : 0 < e) : ∃ L : NNReal → Ω → ℝ,
      ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
        Tendsto (fun s => Y e s w) (nhdsWithin t (Iio t)) (nhds (L t w)) :=
    exercise45CutoffLeftVersionV1 P triplet.levyMeasure triplet.levyMeasure_isLevyMeasure
      Q X Xleft V (Y e) triplet.drift e he hQLaw (fun _ _ => rfl) (fun _ _ => rfl)
  let L (e : ℝ) : NNReal → Ω → ℝ :=
    if h : 0 < e then Classical.choose (hL e h) else fun _ _ => 0
  have hLeftY : ∀ e : ℝ, 0 < e → e < 1 → ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y e s w) (nhdsWithin t (Iio t)) (nhds (L e t w)) := by
    intro e he _
    simpa only [L,dif_pos he] using Classical.choose_spec (hL e he)
  exact ⟨L,hInit,hLeftY⟩
