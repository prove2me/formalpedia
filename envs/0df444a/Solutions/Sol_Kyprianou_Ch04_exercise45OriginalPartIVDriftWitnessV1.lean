-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45OriginalPartIVDriftWitnessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:21:41.074688+00:00
-- url     : https://prove2.me/submissions/7c6685d8-4735-4291-bdd1-6772bfb39f49

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45DeterministicDriftModelV1
import Theorems.Thm_Kyprianou_Ch04_exercise45BadLeftPathV1
import Theorems.Thm_Kyprianou_Ch04_exercise45ZeroTimeObstruction
import Theorems.Thm_Kyprianou_Ch04_exercise45ZeroIntensityPRM
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open Kyprianou.Ch04 Kyprianou.Ch03 Kyprianou.Ch01
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Specialise the obsolete certificate to the deterministic drift model. -/
theorem solution (h : Kyprianou.Ch04.certificate_ex4_5_ivV3) :
    letI m : MeasurableSpace ℕ := ⊥
    let P : Measure ℕ := Measure.dirac 0
    ∃ I : NNReal → ℕ → ℝ,
      (∀ᵐ w ∂P, ∀ t : NNReal, I t w = (t : ℝ)^2) ∧
      Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P
        (fun t _ => (t : ℝ))
        (fun s w => 2 * (if s = 0 then (w : ℝ) else (s : ℝ))) I := by
  classical
  unfold Kyprianou.Ch04.certificate_ex4_5_ivV3 at h
  letI m : MeasurableSpace ℕ := ⊥
  let P : Measure ℕ := Measure.dirac 0
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
  let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
  let tr : LevyKhintchineTriple := ⟨1,0,0,by simp [IsLevyMeasure]⟩
  letI : SigmaFinite tr.levyMeasure := by dsimp [tr]; infer_instance
  let F : Filtration NNReal m := ⊥
  obtain ⟨hX,htr,hF⟩ := Kyprianou.Ch04.exercise45DeterministicDriftModelV1
  obtain ⟨N,hN⟩ := Kyprianou.Ch04.exercise45ZeroIntensityPRM P
  obtain ⟨hLeft,hPath⟩ := Kyprianou.Ch04.exercise45BadLeftPathV1 P
  have hNLaw : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Y w := by
    filter_upwards [] with w
    exact (hN w).trans (hPath w).symm
  let f : ℝ → ℝ → ℝ := fun _ x => x^2
  let ft : ℝ → ℝ → ℝ := fun _ _ => 0
  let fx : ℝ → ℝ → ℝ := fun _ x => 2*x
  let fxx : ℝ → ℝ → ℝ := fun _ _ => 2
  have hX2 (t : NNReal) (w : ℕ) : X t w =
      tr.drift * (t : ℝ) + ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w) := by
    simp [X,tr,hN w]
  obtain ⟨M,stops,I,I2,hGrid,hSum,hUCP,hStop,hMono,hEx,hMart,hIto⟩ :=
    @h ℕ m P inferInstance F X hX tr inferInstance rfl htr hF N Y hLeft hNLaw
      f ft fx fxx (by intros; simp [ft,f]) (by intros; simp [fx,f,deriv_pow])
      (by intros; simp [fxx,fx,deriv_const_mul]) (by intro x; dsimp [f]; fun_prop)
      (by intro s; dsimp [f]; fun_prop)
      (by dsimp [f,ft,fx,fxx]; exact ⟨by fun_prop,by fun_prop,by fun_prop,by fun_prop⟩) X hX2
  have hI : ∀ᵐ w ∂P, ∀ t : NNReal, I t w = (t : ℝ)^2 := by
    filter_upwards [hIto] with w hw
    intro t
    simpa [f,ft,X,hN w] using (hw t).symm
  exact ⟨I,hI,hUCP⟩
