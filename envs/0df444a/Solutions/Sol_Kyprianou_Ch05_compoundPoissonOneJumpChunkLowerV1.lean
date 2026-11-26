-- Prove2me | solution 1 for Kyprianou.Ch05.compoundPoissonOneJumpChunkLowerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:02:15.405909+00:00
-- url     : https://prove2.me/submissions/b7250cc8-8a3f-4285-a499-bacd8912135b

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_compoundPoissonCountOneMarkedMassV1
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (r : NNReal) (hr : 0 < r) (F : Measure ℝ) [IsProbabilityMeasure F]
    (tau M : ℕ → Omega → ℝ)
    (hDriver : LevyFoundations.IsCompoundPoissonDriver tau M r F P)
    (hCount : ∀ t : NNReal,
      P.map (fun w => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival tau n w) (t : ℝ)) = poissonMeasure (r*t))
    (d a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Ioc (0 : ℝ) delta,
      ENNReal.ofReal (3*t/4) * ((r : ENNReal) • F) (Icc a b) ≤
        P {w | LevyFoundations.compoundPoisson d tau M t w ∈
          {z : ℝ | ∃ y ∈ Icc a b, z = d*t+y}} := by
  classical
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  refine ⟨1/(4*(r : ℝ)),by positivity,?_⟩
  intro t ht
  let E : Set Omega := {w | LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival tau n w) t = 1 ∧ M 0 w ∈ Icc a b}
  have hmass : P E = ENNReal.ofReal (Real.exp (-(r:ℝ)*t) * ((r:ℝ)*t)) * F (Icc a b) :=
    Kyprianou.Ch05.compoundPoissonCountOneMarkedMassV1 P r hr F tau M hDriver hCount
      t ht.1.le (Icc a b) measurableSet_Icc
  have hsubset : E ⊆ {w | LevyFoundations.compoundPoisson d tau M t w ∈
        {z : ℝ | ∃ y ∈ Icc a b, z = d*t+y}} := by
    intro w hw
    refine ⟨M 0 w,hw.2,?_⟩
    unfold LevyFoundations.compoundPoisson LevyFoundations.piecewisePath
    rw [hw.1]
    simp
  have hrt : (r:ℝ)*t ≤ 1/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(r:ℝ) by positivity)).mp ht.2
    linarith
  have hsurv : (3:ℝ)/4 ≤ Real.exp (-(r:ℝ)*t) := by
    have hh := Real.add_one_le_exp (-(r:ℝ)*t)
    linarith
  have hc : ENNReal.ofReal (3*t/4) * (r:ENNReal) ≤
      ENNReal.ofReal (Real.exp (-(r:ℝ)*t) * ((r:ℝ)*t)) := by
    have ht0 : 0 ≤ 3*t/4 := by linarith [ht.1]
    have he : ENNReal.ofReal (3*t/4) * (r:ENNReal) =
        ENNReal.ofReal ((3*t/4)*(r:ℝ)) := by
      rw [ENNReal.ofReal_mul ht0,ENNReal.ofReal_coe_nnreal]
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg (sub_nonneg.mpr hsurv) (mul_nonneg hrR.le ht.1.le)]
  calc
    _ = (ENNReal.ofReal (3*t/4) * (r:ENNReal)) * F (Icc a b) := by
      rw [Measure.smul_apply]
      simp only [smul_eq_mul,mul_assoc]
    _ ≤ P E := by
      rw [hmass]
      exact mul_le_mul_of_nonneg_right hc zero_le
    _ ≤ _ := measure_mono hsubset
