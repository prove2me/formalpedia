-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_oneJump_unkilled_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:02:16.596247+00:00
-- url     : https://prove2.me/submissions/3a5371b6-46d1-4478-bd8b-e4cd58df18a4

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_finitePositiveLevyMeasureNormalizeV1
import Theorems.Thm_Kyprianou_Ch05_killedSubordinatorFiniteActivityCharV1
import Theorems.Thm_Kyprianou_Ch05_compoundPoissonOneJumpChunkLowerV1
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
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
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta))) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ a b : Real, 0 < a → a ≤ b →
      ∃ δ : Real, 0 < δ ∧ ∀ t ∈ Set.Ioc (0 : Real) δ,
        ENNReal.ofReal (3 * t / 4) * Pi (Set.Icc a b) ≤
          P {omega : Omega | Y (Real.toNNReal t) omega ∈
            {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}})
 := by
  intro hf a b ha hab
  by_cases hp : Pi (Ioi (0 : ℝ)) = 0
  · refine ⟨1,zero_lt_one,?_⟩
    intro t ht
    have hzero : Pi (Icc a b) = 0 :=
      measure_mono_null (fun x hx => ha.trans_le hx.1) hp
    rw [hzero,mul_zero]
    exact zero_le
  obtain ⟨r,F,hr,hF,hScale⟩ := finitePositiveLevyMeasureNormalizeV1 Pi
    hTriplet.2.2.1 hf (pos_iff_ne_zero.mpr hp)
  letI : IsProbabilityMeasure F := hF
  obtain ⟨O,m,Q,tau,M,hQ,hDriver⟩ := levy_foundations_compoundPoissonDriverExists r hr F
  letI : MeasurableSpace O := m
  letI : IsProbabilityMeasure Q := hQ
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1
  have hCP (t : NNReal) : AEMeasurable (LevyFoundations.compoundPoisson d tau M (t : ℝ)) Q := by
    apply AEMeasurable.of_map_ne_zero
    intro hz
    have hc := levy_foundations_compoundPoissonCharFun hDriver hr d t 0
    rw [hz,MeasureTheory.charFun_zero_measure] at hc
    simp at hc
  have hLaw (t : NNReal) :
      P.map (Y t) = Q.map (LevyFoundations.compoundPoisson d tau M (t : ℝ)) := by
    letI : IsProbabilityMeasure (P.map (Y t)) := Measure.isProbabilityMeasure_map (hm t)
    letI : IsProbabilityMeasure (Q.map (LevyFoundations.compoundPoisson d tau M (t : ℝ))) :=
      Measure.isProbabilityMeasure_map (hCP t)
    apply Measure.ext_of_charFun
    funext u
    rw [killedSubordinatorFiniteActivityCharV1 P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw r F hScale t u,
      levy_foundations_compoundPoissonCharFun hDriver hr d t u]
  obtain ⟨delta,hdelta,hbound⟩ := compoundPoissonOneJumpChunkLowerV1 Q r hr F tau M hDriver
    (levy_foundations_compoundPoissonJumpCountLaw hDriver hr) d a b ha hab
  refine ⟨delta,hdelta,?_⟩
  intro t ht
  let B : Set ℝ := {z | ∃ y ∈ Icc a b, z = d*t+y}
  have hB : MeasurableSet B := by
    have he : B = (fun z : ℝ => z-d*t) ⁻¹' Icc a b := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩
        simpa only [mem_preimage,add_sub_cancel_left] using hy
      · intro hz
        exact ⟨z-d*t,hz,by ring⟩
    rw [he]
    exact measurableSet_Icc.preimage (by fun_prop)
  have ht' : ((Real.toNNReal t : NNReal) : ℝ) = t := Real.coe_toNNReal t ht.1.le
  have h := congrArg (fun mu : Measure ℝ => mu B) (hLaw (Real.toNNReal t))
  rw [Measure.map_apply_of_aemeasurable (hm _) hB,Measure.map_apply_of_aemeasurable (hCP _) hB,ht'] at h
  rw [hScale]
  exact (hbound t ht).trans_eq h.symm
