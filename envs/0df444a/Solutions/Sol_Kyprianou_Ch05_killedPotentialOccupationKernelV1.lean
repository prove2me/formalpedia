-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotentialOccupationKernelV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:09:16.737127+00:00
-- url     : https://prove2.me/submissions/0612b3aa-2bdb-48bc-8def-d5b4826fc346
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula
import Theorems.Thm_Kyprianou_Ch05_jumpPotentialKernelMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_killedPotentialSurvivalFactorGeneralV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
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
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : ℝ → Measure ℝ) (hPotential : IsKilledPotentialFamily P Y death U)
    [SigmaFinite Pi]
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x) :
    jumpPotentialKernel (U 0) Pi x A B = ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
      (∫⁻ v, (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
          ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
        else 0) v ∂(P.map (Y (Real.toNNReal t)))) ∂volume := by
  classical
  let f : ℝ → ENNReal := (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0)
  obtain ⟨hf,hK⟩ := jumpPotentialKernelMeasurableV1 (U 0) Pi x A B hA hB
  change Measurable f at hf
  change jumpPotentialKernel (U 0) Pi x A B = ∫⁻ v, f v ∂(U 0) at hK
  rw [hK,killedPotential_lintegral_formula P Y death eta d Pi Phi hKilled hTriplet
    hLaplaceLaw U hPotential 0 le_rfl f hf]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [killedPotentialSurvivalFactorGeneralV1 P Y death eta hKilled f hf t ht]
  simp only [neg_zero,zero_mul,Real.exp_zero,ENNReal.ofReal_one,one_mul]
  rfl
