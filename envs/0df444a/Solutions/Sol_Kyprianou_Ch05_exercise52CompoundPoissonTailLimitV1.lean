-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CompoundPoissonTailLimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:32:19.042302+00:00
-- url     : https://prove2.me/submissions/f6cb09ae-bacf-40c3-bd1c-5486ffc3888f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_levy_foundations_compoundPoissonDriverExists
import Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverRenewalEpochV1
import Theorems.Thm_Kyprianou_Ch05_exercise52CPPassageRenewalTransferV1
import Theorems.Thm_Kyprianou_Ch05_renewalJointOvershootUndershoot
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Apply the existing renewal limit to the canonical compound Poisson marks. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → ℝ) (deathX : Omega → WithTop NNReal)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hPos : F (Iic 0) = 0) (hNL : NonLatticeMeasure F)
    (hInt : Integrable (fun z : ℝ => z) F)
    (hX : IsKilledSubordinator P X deathX 0)
    (hCP : ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * X t omega) ∂P) =
        Real.exp (-(t : ℝ) * (∫ z in Ioi 0, (1 - Real.exp (-theta*z)) ∂F)))
    (hLeft : IsLeftLimitVersion P X Xleft) :
    ∀ u y : ℝ, 0 < u → 0 < y →
      Tendsto (fun x : ℝ => (P {omega : Omega |
        PassageFinite X deathX x omega ∧
        passageOvershoot X deathX x omega ∈ Ioi u ∧
        passageUndershoot X Xleft deathX x omega ∈ Ioi y}).toReal)
        atTop (nhds ((∫ z in Ioi (u+y), (F (Ioi z)).toReal ∂volume) /
          (∫ z : ℝ, z ∂F))) := by
  obtain ⟨Lambda, mLambda, Q, arrival, marks, hQ, hd⟩ :=
    levy_foundations_compoundPoissonDriverExists (1 : NNReal) one_pos F
  letI : MeasurableSpace Lambda := mLambda
  letI : IsProbabilityMeasure Q := hQ
  have hr := exercise52CPDriverRenewalEpochV1 Q arrival marks F hPos hd
  have hL := (renewalJointOvershootUndershoot Q marks F hr).2 hInt hNL
  intro u y hu hy
  apply (hL u y hu hy).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact congrArg ENNReal.toReal
    (exercise52CPPassageRenewalTransferV1 P Q X Xleft deathX
      arrival marks F hPos hd hX hCP hLeft x u y hx hu hy).symm
