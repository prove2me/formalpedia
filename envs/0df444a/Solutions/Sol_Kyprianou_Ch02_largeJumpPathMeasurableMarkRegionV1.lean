-- Prove2me | solution 1 for Kyprianou.Ch02.largeJumpPathMeasurableMarkRegionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:42:11.551812+00:00
-- url     : https://prove2.me/submissions/ec31391d-591c-4703-98b7-08131020727d

import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped Topology

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
 :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => fun t : ℝ≥0 => Kyprianou.largeJumpProcess P levyMeasure N t ω) := by
  let mReg : MeasurableSpace Ω :=
    ⨆ C ∈ {C : Set (ℝ × ℝ) |
      C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}) ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω C) inferInstance
  refine @measurable_pi_lambda Ω ℝ≥0 (fun _ => ℝ) mReg _ _ ?_
  intro t
  let R : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hR : MeasurableSet R :=
    measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)
  have hm := @Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1 Ω mΩ
    P _ levyMeasure _ N R hR
  unfold Kyprianou.largeJumpProcess
  apply hm.mono ?_ le_rfl
  dsimp [mReg]
  apply iSup_le
  intro C
  apply iSup_le
  intro hC
  have hsub : R ⊆ (Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|} :=
    fun z hz => ⟨Set.mem_univ z.1, hz.2⟩
  exact le_iSup_of_le C
    (le_iSup_of_le ⟨hC.1.trans hsub, hC.2⟩ le_rfl)
