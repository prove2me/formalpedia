-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedSignedRightContinuousAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:49:37.884466+00:00
-- url     : https://prove2.me/submissions/a1eb4a98-c9ab-4e81-a70d-ae8c8906642c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Theorems.Thm_Kyprianou_Ch01_isCadlag_realScalarMultiple
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (c y : ℝ) :
    ∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => reflectedSup (fun v z => c * X v z) y u w) (Ici s) s := by
  filter_upwards [hX.cadlag_ae] with w hw
  let g (u : NNReal) := c * X u w
  let M := LevyExtrema.SBA.runSup g
  have hg := Kyprianou.Ch01.isCadlag_realScalarMultiple c (fun u => X u w) hw
  have hb (s : NNReal) : BddAbove (g '' Set.Icc 0 s) := by
    apply (Kyprianou.Ch01.cadlag_runningSup_bddAbove g hg s).mono
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,hu.2,rfl⟩
  have hM : Monotone M := by
    intro a b hab
    exact csSup_le_csSup (hb b) ⟨g 0,0,⟨le_rfl,zero_le⟩,rfl⟩
      (Set.image_mono (Set.Icc_subset_Icc le_rfl hab))
  have hdom (s : NNReal) : g s ≤ M s :=
    le_csSup (hb s) ⟨s,⟨zero_le,le_rfl⟩,rfl⟩
  have hrepr (s : NNReal) : M s = ⨆ u : Set.Icc (0 : NNReal) s, g u.1 := by
    change sSup (g '' Set.Icc 0 s) = sSup (Set.range _)
    congr 1
    ext z
    exact ⟨fun ⟨u,hu,hz⟩ => ⟨⟨u,hu⟩,hz⟩, fun ⟨u,hu⟩ => ⟨u.1,u.2,hu⟩⟩
  intro s
  have h := AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
    g M hM hdom hrepr (fun u => (hg u).1) s
  exact (continuousWithinAt_const.max h).sub (hg s).1
