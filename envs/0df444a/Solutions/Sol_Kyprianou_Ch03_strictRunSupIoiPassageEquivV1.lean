-- Prove2me | solution 1 for Kyprianou.Ch03.strictRunSupIoiPassageEquivV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:11.793368+00:00
-- url     : https://prove2.me/submissions/cf86e0fa-d1fd-4df2-8454-76eb2b0c54a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (hx : 0 < x) (omega : Omega) (t : NNReal) :
    x < LevyExtrema.SBA.runSup (fun s => L.X s omega) t ↔
      Kyprianou.Ch03.firstHittingTime L.X (Set.Ioi x) omega <
        (t : WithTop NNReal) := by
  classical
  have hl : ∀ u : NNReal, ∃ l : ℝ,
      Tendsto (fun s => L.X s omega) (𝓝[<] u) (𝓝 l) := by
    intro u
    by_cases hu : 0 < u
    · exact L.leftLim omega u hu
    · have h : u = 0 := le_antisymm (le_of_not_gt hu) (zero_le)
      subst u
      exact ⟨0, by simp [Set.Iio]⟩
  have hb := AvramDividend.Classical.one_sided_limits_bddAbove_Icc
    (fun s => L.X s omega) (fun u => L.rightCont omega u) hl t
  have hb' : BddAbove ((fun s => L.X s omega) '' Set.Icc 0 t) := by
    convert hb using 1
    ext z
    simp
  have hn : ((fun s => L.X s omega) '' Set.Icc 0 t).Nonempty :=
    ⟨L.X 0 omega, 0, ⟨le_rfl, zero_le⟩, rfl⟩
  rw [Kyprianou.Ch03.firstHittingIoi_eq_correctedUpTime P F L x hx omega]
  unfold LevyExtrema.SBA.runSup
  change x < sSup ((fun s => L.X s omega) '' Set.Icc 0 t) ↔
    (⨅ (u : NNReal) (_ : x < L.X u omega), (u : ENNReal)) < (t : ENNReal)
  constructor
  · intro hs
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := (lt_csSup_iff hb' hn).mp hs
    have hle : (⨅ (v : NNReal) (_ : x < L.X v omega), (v : ENNReal)) ≤
        (u : ENNReal) := iInf_le_of_le u (iInf_le _ hy)
    by_contra! hnt
    have heq : (u : ENNReal) =
        (⨅ (v : NNReal) (_ : x < L.X v omega), (v : ENNReal)) :=
      le_antisymm (le_trans (by exact_mod_cast hu.2) hnt) hle
    have he := AvramDividend.Classical.firstUpcrossing_value_eq_threshold
      L x hx.le omega u heq
    linarith
  · intro hs
    rw [iInf_lt_iff] at hs
    obtain ⟨u, hu⟩ := hs
    rw [iInf_lt_iff] at hu
    obtain ⟨hxu, hut⟩ := hu
    have hut' : u ≤ t := le_of_lt (by exact_mod_cast hut)
    exact hxu.trans_le (le_csSup hb' ⟨u, ⟨zero_le, hut'⟩, rfl⟩)
