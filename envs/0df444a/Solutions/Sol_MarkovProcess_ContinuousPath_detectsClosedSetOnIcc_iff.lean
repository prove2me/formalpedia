-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.detectsClosedSetOnIcc_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:04.41943+00:00
-- url     : https://prove2.me/submissions/10079bbc-4ad9-42d5-a00e-e430dcc1d295

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Detecting closed sets from countably many path coordinates -/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]













private theorem closedSetDetectionThreshold_pos (n : ℕ) :
    0 < closedSetDetectionThreshold n := by
  exact one_div_pos.mpr (Nat.cast_add_one_pos n)



private theorem exists_denseTime_sample_between
    (u t : NNReal) (f : C(Set.Icc u t, alpha)) (F : Set alpha)
    {s : Set.Icc u t} (hus : u < s) (hst : (s : NNReal) < t)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hzero : Metric.infDist (f s) F = 0) :
    ∃ k : ℕ,
      ∃ huk : u < DenseTime.castOrderEmbedding (DenseTime.enumeration k),
      ∃ hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
        Metric.infDist
            (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), huk.le, hkt.le⟩) F <
          epsilon := by
  let g : Set.Icc u t → ℝ := fun v ↦ Metric.infDist (f v) F
  have hg : Continuous g := (Metric.continuous_infDist_pt (s := F)).comp f.continuous
  let O : Set (Set.Icc u t) := g ⁻¹' Set.Iio epsilon
  have hOopen : IsOpen O := isOpen_Iio.preimage hg
  have hsO : s ∈ O := by
    change Metric.infDist (f s) F < epsilon
    rw [hzero]
    exact hepsilon
  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp hOopen
  have hsW : (s : NNReal) ∈ W := by
    have hsPreimage : s ∈ Subtype.val ⁻¹' W := by
      rw [hW]
      exact hsO
    exact hsPreimage
  have hOpen : IsOpen (W ∩ Set.Ioo u t) := hWopen.inter isOpen_Ioo
  have hNonempty : (W ∩ Set.Ioo u t).Nonempty := ⟨s, hsW, hus, hst⟩
  obtain ⟨a, b, hab, hsub⟩ := hOpen.exists_Ioo_subset hNonempty
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  let k : ℕ := DenseTime.enumeration.symm q
  have hkq : DenseTime.enumeration k = q := DenseTime.enumeration.apply_symm_apply q
  have hqW : DenseTime.castOrderEmbedding q ∈ W ∩ Set.Ioo u t := hsub ⟨haq, hqb⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa only [hkq] using hqW.2.1
  · simpa only [hkq] using hqW.2.2
  · have hqO :
        (⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
          (by simpa only [hkq] using hqW.2.1.le),
          (by simpa only [hkq] using hqW.2.2.le)⟩ : Set.Icc u t) ∈ O := by
      rw [← hW]
      simpa only [hkq] using! hqW.1
    exact hqO







variable [MeasurableSpace alpha] [BorelSpace alpha]





end ContinuousPath

end
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-! # Detecting closed sets from countably many path coordinates -/

open MeasureTheory Set




variable {alpha : Type*} [PseudoMetricSpace alpha]



















namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution
    (u t : NNReal) (hut : u ≤ t) (F : Set alpha) (hF : IsClosed F)
    (f : C(Set.Icc u t, alpha)) :
    DetectsClosedSetOnIcc u t hut F f ↔ ∃ s : Set.Icc u t, f s ∈ F := by
  constructor
  · rintro ⟨hFnonempty, hdetect⟩
    by_contra hmeet
    have hnotmem : ∀ s : Set.Icc u t, f s ∉ F := by
      intro s hs
      exact hmeet ⟨s, hs⟩
    let g : Set.Icc u t → ℝ := fun s ↦ Metric.infDist (f s) F
    have hg : Continuous g := (Metric.continuous_infDist_pt (s := F)).comp f.continuous
    let : CompactSpace (Set.Icc u t) := isCompact_iff_compactSpace.mp isCompact_Icc
    have hcompact : IsCompact (Set.univ : Set (Set.Icc u t)) := isCompact_univ
    have huniv : (Set.univ : Set (Set.Icc u t)).Nonempty :=
      ⟨⟨u, le_rfl, hut⟩, Set.mem_univ _⟩
    obtain ⟨s, -, hsmin⟩ := hcompact.exists_isMinOn huniv hg.continuousOn
    have hgs : 0 < g s := (hF.notMem_iff_infDist_pos hFnonempty).mp (hnotmem s)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgs
    have hn' : closedSetDetectionThreshold n < g s := hn
    rcases hdetect n with hu | ht | ⟨k, huk, hkt, hk⟩
    · have hmin := hsmin (Set.mem_univ (⟨u, le_rfl, hut⟩ : Set.Icc u t))
      exact (not_lt_of_ge hmin) (hu.trans hn')
    · have hmin := hsmin (Set.mem_univ (⟨t, hut, le_rfl⟩ : Set.Icc u t))
      exact (not_lt_of_ge hmin) (ht.trans hn')
    · let q : Set.Icc u t :=
        ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), huk.le, hkt.le⟩
      have hmin := hsmin (Set.mem_univ q)
      exact (not_lt_of_ge hmin) (hk.trans hn')
  · rintro ⟨s, hsF⟩
    have hFnonempty : F.Nonempty := ⟨f s, hsF⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    have hzero : Metric.infDist (f s) F = 0 := Metric.infDist_zero_of_mem hsF
    by_cases hsu : (s : NNReal) = u
    · left
      have hs : s = (⟨u, le_rfl, hut⟩ : Set.Icc u t) := Subtype.ext hsu
      rw [← hs, hzero]
      exact closedSetDetectionThreshold_pos n
    by_cases hst : (s : NNReal) = t
    · right
      left
      have hs : s = (⟨t, hut, le_rfl⟩ : Set.Icc u t) := Subtype.ext hst
      rw [← hs, hzero]
      exact closedSetDetectionThreshold_pos n
    · right
      right
      exact exists_denseTime_sample_between u t f F
        (lt_of_le_of_ne s.property.1 (Ne.symm hsu))
        (lt_of_le_of_ne s.property.2 hst) (closedSetDetectionThreshold_pos n) hzero
