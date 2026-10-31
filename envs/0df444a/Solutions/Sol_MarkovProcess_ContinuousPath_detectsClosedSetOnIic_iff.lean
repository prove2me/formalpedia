-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.detectsClosedSetOnIic_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:11.187996+00:00
-- url     : https://prove2.me/submissions/fb6470b1-0b11-485f-9b28-1109d9f97177

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

/-- The positive thresholds used to detect zero distance to a closed set. -/
private def detectionThreshold (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem detectionThreshold_pos (n : ℕ) : 0 < detectionThreshold n := by
  exact one_div_pos.mpr (Nat.cast_add_one_pos n)



private theorem exists_denseTime_sample_of_lt
    (t : NNReal) (f : C(Set.Iic t, alpha)) (F : Set alpha)
    {s : Set.Iic t} (hs : (s : NNReal) < t) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hzero : Metric.infDist (f s) F = 0) :
    ∃ k : ℕ, ∃ hk : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
      Metric.infDist
          (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
            Set.mem_Iic.mpr hk.le⟩) F < epsilon := by
  let g : Set.Iic t → ℝ := fun u ↦ Metric.infDist (f u) F
  have hg : Continuous g :=
    (Metric.continuous_infDist_pt (s := F)).comp f.continuous
  let O : Set (Set.Iic t) := g ⁻¹' Set.Iio epsilon
  have hOopen : IsOpen O := isOpen_Iio.preimage hg
  have hsO : s ∈ O := by
    change Metric.infDist (f s) F < epsilon
    rw [hzero]
    exact hepsilon
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hOopen
  have hsV : (s : NNReal) ∈ V := by
    have : s ∈ Subtype.val ⁻¹' V := by
      rw [hV]
      exact hsO
    exact this
  have hWopen : IsOpen (V ∩ Set.Iio t) := hVopen.inter isOpen_Iio
  have hWnonempty : (V ∩ Set.Iio t).Nonempty := ⟨s, hsV, hs⟩
  obtain ⟨a, b, hab, hsub⟩ := hWopen.exists_Ioo_subset hWnonempty
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  let k : ℕ := DenseTime.enumeration.symm q
  have hkq : DenseTime.enumeration k = q := DenseTime.enumeration.apply_symm_apply q
  have hqW : DenseTime.castOrderEmbedding q ∈ V ∩ Set.Iio t := hsub ⟨haq, hqb⟩
  have hkW : DenseTime.castOrderEmbedding (DenseTime.enumeration k) ∈
      V ∩ Set.Iio t := by
    rw [hkq]
    exact hqW
  refine ⟨k, ?_, ?_⟩
  · exact hkW.2
  · have hqO :
        (⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
          Set.mem_Iic.mpr hkW.2.le⟩ : Set.Iic t) ∈ O := by
      rw [← hV]
      exact hkW.1
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
    (t : NNReal) (F : Set alpha) (hF : IsClosed F) (f : C(Set.Iic t, alpha)) :
    DetectsClosedSetOnIic t F f ↔ ∃ s : Set.Iic t, f s ∈ F := by
  constructor
  · rintro ⟨hFnonempty, hdetect⟩
    by_contra hmeet
    have hnotmem : ∀ s : Set.Iic t, f s ∉ F := by
      intro s hs
      exact hmeet ⟨s, hs⟩
    let g : Set.Iic t → ℝ := fun s ↦ Metric.infDist (f s) F
    have hg : Continuous g :=
      (Metric.continuous_infDist_pt (s := F)).comp f.continuous
    have hIic : IsCompact (Set.Iic t : Set NNReal) := by
      have heq : Set.Iic t = Set.Icc 0 t := by
        ext u
        simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
      rw [heq]
      exact isCompact_Icc
    let : CompactSpace (Set.Iic t) := isCompact_iff_compactSpace.mp hIic
    have hcompact : IsCompact (Set.univ : Set (Set.Iic t)) := isCompact_univ
    have huniv : (Set.univ : Set (Set.Iic t)).Nonempty :=
      ⟨⟨0, (zero_le : (0 : NNReal) ≤ t)⟩, Set.mem_univ _⟩
    obtain ⟨s, -, hsmin⟩ := hcompact.exists_isMinOn huniv hg.continuousOn
    have hgs : 0 < g s := (hF.notMem_iff_infDist_pos hFnonempty).mp (hnotmem s)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgs
    have hn' : detectionThreshold n < g s := hn
    rcases hdetect n with hendpoint | ⟨k, hkt, hk⟩
    · have hmin := hsmin
          (Set.mem_univ (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t))
      exact (not_lt_of_ge hmin) (hendpoint.trans hn')
    · let q : Set.Iic t :=
        ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), hkt.le⟩
      have hmin := hsmin (Set.mem_univ q)
      exact (not_lt_of_ge hmin) (hk.trans hn')
  · rintro ⟨s, hsF⟩
    have hFnonempty : F.Nonempty := ⟨f s, hsF⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    have hzero : Metric.infDist (f s) F = 0 := Metric.infDist_zero_of_mem hsF
    by_cases hst : (s : NNReal) = t
    · left
      have hs : s = (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t) := Subtype.ext hst
      rw [← hs, hzero]
      exact detectionThreshold_pos n
    · right
      exact exists_denseTime_sample_of_lt t f F
        (lt_of_le_of_ne s.property hst) (detectionThreshold_pos n) hzero
