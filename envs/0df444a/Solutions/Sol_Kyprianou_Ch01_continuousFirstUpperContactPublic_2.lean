-- Prove2me | solution 2 for Kyprianou.Ch01.continuousFirstUpperContactPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:50:08.80078+00:00
-- url     : https://prove2.me/submissions/2f03ee18-9161-41d0-a9b8-ec0041acc073

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- A positive infimum of strict upper crossings of a continuous path touches the level. -/
theorem solution
    (f : ℝ≥0 → ℝ) (hcont : Continuous f) (s : ℝ)
    (hzero : f 0 ≤ s)
    (hcross : ∃ t : ℝ≥0, 0 < t ∧ s < f t)
    (hpos : 0 < sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) :
    f (sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) = s := by
  classical
  let S : Set ℝ≥0 := {t | 0 < t ∧ s < f t}
  let T : ℝ≥0 := sInf S
  have hne : S.Nonempty := hcross
  have hTpos : 0 < T := hpos
  have hle0 : s ≤ f T := by
    have hc : IsClosed {t : ℝ≥0 | s ≤ f t} :=
      isClosed_Ici.preimage hcont
    have hs : S ⊆ {t : ℝ≥0 | s ≤ f t} := by
      rintro t ⟨_, ht⟩
      exact ht.le
    have hmem : T ∈ closure S :=
      csInf_mem_closure hne (OrderBot.bddBelow S)
    exact (closure_minimal hs hc) hmem
  have hle : f T ≤ s := by
    by_contra hn
    have hgt : s < f T := lt_of_not_ge hn
    have hopen : IsOpen {t : ℝ≥0 | s < f t} :=
      isOpen_Ioi.preimage hcont
    have hnhds : {t : ℝ≥0 | s < f t} ∈ 𝓝 T :=
      hopen.mem_nhds hgt
    have hleft : (Iio T).Nonempty := by
      refine ⟨0, ?_⟩
      exact hTpos
    letI : NeBot (𝓝[Iio T] T) :=
      nhdsWithin_Iio_neBot' hleft le_rfl
    have hs : {t : ℝ≥0 | s < f t} ∈ 𝓝[Iio T] T :=
      mem_nhdsWithin_of_mem_nhds hnhds
    have hBoth :
        ({t : ℝ≥0 | s < f t} ∩ Iio T) ∈ 𝓝[Iio T] T :=
      Filter.inter_mem hs self_mem_nhdsWithin
    obtain ⟨u, hu_gt, hu_lt⟩ := Filter.nonempty_of_mem hBoth
    have hu_pos : 0 < u := by
      have hu_ne : u ≠ 0 := by
        intro heq
        subst u
        exact (not_lt_of_ge hzero) hu_gt
      exact pos_iff_ne_zero.mpr hu_ne
    have huS : u ∈ S := ⟨hu_pos, hu_gt⟩
    have hTle : T ≤ u := csInf_le (OrderBot.bddBelow S) huS
    exact (not_le_of_gt hu_lt) hTle
  exact le_antisymm hle hle0
