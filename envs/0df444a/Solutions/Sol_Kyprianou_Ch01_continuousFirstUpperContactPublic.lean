-- Prove2me | solution 1 for Kyprianou.Ch01.continuousFirstUpperContactPublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:46:05.718001+00:00
-- url     : https://prove2.me/submissions/6405b3f1-3b57-4a90-9a22-187c4f455d98

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Closure
import Mathlib.Data.NNReal.Defs
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (hcont : Continuous f) (s : ℝ)
    (hzero : f 0 ≤ s)
    (hcross : ∃ t : ℝ≥0, 0 < t ∧ s < f t)
    (hpos : 0 < sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) :
    f (sInf {t : ℝ≥0 | 0 < t ∧ s < f t}) = s := by 
  set S : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧ s < f t} with hSdef
  set τ := sInf S with hτ
  have hne : S.Nonempty := hcross
  have hbdd : BddBelow S := OrderBot.bddBelow S
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have hU : {t : ℝ≥0 | s < f t} ∈ 𝓝 τ :=
      (isOpen_lt continuous_const hcont).mem_nhds hlt
    obtain ⟨a, ha, hsub⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, hpos⟩
    obtain ⟨t, hat, htτ⟩ := exists_between ha
    have ht0 : 0 < t := lt_of_le_of_lt (show (0:ℝ≥0) ≤ a from a.2) hat
    have htS : t ∈ S := ⟨ht0, hsub ⟨hat, htτ.le⟩⟩
    have := csInf_le hbdd htS
    exact absurd htτ (not_lt.2 this)
  · by_contra hlt
    push Not at hlt
    have hU : {t : ℝ≥0 | f t < s} ∈ 𝓝 τ :=
      (isOpen_lt hcont continuous_const).mem_nhds hlt
    obtain ⟨b, hb, hsub⟩ := exists_Ico_subset_of_mem_nhds hU ⟨τ + 1, by
      have : (0:ℝ≥0) < 1 := one_pos
      exact lt_add_of_pos_right τ this⟩
    obtain ⟨t, htS, htb⟩ := exists_lt_of_csInf_lt hne hb
    have hτt : τ ≤ t := csInf_le hbdd htS
    have := hsub ⟨hτt, htb⟩
    exact absurd htS.2 (not_lt.2 this.le)
