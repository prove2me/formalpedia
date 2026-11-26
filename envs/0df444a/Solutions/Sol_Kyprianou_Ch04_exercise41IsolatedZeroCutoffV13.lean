-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IsolatedZeroCutoffV13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:15.390528+00:00
-- url     : https://prove2.me/submissions/f98dc3d2-ac83-4e8c-9837-c9c2291432b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (s : NNReal) (hs : 0 < s)
    (hf : Set.Finite {u : NNReal | 0 < u ∧ u ≤ s ∧ x u = 0}) :
    ∃ j : ℕ, 0 < q j ∧ q j < s ∧ ∀ u ∈ Ico (q j) s, x u ≠ 0 := by
  classical
  let Z := hf.toFinset.filter (fun u => u < s)
  let m := Z.sup id
  have hm : m < s := (Finset.sup_lt_iff hs).mpr (fun u hu => (Finset.mem_filter.mp hu).2)
  obtain ⟨v,hv⟩ := exists_between hm
  obtain ⟨_,hI,⟨j,rfl⟩⟩ := hq.inter_open_nonempty (Ioo m s) isOpen_Ioo ⟨v,hv⟩
  refine ⟨j,lt_of_le_of_lt bot_le hI.1,hI.2,?_⟩
  intro u hu hz
  have huZ : u ∈ Z := Finset.mem_filter.mpr
    ⟨hf.mem_toFinset.mpr ⟨lt_of_lt_of_le (lt_of_le_of_lt bot_le hI.1) hu.1,hu.2.le,hz⟩,hu.2⟩
  exact (not_lt_of_ge (le_trans (Finset.le_sup (f := id) huZ) (le_refl m)))
    (lt_of_lt_of_le hI.1 hu.1)
