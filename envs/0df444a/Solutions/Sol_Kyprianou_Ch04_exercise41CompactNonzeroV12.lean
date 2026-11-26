-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CompactNonzeroV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:56:30.029975+00:00
-- url     : https://prove2.me/submissions/5059628c-16c2-46ce-80a4-a2a98847398b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (a b : NNReal)
    (hLoc : ∀ s ∈ Icc a b, ∃ e : ℝ, 0 < e ∧
      {v : NNReal | e ≤ |x v|} ∈ nhds s) :
    ∃ e : ℝ, 0 < e ∧ ∀ s ∈ Icc a b, e ≤ |x s| := by
  let U (n : ℕ) := interior {v : NNReal | 1 / ((n : ℝ) + 1) ≤ |x v|}
  have hc : Icc a b ⊆ ⋃ n, U n := by
    intro s hs
    obtain ⟨e,he,hE⟩ := hLoc s hs
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt he
    apply Set.mem_iUnion.mpr
    refine ⟨n,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact mem_of_superset hE (fun v hv => hn.le.trans hv)
  obtain ⟨S,hS⟩ := (isCompact_Icc (a := a) (b := b)).elim_finite_subcover U
    (fun _ => isOpen_interior) hc
  let N := S.sup id
  refine ⟨1 / ((N : ℝ) + 1),by positivity,?_⟩
  intro s hs
  obtain ⟨n,hn,hu⟩ := Set.mem_iUnion₂.mp (hS hs)
  have hnN : n ≤ N := Finset.le_sup (f := id) hn
  have hdiv : 1 / ((N : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnN 1)
  have hbound : s ∈ {v : NNReal | 1 / ((n : ℝ) + 1) ≤ |x v|} := interior_subset hu
  exact hdiv.trans hbound
