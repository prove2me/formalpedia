-- Prove2me | solution 1 for LevyFoundations.compactProjectiveThinning_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:10:55.697905+00:00
-- url     : https://prove2.me/submissions/0523c0fe-361e-45ce-97b6-87dee513cd97

import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.Polish
import Definitions.Def_levy_foundations_projectiveFamily
import Mathlib.Algebra.BigOperators.Fin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset Filter
open scoped ENNReal Topology

set_option maxHeartbeats 800000
theorem solution
    {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    [∀ i, TopologicalSpace (α i)]
    [∀ i, PolishSpace (α i)]
    [∀ i, BorelSpace (α i)]
    (pf : LevyFoundations.ProjectiveFamily ι α)
    (J : ℕ → Finset ι) (hJ_mono : Monotone J)
    (T : ∀ n, Set (∀ j : J n, α j))
    (mT : ∀ n, MeasurableSet (T n))
    (hT_anti : ∀ {n m} (hnm : n ≤ m),
      T m ⊆ Finset.restrict₂ (hJ_mono hnm) ⁻¹' T n)
    (K : ∀ n, Set (∀ j : J n, α j))
    (hK_compact : ∀ n, IsCompact (K n))
    (ε : ℝ≥0∞) (hε_pos : 0 < ε) (hε_ne_top : ε ≠ ⊤)
    (h_lower : ∀ n, ε ≤ pf.measure (J n) (T n))
    (hK_diff : ∀ n, pf.measure (J n) (T n \ K n) ≤ ε / 2 ^ (n + 2)) :
    ∀ n, (K n ∩ ⋂ k : Fin n,
      Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k).Nonempty := by
  classical
  intro n
  by_contra h_empty
  rw [Set.not_nonempty_iff_eq_empty] at h_empty
  suffices pf.measure (J n) (T n) < ε from
    absurd (h_lower n) (not_le.2 this)
  have hT_cover : T n ⊆ (T n \ K n) ∪
      ⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T k \ K k) := by
    intro x hx
    by_cases hxK : x ∈ K n
    · right
      have : x ∉ ⋂ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k := by
        intro hmem
        exact h_empty.subset ⟨hxK, hmem⟩
      rw [Set.mem_iInter] at this
      push Not at this
      obtain ⟨k, hk⟩ := this
      exact Set.mem_iUnion.2 ⟨k, Set.mem_preimage.2 ⟨hT_anti k.2.le hx, hk⟩⟩
    · exact Or.inl ⟨hx, hxK⟩
  have hK_diff_pull : ∀ k : Fin n,
      pf.measure (J n) (Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) =
      pf.measure (J ↑k) (T ↑k \ K ↑k) := by
    intro k
    rw [← Measure.map_apply (Finset.measurable_restrict₂ _)
      ((mT ↑k).diff (hK_compact ↑k).measurableSet),
      ← pf.consistent (J n) (J ↑k) (hJ_mono k.2.le)]
  have hstep1 : pf.measure (J n) (T n) ≤
      pf.measure (J n) (T n \ K n) +
      ∑ k : Fin n, pf.measure (J ↑k) (T ↑k \ K ↑k) := by
    calc pf.measure (J n) (T n)
        ≤ pf.measure (J n) ((T n \ K n) ∪
            ⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) :=
          measure_mono hT_cover
      _ ≤ pf.measure (J n) (T n \ K n) +
            pf.measure (J n)
              (⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) :=
          measure_union_le _ _
      _ ≤ pf.measure (J n) (T n \ K n) +
            ∑ k : Fin n, pf.measure (J n)
              (Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) := by
          gcongr
          exact measure_iUnion_fintype_le _ _
      _ = _ := by
          congr 1
          congr 1 with k
          exact hK_diff_pull k
  have htsum_lt : ∑' k : ℕ, ε / 2 ^ (k + 2) < ε := by
    have h1 : (fun k ↦ ε / 2 ^ (k + 2)) =
        fun k ↦ (ε * (2 : ℝ≥0∞)⁻¹ ^ 2) * (2 : ℝ≥0∞)⁻¹ ^ k := by
      ext k
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow,
        show k + 2 = 2 + k from by omega, pow_add]
      ring
    rw [h1, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ENNReal.one_sub_inv_two, inv_inv]
    rw [show (ε * (2 : ℝ≥0∞)⁻¹ ^ 2) * 2 =
        ε * ((2 : ℝ≥0∞)⁻¹ ^ 2 * 2) from by ring]
    rw [show (2 : ℝ≥0∞)⁻¹ ^ 2 * 2 = (2 : ℝ≥0∞)⁻¹ from by
      rw [pow_succ, pow_one, mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]]
    calc ε * (2 : ℝ≥0∞)⁻¹ = ε / 2 := by rw [ENNReal.div_eq_inv_mul, mul_comm]
      _ < ε := ENNReal.half_lt_self hε_pos.ne' hε_ne_top
  have hstep2 : pf.measure (J n) (T n) ≤
      ε / 2 ^ (n + 2) + ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2) :=
    hstep1.trans (add_le_add (hK_diff n)
      (Finset.sum_le_sum fun k _ ↦ hK_diff ↑k))
  have hstep3 : ε / 2 ^ (n + 2) +
      ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2) ≤
      ∑' k : ℕ, ε / 2 ^ (k + 2) := by
    calc ε / 2 ^ (n + 2) + ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2)
        = ∑ k : Fin (n + 1), ε / 2 ^ ((k : ℕ) + 2) := by
          rw [Fin.sum_univ_castSucc]
          simp [Fin.val_last, Fin.val_castSucc, add_comm]
      _ = ∑' k : Fin (n + 1), ε / 2 ^ ((k : ℕ) + 2) :=
          (tsum_fintype _).symm
      _ ≤ ∑' k : ℕ, ε / 2 ^ (k + 2) :=
          ENNReal.tsum_comp_le_tsum_of_injective Fin.val_injective _
  exact (hstep2.trans hstep3).trans_lt htsum_lt
