-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/d6fe509e-52ef-459f-b33c-44c826d2d594

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonneg_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_at_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s : ℝ} (_hs : 0 ≤ s) (hs' : s < 1)
    (hclosure : FixedLevelCompactifiedCertificateClosure r) :
    LowerSemicontinuousOn (levelRate r) (Set.Icc (0 : ℝ) s) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro R
  let V : Set ℝ := Set.Icc (0 : ℝ) s ∩ (levelRate r) ⁻¹' Set.Iic R
  refine ⟨V, ?_, ?_⟩
  · apply IsSeqClosed.isClosed
    intro u x hu hux
    have hx : x ∈ Set.Icc (0 : ℝ) s :=
      isClosed_Icc.mem_of_tendsto hux
        (Filter.Eventually.of_forall fun n => (hu n).1)
    refine ⟨hx, ?_⟩
    change levelRate r x ≤ R
    by_cases hxzero : x = 0
    · rw [hxzero, levelRate_at_zero]
      exact (levelRate_nonneg_all r (u 0)).trans ((hu 0).2)
    · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
      have hxone : x < 1 := hx.2.trans_lt hs'
      have hevent : ∀ᶠ n : ℕ in atTop,
          0 < u n ∧ u n < 1 :=
        (hux.eventually (Ioi_mem_nhds hxpos)).and
          (hux.eventually (Iio_mem_nhds hxone))
      obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
      let v : ℕ → ℝ := fun n => u (n + N)
      have hvlim : Tendsto v atTop (nhds x) :=
        hux.comp (tendsto_add_atTop_nat N)
      have hvpos : ∀ n, 0 < v n :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).1
      have hvone : ∀ n, v n < 1 :=
        fun n => (hN (n + N) (Nat.le_add_left N n)).2
      have hvrate : ∀ n, levelRate r (v n) ≤ R :=
        fun n => (hu (n + N)).2
      have hdata : ∀ n : ℕ,
          ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
            Interlacing a b ∧ v n < 2 * Gamma a b ∧
              Phi a b < R + 1 / ((n : ℝ) + 1) := by
        intro n
        have hnonempty :=
          levelRateSet_nonempty_of_interior r (hvpos n) (hvone n)
        have hstrict : levelRate r (v n) < R + 1 / ((n : ℝ) + 1) :=
          lt_of_le_of_lt (hvrate n)
            (lt_add_of_pos_right _ (by positivity))
        obtain ⟨_, ⟨a, b, hinterlacing, hgap, rfl⟩, hrate⟩ :=
          exists_lt_of_csInf_lt hnonempty hstrict
        exact ⟨a, b, hinterlacing, hgap, hrate⟩
      choose a b hinter hgap hPhi using hdata
      exact hclosure hxpos hxone v a b hvlim hinter hgap
        (fun n => (hPhi n).le)
  · ext x
    simp [V]
end MetricCodes.Spherical.HigherHierarchy
