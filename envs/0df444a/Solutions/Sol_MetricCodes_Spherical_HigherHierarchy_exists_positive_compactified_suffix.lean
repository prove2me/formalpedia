-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_positive_compactified_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/72529145-20ba-44a5-8acd-774b824d6ef0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedAmbient_monotone_of_weak_interlacing

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
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
    (hA : ∀ i, A i ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ i, B i ∈ Set.Icc (0 : ℝ) 1)
    (hinter : ∀ i : Fin r,
      A i.castSucc ≤ B i ∧ B i ≤ A i.succ)
    (hpaired : ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0)
    (hlast : 0 < A (Fin.last r)) :
    ∃ (k j : ℕ) (hkj : k + j = r),
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) := by
  let P : ℕ → Prop := fun n =>
    ∃ i : Fin (r + 1), i.val = n ∧ 0 < A i
  have hP : ∃ n, P n :=
    ⟨r, Fin.last r, by simp, hlast⟩
  let k := Nat.find hP
  obtain ⟨i₀, hi₀, hpos⟩ := Nat.find_spec hP
  have hkle : k ≤ r := by
    change (Nat.find hP) ≤ r
    omega
  let j := r - k
  have hkj : k + j = r := by
    dsimp [j]
    omega
  refine ⟨k, j, hkj, ?_, ?_, ?_, ?_⟩
  · intro i hik
    have hnot : ¬ 0 < A i.castSucc := by
      intro hpositive
      have hmin := Nat.find_min' hP ⟨i.castSucc, rfl, hpositive⟩
      change k ≤ i.val at hmin
      omega
    have hazero : A i.castSucc = 0 :=
      le_antisymm (le_of_not_gt hnot) (hA i.castSucc).1
    exact ⟨hazero, (hpaired i).mp hazero⟩
  · intro i
    constructor
    · have hle : i₀ ≤ (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
        apply Fin.mk_le_mk.mpr
        omega
      exact hpos.trans_le
        (compactifiedAmbient_monotone_of_weak_interlacing hinter hle)
    · exact (hA ⟨k + i.val, by omega⟩).2
  · intro i
    constructor
    · have hpositive : 0 < A (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
        have hle : i₀ ≤ (⟨k + i.val, by omega⟩ : Fin (r + 1)) := by
          apply Fin.mk_le_mk.mpr
          omega
        exact hpos.trans_le
          (compactifiedAmbient_monotone_of_weak_interlacing hinter hle)
      exact hpositive.trans_le
        (hinter (⟨k + i.val, by omega⟩ : Fin r)).1
    · exact (hB ⟨k + i.val, by omega⟩).2
  · intro i
    have h := hinter (⟨k + i.val, by omega⟩ : Fin r)
    constructor
    · simpa [compactifiedAmbientSuffix, compactifiedStabilizerSuffix]
        using h.1
    · change B (⟨k + i.val, by omega⟩ : Fin r) ≤
        A (⟨k + (i.val + 1), by omega⟩ : Fin (r + 1))
      simpa [Nat.add_assoc] using h.2
end MetricCodes.Spherical.HigherHierarchy
