-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:27.482818+00:00
-- url     : https://prove2.me/submissions/32a97e43-6bdb-4e47-829c-5873c6c07c29

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_abs_eval_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_mul_simple_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIoc_zero_eval_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIoc_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i : Fin (stepIoc Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc Ω ha hab).partition i.castSucc)) ((stepIoc Ω ha hab).ξ i) := by
  intro i
  fin_cases i <;> exact MeasureTheory.stronglyMeasurable_const
theorem LevyStochCalc.Brownian.Ito.stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem LevyStochCalc.Brownian.Ito.partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)
/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => if_neg fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact if_pos hs
@[simp] theorem LevyStochCalc.Brownian.Ito.stepIocGen_eval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIocGen Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h, stepIoc_eval_readable]
  · rw [dif_neg h]
    have ha0 : a = 0 := le_antisymm (not_lt.mp h) ha
    subst ha0
    exact stepIoc_zero_eval_readable _ s ω
theorem LevyStochCalc.Brownian.Ito.stepIocGen_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∀ i : Fin (stepIocGen Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocGen Ω ha hab).partition i.castSucc)) ((stepIocGen Ω ha hab).ξ i) := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h]; exact stepIoc_adapt ℱ h hab
  · rw [dif_neg h]; exact stepIoc₀_adapt ℱ _
/-- **Restriction of a simple integrand to `(a, b]`.** Multiplying an adapted simple integrand
by `1_{(a, b]}` on their common refinement gives an adapted simple integrand whose evaluation is
the restricted evaluation and whose coefficients vanish on every tile not contained in `(a, b]`
and are bounded by `C` on the others. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (T₃ : ℝ) (Q : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
      ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
          ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0) := by
  classical
  obtain ⟨T₃, Q, hQadapt, hQeval, -⟩ :=
    LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple_readable W ℱ G (LevyStochCalc.Brownian.Ito.stepIocGen Ω ha hab) h_adapt
      (LevyStochCalc.Brownian.Ito.stepIocGen_adapt ℱ ha hab)
  have hQeval' : ∀ s ω, Q.eval s ω
      = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω := by
    intro s ω
    rw [hQeval s ω, LevyStochCalc.Brownian.Ito.stepIocGen_eval ha hab, mul_comm]
  refine ⟨T₃, Q, hQadapt, hQeval', fun j ω => ?_⟩
  have hlt : Q.partition j.castSucc < Q.partition j.succ :=
    Q.partition_strictMono Fin.castSucc_lt_succ
  by_cases hin : a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b
  · rw [if_pos hin]
    have hs : Q.partition j.castSucc < Q.partition j.succ
        ∧ Q.partition j.succ ≤ Q.partition j.succ := ⟨hlt, le_rfl⟩
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' _ ω, abs_mul]
    have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)| ≤ 1 := by
      by_cases hm : Q.partition j.succ ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hm]; norm_num
      · rw [Set.indicator_of_notMem hm]; norm_num
    calc |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)|
          * |G.eval (Q.partition j.succ) ω|
        ≤ 1 * C := by
          exact mul_le_mul h1 (G.abs_eval_le_readable hC0 hC _ ω) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [if_neg hin]
    -- pick a time in the tile that lies outside `(a, b]`
    obtain ⟨s, hs, hsout⟩ : ∃ s : ℝ, (Q.partition j.castSucc < s ∧ s ≤ Q.partition j.succ)
        ∧ s ∉ Set.Ioc a b := by
      by_cases hb : Q.partition j.succ ≤ b
      · have hna : Q.partition j.castSucc < a := by
          by_contra hcon
          exact hin ⟨not_lt.mp hcon, hb⟩
        refine ⟨min a (Q.partition j.succ), ⟨lt_min hna hlt, min_le_right _ _⟩, ?_⟩
        exact fun hm => absurd (Set.mem_Ioc.mp hm).1 (not_lt.mpr (min_le_left _ _))
      · refine ⟨Q.partition j.succ, ⟨hlt, le_rfl⟩, ?_⟩
        exact fun hm => hb (Set.mem_Ioc.mp hm).2
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' s ω, Set.indicator_of_notMem hsout, zero_mul,
      abs_zero]
