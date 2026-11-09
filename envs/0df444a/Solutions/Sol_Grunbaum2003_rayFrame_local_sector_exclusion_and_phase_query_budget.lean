-- Prove2me | solution 1 for Grunbaum2003.rayFrame_local_sector_exclusion_and_phase_query_budget
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:02:03.235821+00:00
-- url     : https://prove2.me/submissions/04832d80-bc94-49c2-b2b5-59d3fab10b03

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators Classical

open Grunbaum2003

lemma single_extension_step_query_bound (m cardS n q : ℕ)
    (hWalk : 3 + n ≤ 2 * (m - cardS) + 2) :
    q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3) := by
  omega

lemma multi_step_extension_query_bound (B : ℕ) (q_step : ℕ → ℕ) :
    ∀ K : ℕ, (∀ r < K, q_step (r + 1) ≤ q_step r + B) →
      q_step K ≤ q_step 0 + K * B := by
  intro K
  induction K with
  | zero =>
    intro _
    simp
  | succ K ih =>
    intro hStep
    have hIH := ih (fun r hr => hStep r (by omega))
    have hLast := hStep K (by omega)
    calc
      q_step (K + 1) ≤ q_step K + B := hLast
      _ ≤ (q_step 0 + K * B) + B := Nat.add_le_add_right hIH B
      _ = q_step 0 + (K + 1) * B := by
        rw [Nat.succ_mul, Nat.add_assoc]

lemma facet_discovery_phase_query_bound (d m cardS q_start : ℕ) (q_step : ℕ → ℕ)
    (hInit : q_step 0 ≤ q_start + 1)
    (hSteps : ∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) :
    q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3)) := by
  have hMulti := multi_step_extension_query_bound (2 * (m - cardS) + 3) q_step (d - 1) hSteps
  omega

lemma local_sector_known_facet_exclusion_of_finset {d m : ℕ}
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (hP_L : P = {x | ∀ i, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
    {p u : Fin d → ℝ} (hp_front : p ∈ frontier P)
    (hp_S : ∀ j ∈ S, L j p < 1)
    {a : ℝ} (ha : 0 < a) (hu_neg : (-a) • u ∈ P) (hu_pos : a • u ∈ P) :
    let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
    let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
    let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
    let ε := a * δ / (2 * (1 + a * M + δ))
    p - ε • u ≠ 0 ∧
      ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
        oracle (p - ε • u) = τ • (p - ε • u) ∧
        (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
        let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
        r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
        ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
          p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1 := by
  intro LS δ M ε
  have hP_conv : Convex ℝ P := by
    rcases hP.1 with ⟨W, _, _, rfl⟩
    exact convex_convexHull ℝ W
  have hP_closed : IsClosed P := by
    rw [hP_L]
    have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
        ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
    rw [h_eq]
    exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
  have hp_LS : ∀ j : Fin S.card, LS j p < 1 :=
    fun j => hp_S (eS j).val (eS j).property
  obtain ⟨hδ, hM, hp_δ, hu_M⟩ :=
    Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.1 LS p u hp_LS
  obtain ⟨hne, τ, hτ0, hτ2, horacle, h1, hr₂_ne, hr₂_S, hseg⟩ :=
    Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.2
      hP_conv hP_closed h0 hp_front ha hδ hM hu_neg hu_pos LS hp_δ hu_M hOracle
  have hLS_apply : ∀ (j : Fin m) (hj : j ∈ S) (q : Fin d → ℝ),
      LS (eS.symm ⟨j, hj⟩) q = L j q := by
    intro j hj q
    change (L (eS (eS.symm ⟨j, hj⟩)).val) q = L j q
    rw [Equiv.apply_symm_apply]
  refine ⟨hne, τ, hτ0, hτ2, horacle, ?_, hr₂_ne, ?_, ?_⟩
  · intro j hj
    rw [← hLS_apply j hj]
    exact h1 (eS.symm ⟨j, hj⟩)
  · intro j hj
    rw [← hLS_apply j hj]
    exact hr₂_S (eS.symm ⟨j, hj⟩)
  · intro x hx0 hx1
    refine ⟨(hseg x hx0 hx1).1, fun j hj => ?_⟩
    rw [← hLS_apply j hj]
    exact (hseg x hx0 hx1).2 (eS.symm ⟨j, hj⟩)

theorem solution (d : ℕ) :
    (∀ (m cardS n q : ℕ),
      3 + n ≤ 2 * (m - cardS) + 2 →
      q + 1 + 1 + 1 + n ≤ q + (2 * (m - cardS) + 3)) ∧
    (∀ (m cardS q_start : ℕ) (q_step : ℕ → ℕ),
      q_step 0 ≤ q_start + 1 →
      (∀ r < d - 1, q_step (r + 1) ≤ q_step r + (2 * (m - cardS) + 3)) →
      q_step (d - 1) ≤ q_start + (1 + (d - 1) * (2 * (m - cardS) + 3))) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ), P = {x | ∀ i, L i x ≤ 1} →
      ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
      ∀ (S : Finset (Fin m)) (eS : Fin S.card ≃ S)
        {p u : Fin d → ℝ}, p ∈ frontier P →
      (∀ j ∈ S, L j p < 1) →
      ∀ {a : ℝ}, 0 < a → (-a) • u ∈ P → a • u ∈ P →
      let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
      let δ := ∏ j : Fin S.card, (1 - LS j p) / (1 + (1 - LS j p))
      let M := 1 + ∑ j : Fin S.card, (LS j u) ^ 2
      let ε := a * δ / (2 * (1 + a * M + δ))
      p - ε • u ≠ 0 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
          oracle (p - ε • u) = τ • (p - ε • u) ∧
          (∀ j ∈ S, L j (oracle (p - ε • u)) < 1) ∧
          let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
          r₂ ≠ 0 ∧ (∀ j ∈ S, L j (oracle r₂) < 1) ∧
          ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
            p + x • (r₂ - p) ≠ 0 ∧ ∀ j ∈ S, L j (oracle (p + x • (r₂ - p))) < 1) := by
  refine ⟨single_extension_step_query_bound, facet_discovery_phase_query_bound d, ?_⟩
  intro m P hP h0 L hP_L oracle hOracle S eS p u hp_front hp_S a ha hu_neg hu_pos
  exact local_sector_known_facet_exclusion_of_finset hP h0 L hP_L hOracle S eS
    hp_front hp_S ha hu_neg hu_pos
