-- Prove2me | solution 1 for MaxLatticeFree.Geometry.intW_inter_eq_intW_inter
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:43:55.215005+00:00
-- url     : https://prove2.me/submissions/87cd4bdd-99af-472f-9cda-d1532dedfac5

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_intW

namespace MaxLatticeFree.Geometry

theorem aux_iwie_superset {n : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hVW : V ≤ W)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Convex ℝ S)
    (p : EuclideanSpace ℝ (Fin n)) (hpV : p ∈ V) (δ : ℝ) (hδ : 0 < δ)
    (hpball : Metric.ball p δ ∩ (W : Set (EuclideanSpace ℝ (Fin n))) ⊆ S)
    (x : EuclideanSpace ℝ (Fin n)) (hxV : x ∈ V) (ε : ℝ) (hε : 0 < ε)
    (hball : Metric.ball x ε ∩ (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ S) :
    ∃ ε' : ℝ, 0 < ε' ∧ Metric.ball x ε' ∩ (W : Set (EuclideanSpace ℝ (Fin n))) ⊆ S := by
  set d := ‖x - p‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  set s : ℝ := ε / (2 * (d + 1)) with hs_def
  have hs : 0 < s := by positivity
  have hsd : s * d < ε := by
    rw [hs_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set y := x + s • (x - p) with hy
  have hyV : y ∈ V := V.add_mem hxV (V.smul_mem s (V.sub_mem hxV hpV))
  have hyS : y ∈ S := by
    apply hball
    refine ⟨?_, hyV⟩
    rw [Metric.mem_ball, dist_eq_norm, hy, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs]
    exact hsd
  refine ⟨δ * s / (1 + s), by positivity, ?_⟩
  rintro z ⟨hz, hzW⟩
  set q := (1 / s) • ((1 + s) • z - y) with hq_def
  have hqW : q ∈ W := W.smul_mem _ (W.sub_mem (W.smul_mem _ hzW) (hVW hyV))
  have hqp : q - p = ((1 + s) / s) • (z - x) := by
    rw [hq_def, hy]
    have hs' : s ≠ 0 := hs.ne'
    match_scalars <;> field_simp <;> ring
  have hqS : q ∈ S := by
    apply hpball
    refine ⟨?_, hqW⟩
    rw [Metric.mem_ball, dist_eq_norm, hqp, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc (1 + s) / s * ‖z - x‖ < (1 + s) / s * (δ * s / (1 + s)) := by
          apply mul_lt_mul_of_pos_left hz (by positivity)
      _ = δ := by field_simp
  have hzeq : z = (1 / (1 + s)) • y + (s / (1 + s)) • q := by
    rw [hq_def, hy]
    have hs' : s ≠ 0 := hs.ne'
    match_scalars <;> field_simp <;> ring
  rw [hzeq]
  exact hS hyS hqS (by positivity) (by positivity) (by field_simp)

end MaxLatticeFree.Geometry

open MaxLatticeFree.Geometry

theorem solution {n : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hVW : V ≤ W)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSW : S ⊆ (W : Set (EuclideanSpace ℝ (Fin n)))) (hS : Convex ℝ S)
    (hne : (intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    intW (W : Set (EuclideanSpace ℝ (Fin n))) S ∩ (V : Set (EuclideanSpace ℝ (Fin n))) =
      intW (V : Set (EuclideanSpace ℝ (Fin n))) (S ∩ (V : Set (EuclideanSpace ℝ (Fin n)))) := by
  ext x
  constructor
  · rintro ⟨⟨hxS, ε, hε, hball⟩, hxV⟩
    refine ⟨⟨hxS, hxV⟩, ε, hε, ?_⟩
    rintro z ⟨hz, hzV⟩
    exact ⟨hball ⟨hz, hVW hzV⟩, hzV⟩
  · rintro ⟨⟨hxS, hxV⟩, ε, hε, hball⟩
    obtain ⟨p, ⟨_, δ, hδ, hpball⟩, hpV⟩ := hne
    refine ⟨⟨hxS, ?_⟩, hxV⟩
    exact aux_iwie_superset V W hVW S hS p hpV δ hδ hpball x hxV ε hε
      (fun z hz => (hball hz).1)
