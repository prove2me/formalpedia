-- Prove2me | solution 1 for NieYangPareto.proposition_3_1_i
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-10T12:32:15.709293+00:00
-- url     : https://prove2.me/submissions/ce3f91aa-4a6b-470a-9294-83d7bd07693b

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_ParetoNotions
import Definitions.Def_NieYangPareto_MOP_U

set_option autoImplicit false

open NieYangPareto

private theorem strictDominance_iff_mem_interior {n m : ℕ} {E I : Type*}
    (P : MOP n m E I) (v : Fin m → ℝ) :
    (∃ x ∈ P.K, ∀ i, P.obj x i < v i) ↔ v ∈ interior P.U := by
  constructor
  · rintro ⟨x, hx, hstrict⟩
    let O : Set (Fin m → ℝ) := ⋂ i : Fin m, (fun u : Fin m → ℝ => u i) ⁻¹' Set.Ioi (P.obj x i)
    have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
      isOpen_Ioi.preimage (continuous_apply i)
    have hvO : v ∈ O := Set.mem_iInter.mpr hstrict
    exact mem_interior_iff_mem_nhds.mpr <| Filter.mem_of_superset (hO.mem_nhds hvO)
      (fun u hu => ⟨x, hx, fun i => (show P.obj x i < u i from Set.mem_iInter.mp hu i).le⟩)
  · intro hi
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
    let p : Fin m → ℝ := fun i => v i - ε / 2
    have hp : p ∈ Metric.ball v ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      apply lt_of_le_of_lt _ (show ε / 2 < ε by linarith)
      refine (pi_norm_le_iff_of_nonneg (show 0 ≤ ε / 2 by positivity)).mpr (fun i => ?_)
      change ‖v i - ε / 2 - v i‖ ≤ ε / 2
      rw [show v i - ε / 2 - v i = -(ε / 2) by ring, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    obtain ⟨x, hx, hle⟩ := hball hp
    exact ⟨x, hx, fun i => (hle i).trans_lt (show p i < v i by dsimp [p]; linarith)⟩

theorem solution {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) :
    (P.IsWeaklyParetoValue v ↔ v ∈ frontier P.U) ∧
      (v ∈ (convexHull ℝ P.U).extremePoints ℝ → P.IsParetoValue v) := by
  obtain ⟨xs, hxs, rfl⟩ := hv
  have hvU : P.obj xs ∈ P.U := ⟨xs, hxs, fun _ => le_rfl⟩
  constructor
  · constructor
    · rintro ⟨z, ⟨_, hz⟩, hval⟩
      rw [← hval] at hz
      exact ⟨subset_closure hvU, fun hi => hz ((strictDominance_iff_mem_interior P (P.obj xs)).mpr hi)⟩
    · intro hfront
      exact ⟨xs, ⟨hxs, fun h => hfront.2 ((strictDominance_iff_mem_interior P (P.obj xs)).mp h)⟩, rfl⟩
  · intro hext
    refine ⟨xs, ⟨hxs, ?_⟩, rfl⟩
    rintro ⟨x, hx, hle, j, hj⟩
    let u : Fin m → ℝ := fun i => 2 * P.obj xs i - P.obj x i
    have hu : u ∈ P.U := ⟨x, hx, fun i => by dsimp [u]; linarith [hle i]⟩
    have hxU : P.obj x ∈ P.U := ⟨x, hx, fun _ => le_rfl⟩
    have hseg : P.obj xs ∈ openSegment ℝ (P.obj x) u := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      funext i
      change (1 / 2 : ℝ) * P.obj x i + (1 / 2 : ℝ) * u i = P.obj xs i
      dsimp [u]
      ring
    have heq := (mem_extremePoints_iff_left.mp hext).2 _ (subset_convexHull ℝ P.U hxU)
      _ (subset_convexHull ℝ P.U hu) hseg
    exact hj.ne (congrFun heq j)

#print axioms solution