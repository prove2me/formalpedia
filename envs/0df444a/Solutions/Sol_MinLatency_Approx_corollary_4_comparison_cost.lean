-- Prove2me | solution 1 for MinLatency.Approx.corollary_4_comparison_cost
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-27T00:52:57.829145+00:00
-- url     : https://prove2.me/submissions/0c03eb6b-e664-43d9-b93b-0e90d1ca95dc

import Mathlib
import Definitions.Def_MinLatency_Approx_Setting
namespace Queelius.MinLatency
open MinLatency.Approx
variable {V : Type} [Fintype V] [DecidableEq V]

theorem pcCost_const (d : V → V → ℝ) (P : ℝ) (T : List V) :
    pcCost d (fun _ => P) T = tourLen d T + (missed T : ℝ) * P := by
  simp [pcCost, missed, nsmul_eq_mul]

theorem comparison_cost (d : V → V → ℝ) (p : V) (L : ℝ) (hL : 0 ≤ L)
    (k : ℕ) (hk : 1 ≤ k) (T : List V) (_hT : IsRootedTour p T)
    (hlen : tourLen d T ≤ L) (hmiss : missed T ≤ k) :
    pcCost d (fun _ => 2 * L / k) T ≤ 3 * L := by
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hp : 0 ≤ 2 * L / (k : ℝ) := by positivity
  rw [pcCost_const]
  calc
    tourLen d T + (missed T : ℝ) * (2 * L / k) ≤ L + (k : ℝ) * (2 * L / k) :=
      add_le_add hlen (mul_le_mul_of_nonneg_right (by exact_mod_cast hmiss) hp)
    _ = 3 * L := by field_simp; ring

theorem distance_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (u v : V) : 0 ≤ d u v := by
  by_cases h : u=v
  · subst v
    rw [hd.self]
  · exact (hd.pos u v h).le

theorem pathLen_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (T : List V) : 0 ≤ pathLen d T := by
  induction T with
  | nil => simp [pathLen]
  | cons u T ih =>
    cases T with
    | nil => simp [pathLen]
    | cons v T => exact add_nonneg (distance_nonnegative d hd u v) ih

theorem tourLen_nonnegative (d : V → V → ℝ) (hd : IsMetric d) (T : List V) : 0 ≤ tourLen d T := by
  cases T with
  | nil => simp [tourLen]
  | cons u T => exact add_nonneg (pathLen_nonnegative d hd _) (distance_nonnegative d hd _ _)

theorem oracle_bounds (d : V → V → ℝ) (p : V) (hd : IsMetric d)
    (O : (V → ℝ) → List V) (hO : PCAdmissible d p O)
    (L : ℝ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k)
    (hex : ∃ T, IsRootedTour p T ∧ tourLen d T ≤ L ∧ missed T ≤ k) :
    IsRootedTour p (O (fun _ => 2 * L / k)) ∧
      tourLen d (O (fun _ => 2 * L / k)) ≤ 6 * L ∧
      missed (O (fun _ => 2 * L / k)) ≤ 3 * k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpen : 0 < 2 * L / (k : ℝ) := by positivity
  obtain ⟨T,hT,hlen,hmiss⟩ := hex
  obtain ⟨hroot,hcost⟩ := hO (fun _ => 2 * L / k) (fun _ => hpen.le)
  have hc : pcCost d (fun _ => 2 * L / k) (O (fun _ => 2 * L / k)) ≤ 6 * L :=
    (hcost T hT).trans (by have hh := comparison_cost d p L hL.le k hk T hT hlen hmiss; linarith)
  rw [pcCost_const] at hc
  refine ⟨hroot, ?_, ?_⟩
  · have hm : 0 ≤ (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) := by positivity
    linarith
  · have hnonneg := tourLen_nonnegative d hd (O (fun _ => 2 * L / k))
    have heq : (3 * k : ℝ) * (2 * L / k) = 6 * L := by field_simp; ring
    have hb : (missed (O (fun _ => 2 * L / k)) : ℝ) * (2 * L / k) ≤
        (3 * k : ℝ) * (2 * L / k) := by rw [heq]; linarith
    have hm := (mul_le_mul_iff_left₀ hpen).mp hb
    exact_mod_cast hm
end Queelius.MinLatency

open MinLatency.Approx

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (p : V) (L : ℝ) (hL : 0 ≤ L) (k : ℕ) (hk : 1 ≤ k)
    (T : List V) (hT : IsRootedTour p T) (hlen : tourLen d T ≤ L) (hmiss : missed T ≤ k) :
    pcCost d (fun _ => 2 * L / k) T ≤ 3 * L := by
  exact Queelius.MinLatency.comparison_cost d p L hL k hk T hT hlen hmiss

