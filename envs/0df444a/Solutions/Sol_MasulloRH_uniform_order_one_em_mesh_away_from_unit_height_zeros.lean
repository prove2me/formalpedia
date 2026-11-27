-- Prove2me | solution 1 for MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:57:28.955468+00:00
-- url     : https://prove2.me/submissions/bd0c2f70-fd0c-4c92-ade2-e252498354c3

import Theorems.Thm_MasulloRH_rational_mesh_completes_unit_height_em_balls
import Theorems.Thm_MasulloRH_unit_height_em_enclosure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter Topology MasulloRH.UnitHeightMeshes

private lemma budget_small (n : ℕ) {h : ℝ} (hh : 0 < h) :
    ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ 2*((derivBudget n * rad m + emError n 1 m : ℚ):ℝ) < h := by
  let A : ℝ := ((100002+n+2:ℕ):ℝ)^3/108
  have f := tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)
  have g := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).pow 2
  have bg : Tendsto (fun m : ℕ => 2*((derivBudget n:ℝ)*(2/(m:ℝ)) + A*((1:ℝ)/m)^2)) atTop (𝓝 0) := by
    simpa using (((f.const_mul (derivBudget n:ℝ)).add (g.const_mul A)).const_mul 2)
  have ev := (tendsto_order.mp bg).2 h hh
  obtain ⟨B,hB⟩ := eventually_atTop.1 ev
  refine ⟨max B 1,fun m hm => ⟨(le_max_right ..).trans hm,?_⟩⟩
  have bound := hB m ((le_max_left ..).trans hm)
  calc
    _ = 2*((derivBudget n:ℝ)*(2/(m:ℝ)) + A*((1:ℝ)/m)^2) := by
      norm_num [rad,emError,A,div_eq_mul_inv,mul_inv_rev]; ring
    _ < h := bound

private lemma uniform (n k : ℕ) (S : Set ℂ) (hS : IsCompact S) (sub : S ⊆ rect n k)
    (nz : ∀ s ∈ S, riemannZeta s ≠ 0) :
    ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
      (∃ s ∈ S, dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) → passes n k m i j := by
  rcases S.eq_empty_or_nonempty with rfl | ne
  · exact ⟨1,fun m hm => ⟨hm,by simp⟩⟩
  have cont : ContinuousOn (fun s : ℂ => ‖riemannZeta s‖) S := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.norm
    apply (differentiableAt_riemannZeta _).continuousAt
    intro eq
    have height := (sub hs).2.1
    rw [eq,Complex.one_im] at height
    have pos : 0 < margin k := by unfold margin; positivity
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨z,hz,least⟩ := hS.exists_isMinOn ne cont
  obtain ⟨B,hB⟩ := budget_small n (norm_pos_iff.mpr (nz z hz))
  refine ⟨B,fun m hm => ⟨(hB m hm).1,?_⟩⟩
  rintro i hi j hj ⟨s,hs,near⟩
  let v := rationalCenter (node n k m i j)
  have pos := (hB m hm).1
  have hv := MasulloRH.rational_mesh_completes_unit_height_em_balls.1 n k m i j pos hi hj
  have var := MasulloRH.rational_mesh_completes_unit_height_em_balls.2.2.1 n k s (sub hs) v hv
  have err := MasulloRH.unit_height_em_enclosure n k 1 m (by decide) pos v hv
  change ‖riemannZeta v - ZetaReflection.EMHigh.emFinite 1 v m‖ ≤ (emError n 1 m:ℝ) at err
  have height : ‖riemannZeta z‖ ≤ ‖riemannZeta s‖ := least hs
  have sl : 0 ≤ (derivBudget n:ℝ) := by simp [derivBudget]; positivity
  have bd := mul_le_mul_of_nonneg_left near.le sl
  have a := norm_add_le (riemannZeta s - riemannZeta v) (riemannZeta v)
  have b := norm_add_le (riemannZeta v - ZetaReflection.EMHigh.emFinite 1 v m)
    (ZetaReflection.EMHigh.emFinite 1 v m)
  rw [sub_add_cancel] at a b
  have small := (hB m hm).2
  change ((derivBudget n * rad m + emError n 1 m : ℚ):ℝ) < ‖ZetaReflection.EMHigh.emFinite 1 v m‖
  push_cast at small ⊢
  change (derivBudget n:ℝ) * dist s v ≤ _ at bd
  linarith

private lemma pass_covers {n k m i j : ℕ} (hm : 0 < m) (hi : i ≤ m) (hj : j ≤ m)
    {s : ℂ} (hd : dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) (hp : passes n k m i j) :
    covered n k s := by
  exact ⟨node n k m i j,rad m,⟨MasulloRH.rational_mesh_completes_unit_height_em_balls.1 n k m i j hm hi hj,
    1,m,by decide,hm,hp⟩,hd⟩

private lemma complete (n k : ℕ) (s : ℂ) (hs : s ∈ rect n k) :
    covered n k s ↔ riemannZeta s ≠ 0 := by
  refine ⟨MasulloRH.rational_mesh_completes_unit_height_em_balls.2.2.2 n k s hs,fun hn => ?_⟩
  obtain ⟨B,hB⟩ := uniform n k {s} isCompact_singleton (singleton_subset_iff.mpr hs) (by simpa using hn)
  obtain ⟨pos,all⟩ := hB B le_rfl
  obtain ⟨i,hi,j,hj,_,near⟩ := MasulloRH.rational_mesh_completes_unit_height_em_balls.2.1 n k B pos s hs
  exact pass_covers pos hi hj near (all i hi j hj ⟨s,by simp,near⟩)

theorem solution :
    (∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s ↔ riemannZeta s ≠ 0) ∧
    (∀ n k : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ rect n k → (∀ s ∈ S, riemannZeta s ≠ 0) →
      ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
        (∃ s ∈ S, dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) → passes n k m i j) := by
  exact ⟨complete,uniform⟩
