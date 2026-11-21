-- Prove2me | solution 1 for MasulloGRH.escaping_set_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:30:53.685128+00:00
-- url     : https://prove2.me/submissions/8cb1bd9e-e485-41e1-b2e4-500cb707860b

import Definitions.Def_MasulloGRH_LocallyConvex

open Set MasulloGRH

private theorem separate_stage {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (V : Submodule ℂ E) (hc : IsClosed (V : Set E))
    (x : E) (hx : x ∉ V) (a : ℂ) :
    ∃ f : StrongDual ℂ E, (∀ y ∈ V, f y = 0) ∧ f x = a := by
  letI : Module ℝ E := Module.compHom E (algebraMap ℝ ℂ)
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.of_compHom ℝ ℂ E
  obtain ⟨ι, _, p, hp⟩ := hE.1
  haveI := hp.topologicalAddGroup
  haveI := hp.continuousSMul
  haveI := hp.toLocallyConvexSpace
  have hconv : Convex ℝ (V : Set E) := (V.restrictScalars ℝ).convex
  obtain ⟨g, r, hV, hg⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv hc hx
  have hr := hV 0 V.zero_mem
  simp at hr
  have hne : g x ≠ 0 := by intro h; simp [h] at hg; linarith
  refine ⟨(a / g x) • g, ?_, ?_⟩
  · intro y hy
    have hy0 : g y = 0 := by
      by_contra h
      have hh := hV (((r : ℂ) / g y) • y) (V.smul_mem _ hy)
      simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ h] at hh
    simp [hy0]
  · simp [smul_eq_mul, hne]

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hcl : ∀ n, IsClosed (X n : Set E)) (B : Set E)
    (hesc : ∀ n, ∃ x ∈ B, x ∉ X n) :
    ∃ p : Seminorm ℂ E, (∀ n, Continuous (fun x : X n => p (x : E))) ∧ ¬ BddAbove (p '' B) := by
  classical
  choose x hxB hx using hesc
  choose f hann hvalue using fun n =>
    separate_stage hE (X n) (hcl n) (x n) (hx n) (n : ℂ)
  let P (y : E) := ∑' n, ‖f n y‖
  have trunc (n : ℕ) (y : E) (hy : y ∈ X n) :
      P y = ∑ k ∈ Finset.range n, ‖f k y‖ := by
    apply tsum_eq_sum
    intro k hk
    simp [hann k y (hmono (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))) hy)]
  let p : Seminorm ℂ E := Seminorm.of P (by
    intro y z
    obtain ⟨i, hi⟩ := hexh y
    obtain ⟨j, hj⟩ := hexh z
    have hy := hmono (le_max_left i j) hi
    have hz := hmono (le_max_right i j) hj
    rw [trunc _ _ ((X _).add_mem hy hz), trunc _ _ hy, trunc _ _ hz, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun k _ => by rw [map_add]; exact norm_add_le _ _)) (by
    intro c y
    obtain ⟨n, hn⟩ := hexh y
    rw [trunc _ _ ((X n).smul_mem c hn), trunc _ _ hn, Finset.mul_sum]
    simp [norm_smul])
  refine ⟨p, ?_, ?_⟩
  · intro n
    have heq : (fun y : X n => p (y : E)) = fun y : X n => ∑ k ∈ Finset.range n, ‖f k (y : E)‖ :=
      funext (fun y => trunc n y y.property)
    rw [heq]
    exact continuous_finset_sum _ (fun k _ => ((f k).continuous.comp continuous_subtype_val).norm)
  · rintro ⟨C, hC⟩
    obtain ⟨k, hk⟩ := exists_nat_gt C
    obtain ⟨j, hj⟩ := hexh (x k)
    let n := max j (k+1)
    have he := trunc n (x k) (hmono (le_max_left _ _) hj)
    have hk' : k ∈ Finset.range n := Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
    have hle := Finset.single_le_sum (f := fun i => ‖f i (x k)‖) (fun i _ => norm_nonneg _) hk'
    rw [← he, hvalue] at hle
    have hupper : P (x k) ≤ C := hC ⟨x k, hxB k, rfl⟩
    simpa using (not_lt_of_ge (hle.trans hupper)) (by simpa using hk)
