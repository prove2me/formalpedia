-- Prove2me | solution 1 for MetricGeometry.exists_unique_nearest_of_isNPC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T20:55:26.00492+00:00
-- url     : https://prove2.me/submissions/755e6257-521f-4d4a-8daa-202771a9f005

import Definitions.Def_metric_npc_cone

open MetricGeometry Filter Topology

theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hnpc : IsNPC X) (hmid : HasMidpoints X)
    (C : Set X) (hC : IsClosed C) (hCne : C.Nonempty)
    (hconv : ∀ u ∈ C, ∀ v ∈ C, ∀ m, IsMidpoint m u v → m ∈ C)
    (x : X) :
    ∃ p, p ∈ C ∧ (∀ q ∈ C, dist x p ≤ dist x q) ∧
      ∀ p', p' ∈ C → (∀ q ∈ C, dist x p' ≤ dist x q) → p' = p := by
  classical
  set S : Set ℝ := (fun q => dist x q) '' C with hS
  have hSne : S.Nonempty := hCne.image _
  have hbdd : BddBelow S := ⟨0, by rintro _ ⟨q, -, rfl⟩; exact dist_nonneg⟩
  set d : ℝ := sInf S with hd
  have hd0 : 0 ≤ d := le_csInf hSne (by rintro _ ⟨q, -, rfl⟩; exact dist_nonneg)
  have hdle : ∀ q ∈ C, d ≤ dist x q := fun q hq => csInf_le hbdd ⟨q, hq, rfl⟩
  -- the key quadratic inequality on `C`
  have key : ∀ u ∈ C, ∀ v ∈ C, dist u v ^ 2 ≤ 2 * dist x u ^ 2 + 2 * dist x v ^ 2 - 4 * d ^ 2 := by
    intro u hu v hv
    obtain ⟨m, hm⟩ := hmid u v
    have hmC : m ∈ C := hconv u hu v hv m hm
    have hcn := hnpc u v m x hm
    have h1 : d ≤ dist x m := hdle m hmC
    have h2 : dist m x = dist x m := dist_comm m x
    have h3 : dist u x = dist x u := dist_comm u x
    have h4 : dist v x = dist x v := dist_comm v x
    rw [h2, h3, h4] at hcn
    nlinarith [hcn, h1, hd0, dist_nonneg (x := x) (y := m)]
  -- a minimizing sequence
  have hchoose : ∀ n : ℕ, ∃ q ∈ C, dist x q < d + 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨a, ha, hlt⟩ := exists_lt_of_csInf_lt hSne (by linarith : sInf S < d + 1 / (n + 1))
    obtain ⟨q, hq, rfl⟩ := ha
    exact ⟨q, hq, hlt⟩
  choose y hyC hylt using hchoose
  have heps_pos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have heps_anti : ∀ n m : ℕ, n ≤ m → (1 : ℝ) / (m + 1) ≤ 1 / (n + 1) := by
    intro n m h
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right h 1
  set b : ℕ → ℝ := fun N => 2 * Real.sqrt (2 * d * (1 / (N + 1)) + (1 / (N + 1)) ^ 2) with hbdef
  have hrad : ∀ N : ℕ, 0 ≤ 2 * d * (1 / (N + 1)) + ((1 : ℝ) / (N + 1)) ^ 2 := fun N => by
    have := heps_pos N; positivity
  have hbnn : ∀ N, 0 ≤ b N := fun N => by
    have h := Real.sqrt_nonneg (2 * d * (1 / (N + 1)) + ((1 : ℝ) / (N + 1)) ^ 2)
    simp only [hbdef]; linarith
  have hbsq : ∀ N, b N ^ 2 = 4 * (2 * d * (1 / (N + 1)) + ((1 : ℝ) / (N + 1)) ^ 2) := by
    intro N
    simp only [hbdef, mul_pow]
    rw [Real.sq_sqrt (hrad N)]
    ring
  have hbound : ∀ n m N : ℕ, N ≤ n → N ≤ m → dist (y n) (y m) ≤ b N := by
    intro n m N hn hm
    have h1 := key (y n) (hyC n) (y m) (hyC m)
    have hxn : dist x (y n) < d + 1 / (N + 1) :=
      lt_of_lt_of_le (hylt n) (by linarith [heps_anti N n hn])
    have hxm : dist x (y m) < d + 1 / (N + 1) :=
      lt_of_lt_of_le (hylt m) (by linarith [heps_anti N m hm])
    have hxn0 : (0 : ℝ) ≤ dist x (y n) := dist_nonneg
    have hxm0 : (0 : ℝ) ≤ dist x (y m) := dist_nonneg
    have hsq : dist (y n) (y m) ^ 2 ≤ b N ^ 2 := by
      rw [hbsq N]; nlinarith [h1, hxn, hxm, hxn0, hxm0, hd0, heps_pos N]
    nlinarith [hsq, dist_nonneg (x := y n) (y := y m), hbnn N]
  have heps_tendsto : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 2 * d * (1 / (N + 1)) + ((1 : ℝ) / (N + 1)) ^ 2)
        atTop (𝓝 0) := by
      simpa using (heps_tendsto.const_mul (2 * d)).add (heps_tendsto.pow 2)
    have h2 : Tendsto (fun N : ℕ =>
        Real.sqrt (2 * d * (1 / (N + 1)) + ((1 : ℝ) / (N + 1)) ^ 2)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [hbdef] using h2.const_mul 2
  have hcauchy : CauchySeq y := cauchySeq_of_le_tendsto_0 b hbound hb_tendsto
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hpC : p ∈ C := hC.mem_of_tendsto hp (Eventually.of_forall hyC)
  have hlim1 : Tendsto (fun n => dist x (y n)) atTop (𝓝 (dist x p)) :=
    tendsto_const_nhds.dist hp
  have hlim2 : Tendsto (fun n => dist x (y n)) atTop (𝓝 d) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ => d) (h := fun n : ℕ => d + 1 / (n + 1)) tendsto_const_nhds ?_ ?_ ?_
    · simpa using tendsto_const_nhds.add heps_tendsto
    · exact fun n => hdle (y n) (hyC n)
    · exact fun n => le_of_lt (hylt n)
  have hdp : dist x p = d := tendsto_nhds_unique hlim1 hlim2
  refine ⟨p, hpC, fun q hq => by rw [hdp]; exact hdle q hq, ?_⟩
  intro p' hp'C hp'min
  have h1 : dist x p' ≤ d := by rw [← hdp]; exact hp'min p hpC
  have h2 : d ≤ dist x p' := hdle p' hp'C
  have h3 : dist x p' = d := le_antisymm h1 h2
  have h4 := key p' hp'C p hpC
  rw [h3, hdp] at h4
  have hz : dist p' p = 0 := by nlinarith [h4, dist_nonneg (x := p') (y := p)]
  exact dist_eq_zero.mp hz
