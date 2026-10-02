-- Prove2me | solution 1 for HighDimProb.RandomMatrices.covering_numbers_of_euclidean_ball_and_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:28:13.282753+00:00
-- url     : https://prove2.me/submissions/e946b4a2-9416-48be-9fea-0a87ef8a2897

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Definitions.Def_HighDimProb_RandomMatrices_coveringNumber

set_option autoImplicit false

open MeasureTheory Metric in
/-- Volume packing bound: an `ε`-separated finite subset of the closed unit ball has at most
`(2/ε + 1)^n` points. -/
theorem p792_pack_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (C : Finset (EuclideanSpace ℝ (Fin n)))
    (hC : (↑C : Set (EuclideanSpace ℝ (Fin n))) ⊆ closedBall 0 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) :
    (C.card : ℝ) ≤ (2 / ε + 1) ^ n := by
  have hε2 : 0 < ε / 2 := by positivity
  have hd : Set.PairwiseDisjoint (↑C : Set (EuclideanSpace ℝ (Fin n)))
      (fun c => ball c (ε / 2)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ c ∈ C, ball c (ε / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    have hc1 : dist c 0 ≤ 1 := hC hc
    rw [mem_ball] at hzc ⊢
    calc dist z 0 ≤ dist z c + dist c 0 := dist_triangle _ _ _
      _ < ε / 2 + 1 := by linarith
      _ = 1 + ε / 2 := by ring
  have h2 := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub
  rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun c _ => Measure.addHaar_ball_of_pos volume c hε2),
    Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_ball_of_pos volume (0 : EuclideanSpace ℝ (Fin n)) (by positivity : (0:ℝ) < 1 + ε / 2),
    finrank_euclideanSpace_fin, ← mul_assoc] at h2
  have hV0 : (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ 0 :=
    (measure_ball_pos volume _ one_pos).ne'
  have hVt : (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h3 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 h2
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have heq : 2 / ε + 1 = (1 + ε / 2) / (ε / 2) := by field_simp
  rw [heq, div_pow, le_div_iff₀ (by positivity)]
  exact h4

open MeasureTheory HighDimProb.RandomMatrices in
/-- Every subset of the closed unit ball has a finite `ε`-net (inside it) of size at most
`(2/ε+1)^n`: a maximal-cardinality `ε`-separated subset. -/
theorem p792_exists_net (n : ℕ) (ε : ℝ) (hε : 0 < ε) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : K ⊆ Metric.closedBall 0 1) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)), IsEpsNet K (↑N : Set _) ε ∧
      (N.card : ℝ) ≤ (2 / ε + 1) ^ n := by
  classical
  let P : ℕ → Prop := fun m => ∃ C : Finset (EuclideanSpace ℝ (Fin n)),
    (↑C : Set _) ⊆ K ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) ∧ C.card = m
  let B : ℕ := ⌊(2 / ε + 1) ^ n⌋₊
  have hbound : ∀ m, P m → m ≤ B := by
    rintro m ⟨C, hCK, hsep, rfl⟩
    exact Nat.le_floor (p792_pack_bound n ε hε C (hCK.trans hK) hsep)
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  have hk : P (Nat.findGreatest P B) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨C, hCK, hsep, hcard⟩ := hk
  refine ⟨C, ⟨hCK, fun x hx => ?_⟩, p792_pack_bound n ε hε C (hCK.trans hK) hsep⟩
  by_contra hno
  push Not at hno
  have hxC : x ∉ C := by
    intro hxC
    have := hno x (Finset.mem_coe.2 hxC)
    rw [dist_self] at this
    linarith
  have hP1 : P (Nat.findGreatest P B + 1) := by
    refine ⟨insert x C, ?_, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hCK
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hno b (Finset.mem_coe.2 hb)
      · rw [dist_comm]; exact hno a (Finset.mem_coe.2 ha)
      · exact hsep a ha b hb hab
    · rw [Finset.card_insert_of_notMem hxC, hcard]
  have := Nat.le_findGreatest (hbound _ hP1) hP1
  omega

open MeasureTheory HighDimProb.RandomMatrices in
theorem p792_upper (n : ℕ) (ε : ℝ) (hε : 0 < ε) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : K ⊆ Metric.closedBall 0 1) :
    (coveringNumber K ε : ℝ) ≤ (2 / ε + 1) ^ n := by
  obtain ⟨N, hN, hcard⟩ := p792_exists_net n ε hε K hK
  have : coveringNumber K ε ≤ N.card := by
    unfold coveringNumber
    exact Nat.sInf_le ⟨N, rfl, hN⟩
  calc (coveringNumber K ε : ℝ) ≤ N.card := by exact_mod_cast this
    _ ≤ _ := hcard

open MeasureTheory HighDimProb.RandomMatrices in
theorem p792_lower (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (1 / ε) ^ n ≤ (coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ) := by
  obtain ⟨N0, hN0, -⟩ := p792_exists_net n ε hε (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    le_rfl
  have hne : {c : ℕ | ∃ net : Finset (EuclideanSpace ℝ (Fin n)), net.card = c ∧
      IsEpsNet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (↑net : Set _) ε}.Nonempty :=
    ⟨N0.card, N0, rfl, hN0⟩
  obtain ⟨N, hNc, hN⟩ := Nat.sInf_mem hne
  unfold coveringNumber
  rw [← hNc]
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ y ∈ N, Metric.closedBall y ε := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hN.2 x hx
    simp only [Set.mem_iUnion]
    exact ⟨y, Finset.mem_coe.1 hy, hxy⟩
  have h2 := (measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub).trans
    (measure_biUnion_finset_le N _)
  rw [Finset.sum_congr rfl (fun c _ => Measure.addHaar_closedBall volume c hε.le),
    Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_closedBall volume (0 : EuclideanSpace ℝ (Fin n)) zero_le_one,
    finrank_euclideanSpace_fin, ← mul_assoc] at h2
  have hV0 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hVt : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h3 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 h2
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  rw [one_pow] at h4
  rw [one_div_pow, div_le_iff₀ (by positivity)]
  exact h4

open HighDimProb.RandomMatrices in
theorem solution (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hε : 0 < ε) :
    (1 / ε) ^ n ≤ (coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ) ∧
    (coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ)
        ≤ (2 / ε + 1) ^ n ∧
    (coveringNumber (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ε : ℝ)
        ≤ (2 / ε + 1) ^ n := by
  refine ⟨p792_lower n ε hε, p792_upper n ε hε _ le_rfl, p792_upper n ε hε _ ?_⟩
  exact Metric.sphere_subset_closedBall
