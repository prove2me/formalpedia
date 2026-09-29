-- Prove2me | solution 1 for HeldWolfeCrowder.CoreProblem.bounded_iterates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:35:06.100073+00:00
-- url     : https://prove2.me/submissions/af61fa3c-9e25-450d-a005-022d6ff80e59

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting



namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

lemma hwc_w_le {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (i : ι) :
    w c v p ≤ c i + ⟪p, v i⟫_ℝ :=
  Finset.inf'_le _ (Finset.mem_univ i)

lemma hwc_w_eq {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ∃ i, w c v p = c i + ⟪p, v i⟫_ℝ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
    (fun k => c k + ⟪p, v k⟫_ℝ)
  exact ⟨i, hi⟩


lemma hwc_coercive {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → EuclideanSpace ℝ (Fin n))
    (hdir : ∀ π : EuclideanSpace ℝ (Fin n), π ≠ 0 → ∃ k, ⟪π, v k⟫_ℝ < 0) :
    ∃ δ > 0, ∀ p : EuclideanSpace ℝ (Fin n), ∃ i, ⟪p, v i⟫_ℝ ≤ -δ * ‖p‖ := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun u => Finset.univ.inf' Finset.univ_nonempty (fun i => ⟪u, v i⟫_ℝ)
  have gc : Continuous g := by
    apply Continuous.finset_inf'_apply
    intro i _; fun_prop
  have gex : ∀ u, ∃ i, g u = ⟪u, v i⟫_ℝ := fun u => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι))
      (fun k => ⟪u, v k⟫_ℝ)
    exact ⟨i, hi⟩
  by_cases hS : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty
  · obtain ⟨u0, hu0, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
      hS gc.continuousOn
    have hneg : g u0 < 0 := by
      have hne : u0 ≠ 0 := by
        intro h; rw [h] at hu0; simp at hu0
      obtain ⟨k, hk⟩ := hdir u0 hne
      exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ k)) hk
    refine ⟨-g u0, by linarith, fun p => ?_⟩
    by_cases hp : p = 0
    · refine ⟨Classical.arbitrary ι, ?_⟩; simp [hp]
    · have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
      set u := ‖p‖⁻¹ • p
      have hu : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simp [u, norm_smul, hpn.ne']
      have : g u ≤ g u0 := hmax hu
      obtain ⟨i, hi⟩ := gex u
      refine ⟨i, ?_⟩
      have e : ⟪p, v i⟫_ℝ = ‖p‖ * ⟪u, v i⟫_ℝ := by
        simp only [u, inner_smul_left, conj_trivial]; field_simp
      rw [e]
      have : ⟪u, v i⟫_ℝ ≤ g u0 := hi ▸ this
      nlinarith
  · refine ⟨1, one_pos, fun p => ⟨Classical.arbitrary ι, ?_⟩⟩
    by_cases hp : p = 0
    · simp [hp]
    · exfalso; apply hS
      exact ⟨‖p‖⁻¹ • p, by simp [norm_smul, norm_pos_iff.2 hp |>.ne']⟩

theorem hwc_bdd_core {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n))
    (hdir : ∀ π : EuclideanSpace ℝ (Fin n), π ≠ 0 → ∃ k, ⟪π, v k⟫_ℝ < 0)
    (t : ℕ → ℝ) (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι)
    (hrun : IsSubgradientRun c v t π k) (ht : StepSizeCond t) :
    Bornology.IsBounded (Set.range π) := by
  obtain ⟨δ, hδ, hco⟩ := hwc_coercive v hdir
  set C := ∑ i, |c i|
  have hC : ∀ i, c i ≤ C := fun i => by
    have := Finset.single_le_sum (f := fun i => |c i|) (fun i _ => abs_nonneg (c i))
      (Finset.mem_univ i)
    exact le_trans (le_abs_self _) this
  set p := π 0
  set α := w c v p - 1
  set R := (C - α) / δ
  have hR : ∀ q, α ≤ w c v q → ‖q‖ ≤ R := by
    intro q hq
    obtain ⟨i, hi⟩ := hco q
    have h1 := hwc_w_le c v q i
    have h2 := hC i
    rw [le_div_iff₀ hδ]; nlinarith
  set M := ∑ i, ‖v i‖ ^ 2
  have hM : ∀ i, ‖v i‖ ^ 2 ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM (Classical.arbitrary ι))
  set Vn := ∑ i, ‖v i‖
  have hV : ∀ i, ‖v i‖ ≤ Vn := fun i =>
    Finset.single_le_sum (f := fun i => ‖v i‖) (fun _ _ => by positivity) (Finset.mem_univ i)
  obtain ⟨N1, hN1⟩ := (ht.1.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (M + 1) by positivity))).exists_forall_of_atTop
  set B := max ‖π N1 - p‖ (R + ‖p‖ + Vn)
  have hB : ∀ j, N1 ≤ j → ‖π j - p‖ ≤ B := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ j hj ih =>
      have htj := hN1 j hj
      have htp := hrun.step_pos j
      have ht1 : t j ≤ 1 := by
        have : 1 / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        linarith
      have htv : t j * ‖v (k j)‖ ^ 2 ≤ 1 := by
        calc t j * ‖v (k j)‖ ^ 2 ≤ 1 / (M + 1) * (M + 1) := by
              apply mul_le_mul htj.le (by linarith [hM (k j)]) (by positivity) (by positivity)
          _ = 1 := by field_simp
      by_cases hgood : α ≤ w c v (π j)
      · have h1 := hR _ hgood
        have e : π (j + 1) - p = π j + t j • v (k j) - p := by rw [hrun.step]
        rw [e]
        calc ‖π j + t j • v (k j) - p‖ ≤ ‖π j + t j • v (k j)‖ + ‖p‖ := norm_sub_le _ _
          _ ≤ ‖π j‖ + ‖t j • v (k j)‖ + ‖p‖ := by linarith [norm_add_le (π j) (t j • v (k j))]
          _ ≤ R + Vn + ‖p‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos htp]
              have := hV (k j)
              have : t j * ‖v (k j)‖ ≤ Vn := by nlinarith [norm_nonneg (v (k j))]
              linarith
          _ ≤ B := by rw [show R + Vn + ‖p‖ = R + ‖p‖ + Vn by ring]; exact le_max_right _ _
      · push Not at hgood
        have e : π (j + 1) - p = (π j - p) + t j • v (k j) := by rw [hrun.step]; abel
        have hin : ⟪π j - p, v (k j)⟫_ℝ ≤ -1 := by
          have h1 := hrun.index_min j
          unfold IsMinIndex at h1
          have h2 := hwc_w_le c v p (k j)
          rw [inner_sub_left]
          simp only [α] at hgood; linarith
        have hsq : ‖π (j + 1) - p‖ ^ 2 ≤ ‖π j - p‖ ^ 2 := by
          rw [e, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
            sq_abs]
          nlinarith
        have := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
        linarith
  rw [isBounded_iff_forall_norm_le]
  refine ⟨B + ‖p‖ + ∑ i ∈ Finset.range N1, ‖π i‖, ?_⟩
  rintro _ ⟨j, rfl⟩
  have hS0 : 0 ≤ ∑ i ∈ Finset.range N1, ‖π i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (le_max_left _ _)
  rcases le_or_gt N1 j with hj | hj
  · have := hB j hj
    have := norm_le_norm_add_norm_sub' (π j) p
    have : ‖π j‖ ≤ ‖p‖ + ‖π j - p‖ := by
      have h := norm_add_le p (π j - p); simp at h; exact h
    linarith
  · have := Finset.single_le_sum (f := fun i => ‖π i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 hj)
    linarith [norm_nonneg p]

end HeldWolfeCrowder.CoreProblem

open HeldWolfeCrowder.CoreProblem
open scoped InnerProductSpace

theorem solution {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (hw : BddAbove (Set.range (w c v)))
    (hdir : ∀ π : EuclideanSpace ℝ (Fin n), π ≠ 0 → ∃ k, ⟪π, v k⟫_ℝ < 0)
    (t : ℕ → ℝ) (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι)
    (hrun : IsSubgradientRun c v t π k) (ht : StepSizeCond t) :
    Bornology.IsBounded (Set.range π) := by
  exact hwc_bdd_core c v hdir t π k hrun ht
