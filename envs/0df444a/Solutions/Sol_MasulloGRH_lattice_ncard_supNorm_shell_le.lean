-- Prove2me | solution 1 for MasulloGRH.lattice_ncard_supNorm_shell_le
-- status  : ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T17:43:13.65211+00:00
-- url     : https://prove2.me/submissions/9af5fe1e-ae63-4d3f-8bf3-cb64e2804823

import Mathlib

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

theorem solution
    (N : ℕ) (hN : 1 ≤ N) (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      {ξ : Fin N → ℝ | ξ ∈ Γ ∧ r ≤ ‖ξ‖ ∧ ‖ξ‖ < r + 1}.Finite ∧
      ({ξ : Fin N → ℝ | ξ ∈ Γ ∧ r ≤ ‖ξ‖ ∧ ‖ξ‖ < r + 1}.ncard : ℝ) ≤ C * r ^ (N - 1) := by
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ξ ∈ Γ, ξ ≠ 0 → δ ≤ ‖ξ‖ := by
    have hopen : IsOpen ({(0 : Γ)} : Set Γ) := isOpen_discrete _
    rcases isOpen_induced_iff.mp hopen with ⟨U, hUopen, hUeq⟩
    have h0U : (0 : Fin N → ℝ) ∈ U := by
      have : (0 : Γ) ∈ Subtype.val ⁻¹' U := by
        rw [hUeq]
        exact Set.mem_singleton 0
      exact this
    rcases Metric.isOpen_iff.mp hUopen 0 h0U with ⟨δ, hδpos, hball⟩
    refine ⟨δ, hδpos, fun ξ hξ hξ0 => ?_⟩
    by_contra! hlt
    have hmemU : ξ ∈ U := hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
    have hmem0 : (⟨ξ, hξ⟩ : Γ) ∈ ({(0 : Γ)} : Set Γ) := by
      rw [← hUeq]
      exact hmemU
    exact hξ0 (congr_arg Subtype.val hmem0)
  let c : ℝ := min (1 / 2 : ℝ) (δ / 3)
  have hcpos : 0 < c := lt_min (by norm_num) (by linarith)
  have hc_half : c ≤ 1 / 2 := min_le_left _ _
  have hc_δ : c ≤ δ / 3 := min_le_right _ _
  have hdisj : ∀ ξ₁ ∈ Γ, ∀ ξ₂ ∈ Γ, ξ₁ ≠ ξ₂ →
      Disjoint (Metric.ball ξ₁ c) (Metric.ball ξ₂ c) := by
    intro ξ₁ h₁ ξ₂ h₂ hne
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    rw [Metric.mem_ball] at hy₁ hy₂
    have hdiff_mem : ξ₁ - ξ₂ ∈ Γ := Γ.sub_mem h₁ h₂
    have hdiff_ne : ξ₁ - ξ₂ ≠ 0 := sub_ne_zero.mpr hne
    have hnorm := hδ (ξ₁ - ξ₂) hdiff_mem hdiff_ne
    have hdist : dist ξ₁ ξ₂ ≤ dist ξ₁ y + dist y ξ₂ := dist_triangle ξ₁ y ξ₂
    rw [dist_eq_norm, dist_comm ξ₁ y] at hdist
    linarith
  let C : ℝ := 2 * (1 + 2 * c) * (N : ℝ) * (2 * (2 + c)) ^ (N - 1) / (2 * c) ^ N
  refine ⟨C, fun r hr => ?_⟩
  let S : Set (Fin N → ℝ) := {ξ : Fin N → ℝ | ξ ∈ Γ ∧ r ≤ ‖ξ‖ ∧ ‖ξ‖ < r + 1}
  let M : ℝ := ((2 * (r + 1 + c)) ^ N - (2 * (r - c)) ^ N) / (2 * c) ^ N
  have hvol_ball : ∀ ξ : Fin N → ℝ,
      volume (Metric.ball ξ c) = ENNReal.ofReal ((2 * c) ^ N) := by
    intro ξ
    rw [volume_pi_ball ξ hcpos]
    simp_rw [Real.volume_ball]
    rw [Finset.prod_const, Finset.card_fin, ← ENNReal.ofReal_pow (by positivity)]
  have hvol_closed : ∀ R : ℝ, 0 ≤ R →
      volume (Metric.closedBall (0 : Fin N → ℝ) R) = ENNReal.ofReal ((2 * R) ^ N) := by
    intro R hR
    rw [volume_pi_closedBall (0 : Fin N → ℝ) hR]
    simp_rw [Real.volume_closedBall]
    rw [Finset.prod_const, Finset.card_fin, ← ENNReal.ofReal_pow (by positivity)]
  have hcard_le_M : ∀ t : Finset (Fin N → ℝ), (↑t : Set (Fin N → ℝ)) ⊆ S →
      (t.card : ℝ) ≤ M := by
    intro t ht
    have hsub_ann : ∀ ξ ∈ t, Metric.ball ξ c ⊆
        Metric.closedBall (0 : Fin N → ℝ) (r + 1 + c) \
          Metric.closedBall (0 : Fin N → ℝ) (r - c) := by
      intro ξ hξ y hy
      have hξS := ht hξ
      simp only [Set.mem_ofPred_eq, S] at hξS
      rw [Metric.mem_ball] at hy
      rw [Set.mem_sdiff, Metric.mem_closedBall, dist_zero_right,
        Metric.mem_closedBall, dist_zero_right, not_le]
      constructor
      · have htri : ‖y‖ ≤ ‖y - ξ‖ + ‖ξ‖ := by
          calc ‖y‖ = ‖(y - ξ) + ξ‖ := by ring_nf
            _ ≤ ‖y - ξ‖ + ‖ξ‖ := norm_add_le _ _
        rw [← dist_eq_norm] at htri
        linarith [hξS.2.2]
      · have htri : ‖ξ‖ ≤ ‖ξ - y‖ + ‖y‖ := by
          calc ‖ξ‖ = ‖(ξ - y) + y‖ := by ring_nf
            _ ≤ ‖ξ - y‖ + ‖y‖ := norm_add_le _ _
        rw [← dist_eq_norm, dist_comm] at htri
        linarith [hξS.2.1]
    have hpwd : (↑t : Set (Fin N → ℝ)).PairwiseDisjoint (fun ξ => Metric.ball ξ c) := by
      intro ξ₁ h₁ ξ₂ h₂ hne
      exact hdisj ξ₁ (ht h₁).1 ξ₂ (ht h₂).1 hne
    have hmeas : ∀ ξ ∈ t, MeasurableSet (Metric.ball ξ c) :=
      fun _ _ => measurableSet_ball
    have hle_ann : volume (⋃ ξ ∈ t, Metric.ball ξ c) ≤
        volume (Metric.closedBall (0 : Fin N → ℝ) (r + 1 + c) \
          Metric.closedBall (0 : Fin N → ℝ) (r - c)) :=
      measure_mono (Set.iUnion₂_subset hsub_ann)
    rw [measure_biUnion_finset hpwd hmeas] at hle_ann
    have hlhs : ∑ ξ ∈ t, volume (Metric.ball ξ c) =
        ENNReal.ofReal ((t.card : ℝ) * (2 * c) ^ N) := by
      simp_rw [hvol_ball]
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hrc_nonneg : 0 ≤ r - c := by linarith
    have hr1c_nonneg : 0 ≤ r + 1 + c := by linarith
    have hrhs :
        volume (Metric.closedBall (0 : Fin N → ℝ) (r + 1 + c) \
          Metric.closedBall (0 : Fin N → ℝ) (r - c)) =
          ENNReal.ofReal ((2 * (r + 1 + c)) ^ N - (2 * (r - c)) ^ N) := by
      have hfinB : volume (Metric.closedBall (0 : Fin N → ℝ) (r - c)) ≠ ⊤ := by
        rw [hvol_closed _ hrc_nonneg]
        exact ENNReal.ofReal_ne_top
      rw [measure_sdiff (Metric.closedBall_subset_closedBall (by linarith))
        measurableSet_closedBall.nullMeasurableSet hfinB,
        hvol_closed _ hr1c_nonneg, hvol_closed _ hrc_nonneg,
        ← ENNReal.ofReal_sub _ (pow_nonneg (by linarith) N)]
    rw [hlhs, hrhs] at hle_ann
    have hreal : (t.card : ℝ) * (2 * c) ^ N ≤ (2 * (r + 1 + c)) ^ N - (2 * (r - c)) ^ N := by
      exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr
        (pow_le_pow_left₀ (by linarith) (by linarith) N))).mp hle_ann
    exact (le_div_iff₀ (pow_pos (by linarith) N)).mpr hreal
  have hM_le : M ≤ C * r ^ (N - 1) := by
    let a : ℝ := 2 * (r + 1 + c)
    let b : ℝ := 2 * (r - c)
    have ha_nonneg : 0 ≤ a := by dsimp [a]; linarith
    have hb_nonneg : 0 ≤ b := by dsimp [b]; linarith
    have hba : b ≤ a := by dsimp [a, b]; linarith
    have hab : a - b = 2 * (1 + 2 * c) := by dsimp [a, b]; ring
    have hgeom : a ^ N - b ^ N = (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) * (a - b) :=
      (geom_sum₂_mul a b N).symm
    have hsum_le : ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) ≤ (N : ℝ) * a ^ (N - 1) := by
      calc ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)
          ≤ ∑ i ∈ Finset.range N, a ^ (N - 1) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hiN : i < N := Finset.mem_range.mp hi
            have h1 : b ^ (N - 1 - i) ≤ a ^ (N - 1 - i) :=
              pow_le_pow_left₀ hb_nonneg hba _
            have h2 : a ^ i * b ^ (N - 1 - i) ≤ a ^ i * a ^ (N - 1 - i) :=
              mul_le_mul_of_nonneg_left h1 (pow_nonneg ha_nonneg i)
            have hexp : i + (N - 1 - i) = N - 1 := by omega
            rwa [← pow_add, hexp] at h2
        _ = (N : ℝ) * a ^ (N - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have ha_le : a ≤ 2 * (2 + c) * r := by
      dsimp [a]
      nlinarith
    have ha_pow : a ^ (N - 1) ≤ (2 * (2 + c)) ^ (N - 1) * r ^ (N - 1) := by
      calc a ^ (N - 1) ≤ (2 * (2 + c) * r) ^ (N - 1) :=
            pow_le_pow_left₀ ha_nonneg ha_le (N - 1)
        _ = (2 * (2 + c)) ^ (N - 1) * r ^ (N - 1) := mul_pow _ _ _
    have hdiff_le : a ^ N - b ^ N ≤
        2 * (1 + 2 * c) * (N : ℝ) * (2 * (2 + c)) ^ (N - 1) * r ^ (N - 1) := by
      rw [hgeom, hab]
      have h1 : (∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) * (2 * (1 + 2 * c)) ≤
          ((N : ℝ) * a ^ (N - 1)) * (2 * (1 + 2 * c)) :=
        mul_le_mul_of_nonneg_right hsum_le (by linarith)
      have h2 : ((N : ℝ) * a ^ (N - 1)) * (2 * (1 + 2 * c)) ≤
          ((N : ℝ) * ((2 * (2 + c)) ^ (N - 1) * r ^ (N - 1))) * (2 * (1 + 2 * c)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact mul_le_mul_of_nonneg_left ha_pow (Nat.cast_nonneg N)
      linarith
    have hdiv : M ≤ (2 * (1 + 2 * c) * (N : ℝ) * (2 * (2 + c)) ^ (N - 1) * r ^ (N - 1)) /
        (2 * c) ^ N :=
      div_le_div_of_nonneg_right hdiff_le (pow_nonneg (by linarith) N)
    simpa [C, div_mul_eq_mul_div] using hdiv
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, htS, htcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Nat.floor M + 1)
    have h1 := hcard_le_M t htS
    rw [htcard] at h1
    have hlt : M < ((Nat.floor M + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one M
    linarith
  refine ⟨hfin, ?_⟩
  have hnc : S.ncard = hfin.toFinset.card := by
    rw [← Set.ncard_coe_finset hfin.toFinset, hfin.coe_toFinset]
  rw [hnc]
  exact (hcard_le_M hfin.toFinset (by rw [hfin.coe_toFinset])).trans hM_le
