-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_simplex_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:19:42.659533+00:00
-- url     : https://prove2.me/submissions/563d9088-db54-4acd-9baf-4d4144f35919

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_bounds

open scoped BigOperators

open OAI.PiExponent in
private lemma x8_mem_rws {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (a : Fin n → ℕ) :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  unfold realWeightedSimplex
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : w i * (a i : ℝ) ≤ H :=
      le_trans (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
        (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)) h
    have h2 : (a i : ℝ) ≤ H / w i := by
      rw [le_div_iff₀ (hw i)]; linarith
    have := Nat.le_floor h2
    omega

open OAI.PiExponent in
private lemma x8_set_eq {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) :
    {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ H} =
      (Finsupp.equivFunOnFinite.symm) '' (↑(realWeightedSimplex w H) : Set (Fin n → ℕ)) := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe]
  constructor
  · intro h
    refine ⟨Finsupp.equivFunOnFinite m, ?_, by simp⟩
    rw [x8_mem_rws w hw]
    simpa [mul_comm] using h
  · rintro ⟨a, ha, rfl⟩
    rw [x8_mem_rws w hw] at ha
    simpa [mul_comm] using ha

open OAI.PiExponent in
private lemma x8_count {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (hH : 0 ≤ H) :
    Set.Finite {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ H} ∧
    H ^ n / ((Nat.factorial n : ℝ) * ∏ i, w i) ≤
      (Set.ncard {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ H} : ℝ) ∧
    (Set.ncard {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ H} : ℝ) ≤
      (H + ∑ i, w i) ^ n / ((Nat.factorial n : ℝ) * ∏ i, w i) := by
  rw [x8_set_eq w hw H]
  have hc : Set.ncard ((Finsupp.equivFunOnFinite.symm) ''
      (↑(realWeightedSimplex w H) : Set (Fin n → ℕ))) = (realWeightedSimplex w H).card := by
    rw [Set.ncard_image_of_injective _ (Equiv.injective _), Set.ncard_coe_finset]
  rw [hc]
  have := OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds n w H hw hH
  exact ⟨Set.Finite.image _ (Finset.finite_toSet _), this.1, this.2⟩

private lemma x8_strict {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (hH : 0 ≤ H) :
    Set.Finite {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) < H} ∧
    (Set.ncard {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) < H} : ℝ) ≤
      (H + ∑ i, w i) ^ n / ((Nat.factorial n : ℝ) * ∏ i, w i) := by
  obtain ⟨hf, -, hle⟩ := x8_count w hw H hH
  have hsub : {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) < H} ⊆
      {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ H} := fun m hm => le_of_lt (show _ < H from hm)
  refine ⟨hf.subset hsub, le_trans ?_ hle⟩
  exact_mod_cast Set.ncard_le_ncard hsub hf

/-- `(c N + s)^n / N^n → c^n`. -/
private lemma x8_tendsto (n : ℕ) (c s : ℝ) :
    Filter.Tendsto (fun N : ℕ => (c * N + s) ^ n / (N : ℝ) ^ n) Filter.atTop (nhds (c ^ n)) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (c + s / (N : ℝ)) ^ n) Filter.atTop (nhds (c ^ n)) := by
    have := (tendsto_const_nhds (x := c)).add (tendsto_const_div_atTop_nhds_zero_nat s)
    simpa using this.pow n
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← div_pow]
  congr 1
  field_simp


theorem solution
    (n : Nat) (W : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real))
    (c ε : Real) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      Set.Finite {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ c * (N : Real)} ∧
      ((Set.ncard {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) ≤ c * (N : Real)} : Nat) : Real) >
        (c ^ n / ((Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real))) - ε) * (N : Real) ^ n := by
  refine ⟨1, fun N hN => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hf, hlow, -⟩ := x8_count (fun i => (W i : ℝ)) hW (c * N) (by positivity)
  refine ⟨hf, ?_⟩
  have hpow : (0 : ℝ) < (N : ℝ) ^ n := pow_pos hN' n
  calc (c ^ n / ((Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real))) - ε) * (N : Real) ^ n
      < (c ^ n / ((Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real)))) * (N : Real) ^ n := by
        nlinarith
    _ = (c * N) ^ n / ((Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real))) := by
        rw [mul_pow]; ring
    _ ≤ _ := hlow
