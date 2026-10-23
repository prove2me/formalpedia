-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_simplex_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:19:43.938675+00:00
-- url     : https://prove2.me/submissions/83c529a9-25cf-4cbc-b991-a57460b0b1f0

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

private lemma x8_compare (n K : ℕ) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (a : ℝ) (ha : 0 < a) (hvol : (K : ℝ) * a ^ n * (∏ i, w i) / (∏ i, v i) < 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      Set.Finite {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ (N : ℝ)} ∧
      Set.Finite {b : Fin n →₀ ℕ | (∑ i, (b i : ℝ) * v i) < a * (N : ℝ)} ∧
      Set.ncard {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ (N : ℝ)} >
        K * Set.ncard {b : Fin n →₀ ℕ | (∑ i, (b i : ℝ) * v i) < a * (N : ℝ)} := by
  have hPw : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have hPv : 0 < ∏ i, v i := Finset.prod_pos fun i _ => hv i
  have hF : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have ht := ((x8_tendsto n a (∑ i, v i)).const_mul (K : ℝ)).mul_const ((∏ i, w i) / (∏ i, v i))
  have hlim : (K : ℝ) * a ^ n * ((∏ i, w i) / (∏ i, v i)) < 1 := by
    rw [← mul_div_assoc]; exact hvol
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    ((ht.eventually (gt_mem_nhds hlim)).and (Filter.eventually_ge_atTop 1))
  refine ⟨N1, fun N hN => ?_⟩
  obtain ⟨h1, hN0⟩ := hN1 N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hpow : (0 : ℝ) < (N : ℝ) ^ n := pow_pos hNpos n
  obtain ⟨hfS, hlowS, -⟩ := x8_count w hw (N : ℝ) hNpos.le
  obtain ⟨hfT, hupT⟩ := x8_strict v hv (a * N) (by positivity)
  refine ⟨hfS, hfT, ?_⟩
  set X := (a * N + ∑ i, v i) ^ n with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ a * N + ∑ i, v i :=
      add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hv i).le)
    positivity
  -- from h1 : K * (X / N^n) * (Pw / Pv) < 1
  have key : (K : ℝ) * X * (∏ i, w i) < (N : ℝ) ^ n * (∏ i, v i) := by
    have h1' : (K : ℝ) * (X / (N : ℝ) ^ n) * ((∏ i, w i) / (∏ i, v i)) < 1 := h1
    have e : (K : ℝ) * (X / (N : ℝ) ^ n) * ((∏ i, w i) / (∏ i, v i)) =
        ((K : ℝ) * X * (∏ i, w i)) / ((N : ℝ) ^ n * (∏ i, v i)) := by
      field_simp
    rw [e, div_lt_one (by positivity)] at h1'
    exact h1'
  have key2 : (K : ℝ) * (X / ((Nat.factorial n : ℝ) * ∏ i, v i)) <
      (N : ℝ) ^ n / ((Nat.factorial n : ℝ) * ∏ i, w i) := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (K : ℝ) * X * (∏ i, w i) * (Nat.factorial n : ℝ) <
        (N : ℝ) ^ n * (∏ i, v i) * (Nat.factorial n : ℝ) := mul_lt_mul_of_pos_right key hF
    nlinarith [this]
  have hfinal : (K : ℝ) * (Set.ncard {b : Fin n →₀ ℕ | (∑ i, (b i : ℝ) * v i) < a * (N : ℝ)} : ℝ) <
      (Set.ncard {m : Fin n →₀ ℕ | (∑ i, (m i : ℝ) * w i) ≤ (N : ℝ)} : ℝ) := by
    calc _ ≤ (K : ℝ) * (X / ((Nat.factorial n : ℝ) * ∏ i, v i)) :=
          mul_le_mul_of_nonneg_left hupT (Nat.cast_nonneg K)
      _ < _ := key2
      _ ≤ _ := hlowS
  exact_mod_cast hfinal

theorem solution
    (n : Nat) (W : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real))
    (c ε : Real) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      Set.Finite {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) < c * (N : Real)} ∧
      ((Set.ncard {m : Fin n →₀ Nat |
        (∑ i : Fin n, (m i : Real) * (W i : Real)) < c * (N : Real)} : Nat) : Real) <
        (c ^ n / ((Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real))) + ε) * (N : Real) ^ n := by
  set D := (Nat.factorial n : Real) * (∏ i : Fin n, (W i : Real)) with hD
  have hD0 : 0 < D := mul_pos (by exact_mod_cast Nat.factorial_pos n)
    (Finset.prod_pos fun i _ => hW i)
  have ht := x8_tendsto n c (∑ i, (W i : ℝ))
  have hlt : c ^ n < c ^ n + ε * D := by nlinarith
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    ((ht.eventually (gt_mem_nhds hlt)).and (Filter.eventually_ge_atTop 1))
  refine ⟨N1, fun N hN => ?_⟩
  obtain ⟨h1, hN0⟩ := hN1 N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hpow : (0 : ℝ) < (N : ℝ) ^ n := pow_pos hNpos n
  obtain ⟨hf, hup⟩ := x8_strict (fun i => (W i : ℝ)) hW (c * N) (by positivity)
  refine ⟨hf, lt_of_le_of_lt hup ?_⟩
  have h1' : (c * N + ∑ i, (W i : ℝ)) ^ n < (c ^ n + ε * D) * (N : ℝ) ^ n := by
    have := h1
    rw [div_lt_iff₀ hpow] at this
    exact this
  rw [div_lt_iff₀ hD0]
  have e : (c ^ n / D + ε) * (N : ℝ) ^ n * D = (c ^ n + ε * D) * (N : ℝ) ^ n := by
    field_simp
  rw [e]; exact h1'
