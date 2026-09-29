-- Prove2me | solution 1 for IPProximity.Eisenbrand.fractional_part_split
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:01:57.15806+00:00
-- url     : https://prove2.me/submissions/f857ad54-3283-42bd-9caa-e2d37c7dd884

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope



namespace IPProximity.Eisenbrand

/-- at an extreme point, the strictly-interior coordinates number at most m -/
theorem vertex_card_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) :
    (Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ))).card ≤ m := by
  classical
  set F := Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ)) with hF
  by_contra hlt
  push_neg at hlt
  let E : (F → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => if h : i ∈ F then LinearMap.proj (⟨i, h⟩ : F) else 0)
  let L : (F → ℝ) →ₗ[ℝ] (Fin m → ℝ) := (A.map (Int.cast : ℤ → ℝ)).mulVecLin ∘ₗ E
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp [Module.finrank_fin_fun]
    exact hlt
  obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set v := E w with hv
  have hAv : (A.map (Int.cast : ℤ → ℝ)).mulVec v = 0 := by
    have := LinearMap.mem_ker.mp hwk
    simpa [L] using this
  have hvF : ∀ i, i ∉ F → v i = 0 := by
    intro i hi; simp [hv, E, hi]
  have hv0 : v ≠ 0 := by
    intro h; apply hw0; funext ⟨i, hi⟩
    have := congrFun h i
    simpa [hv, E, hi] using this
  have hmem := hx.1
  -- eventually good
  have hev : ∀ᶠ t in nhds (0:ℝ), ∀ i, 0 ≤ x i + t * v i ∧ x i + t * v i ≤ (u i : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ F
    · have hi' := (Finset.mem_filter.mp hi).2
      have hc : Continuous (fun t : ℝ => x i + t * v i) := by continuity
      have h1 : ∀ᶠ t in nhds (0:ℝ), x i + t * v i ∈ Set.Ioo 0 (u i : ℝ) := by
        apply hc.continuousAt.preimage_mem_nhds
        apply Ioo_mem_nhds <;> simp [hi'.1, hi'.2]
      filter_upwards [h1] with t ht
      exact ⟨ht.1.le, ht.2.le⟩
    · filter_upwards with t
      simp [hvF i hi, hmem.2 i]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hp := hball (y := ε/2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have hm := hball (y := -(ε/2)) (by rw [Real.dist_eq]; simp; rw [abs_of_pos (by linarith)]; linarith)
  have hin : ∀ t : ℝ, (∀ i, 0 ≤ x i + t * v i ∧ x i + t * v i ≤ (u i : ℝ)) →
      (x + t • v) ∈ lpPolytope A b u := by
    intro t ht
    refine ⟨?_, fun i => by simpa [mul_comm] using ht i⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hmem.1]; simp
  have hseg : x ∈ openSegment ℝ (x + (ε/2) • v) (x + (-(ε/2)) • v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i; simp; ring
  have := hx.2 (hin _ hp) (hin _ hm) hseg
  apply hv0
  have h2 : (ε/2) • v = 0 := by
    have := congrArg (fun y => y - x) this; simpa using this
  rcases smul_eq_zero.mp h2 with h | h
  · linarith
  · exact h


theorem int_split_core (m : ℕ) (Δ : ℤ) (hΔ : 0 ≤ Δ) (v : ℤ) (hv : |v| ≤ Δ * m) :
    ∃ w : Fin m → ℤ, (∀ j, |w j| ≤ Δ) ∧ ∑ j, w j = v := by
  let f : ℕ → ℤ := fun k => max (-(Δ * k)) (min (Δ * k) v)
  refine ⟨fun j => f (j + 1) - f j, ?_, ?_⟩
  · intro j
    simp only [f]
    push_cast
    generalize (j : ℕ) = k
    have : Δ * ((k:ℤ) + 1) = Δ * k + Δ := by ring
    rw [this]
    generalize Δ * (k:ℤ) = a
    rw [abs_le]
    constructor <;> omega
  · rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j), Finset.sum_range_sub]
    simp only [f]
    rw [abs_le] at hv
    push_cast
    generalize Δ * (m:ℤ) = a at hv ⊢
    omega

theorem fps_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) (z : Fin n → ℤ) :
    let r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋
    let frac : Fin n → ℝ := fun i => x i - (r i : ℝ)
    (∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m) ∧
      ∃ w : Fin m → Fin m → ℤ, (∀ j i, |w j i| ≤ (Δ : ℤ)) ∧
        ∀ i, ∑ j, (w j i : ℝ) = (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i := by
  classical
  intro r frac
  set F := Finset.univ.filter (fun i => 0 < x i ∧ x i < (u i : ℝ)) with hF
  have hcard : F.card ≤ m := vertex_card_core A b u x hx
  have hmem := hx.1
  have hfrac0 : ∀ i, i ∉ F → frac i = 0 := by
    intro i hi
    have hint : ∃ k : ℤ, x i = k := by
      by_cases h0 : x i = 0
      · exact ⟨0, by simp [h0]⟩
      by_cases h1 : x i = (u i : ℝ)
      · exact ⟨u i, by simp [h1]⟩
      exfalso; apply hi
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_of_le_of_ne (hmem.2 i).1 (Ne.symm h0), lt_of_le_of_ne (hmem.2 i).2 h1⟩
    obtain ⟨k, hk⟩ := hint
    simp only [frac, r, hk]
    split_ifs <;> simp
  have hfrac1 : ∀ i, |frac i| ≤ 1 := by
    intro i
    simp only [frac, r]
    split_ifs
    · have h1 := Int.le_ceil (x i); have h2 := Int.ceil_lt_add_one (x i)
      rw [abs_le]; constructor <;> linarith
    · have h1 := Int.floor_le (x i); have h2 := Int.lt_floor_add_one (x i)
      rw [abs_le]; constructor <;> linarith
  have hbound : ∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m := by
    intro i
    rw [Pi.neg_apply, abs_neg]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← Finset.sum_subset (Finset.subset_univ F) (fun j _ hj => by simp [hfrac0 j hj])]
    calc |∑ j ∈ F, (A i j : ℝ) * frac j| ≤ ∑ j ∈ F, |(A i j : ℝ) * frac j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ F, (Δ : ℝ) := by
          apply Finset.sum_le_sum; intro j _
          rw [abs_mul]
          have h1 : |(A i j : ℝ)| ≤ Δ := by
            have := hΔ i j; rw [← Int.cast_abs]; exact_mod_cast this
          have h2 := hfrac1 j
          calc |(A i j : ℝ)| * |frac j| ≤ Δ * 1 :=
                mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
            _ = Δ := mul_one _
      _ = (Δ : ℝ) * F.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (Δ : ℝ) * m := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); exact_mod_cast hcard
  refine ⟨hbound, ?_⟩
  -- integrality
  let vZ : Fin m → ℤ := fun i => Matrix.mulVec A r i - b i
  have hvZ : ∀ i, (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i = (vZ i : ℝ) := by
    intro i
    have hb := congrFun hmem.1 i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hb
    simp only [vZ, frac, Pi.neg_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sub, Finset.sum_sub_distrib, hb]
    push_cast; ring
  have hsplit : ∀ i, ∃ w : Fin m → ℤ, (∀ j, |w j| ≤ Δ) ∧ ∑ j, w j = vZ i := by
    intro i
    apply int_split_core m Δ (by positivity)
    have := hbound i
    rw [hvZ i] at this
    have : ((|vZ i| : ℤ) : ℝ) ≤ ((Δ * m : ℤ) : ℝ) := by push_cast; exact this
    exact_mod_cast this
  choose w hw1 hw2 using hsplit
  refine ⟨fun j i => w i j, fun j i => hw1 i j, fun i => ?_⟩
  rw [hvZ i, ← hw2 i]; push_cast; rfl

end IPProximity.Eisenbrand

open IPProximity.Eisenbrand


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) (z : Fin n → ℤ) :
    let r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋
    let frac : Fin n → ℝ := fun i => x i - (r i : ℝ)
    (∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m) ∧
      ∃ w : Fin m → Fin m → ℤ, (∀ j i, |w j i| ≤ (Δ : ℤ)) ∧
        ∀ i, ∑ j, (w j i : ℝ) = (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i := by
  exact fps_core A b u Δ hΔ x hx z
