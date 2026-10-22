-- Prove2me | solution 1 for IoTFusion.KnownQuality.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:23:55.511796+00:00
-- url     : https://prove2.me/submissions/c2b9330d-3829-4082-b0b6-2aaf95c9a370

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model
import Theorems.Thm_IoTFusion_KnownQuality_proposition_2

open IoTFusion.KnownQuality Filter

theorem solution {n : ℕ} (P : IoTFusion.KnownQuality.Instance n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j) (s : ℕ → ℝ) (i j : Fin n) (hj : j ≠ i) :
    j ∈ longRunContacts P i s ↔ ∃ᶠ k in Filter.atTop, target P i s k = j := by
  have hform : ∀ k, fam P i s k j (s k) =
      psi1 P i j (s k) + stick (P.q i) (P.q j) * (count P i s j k : ℝ) :=
    fun k => ((proposition_2 P i j s (s k)).2 k)
  have hf : 0 < stick (P.q i) (P.q j) := by
    unfold stick; have := hq i; have := hq j; positivity
  have hpos : ∀ x, 0 ≤ psi1 P i j x := by
    intro x; unfold psi1; have := hv i j; have := hw i j; positivity
  have hle : ∀ x, psi1 P i j x ≤ P.v i j ^ 2 := by
    intro x; unfold psi1
    have hw2 : 0 < P.w i j ^ 2 := by have := hw i j; positivity
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (P.v i j), sq_nonneg x, mul_nonneg (sq_nonneg (P.v i j)) (sq_nonneg x),
      mul_nonneg (mul_nonneg (sq_nonneg (P.v i j)) (sq_nonneg (P.v i j))) (sq_nonneg x)]
  have hmono : Monotone (count P i s j) := by
    intro a b hab
    unfold count
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hab))
  constructor
  · rintro ⟨-, ht⟩
    by_contra hfr
    rw [not_frequently] at hfr
    obtain ⟨N, hN⟩ := eventually_atTop.mp hfr
    have hbound : ∀ k, count P i s j k ≤ N := by
      intro k
      unfold count
      calc ((Finset.range k).filter (fun l => target P i s l = j)).card
          ≤ (Finset.range N).card := by
            apply Finset.card_le_card
            intro l hl
            simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
            by_contra h
            exact hN l (by omega) hl.2
        _ = N := Finset.card_range N
    have := ht.eventually (eventually_gt_atTop (P.v i j ^ 2 + stick (P.q i) (P.q j) * N))
    obtain ⟨k, hk⟩ := this.exists
    rw [hform k] at hk
    have h1 := hle (s k)
    have h2 : (count P i s j k : ℝ) ≤ N := by exact_mod_cast hbound k
    nlinarith
  · intro hfr
    refine ⟨hj, ?_⟩
    have hinf : {l | target P i s l = j}.Infinite := Nat.frequently_atTop_iff_infinite.mp hfr
    have hcount : Tendsto (count P i s j) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq M
      obtain ⟨K, hK⟩ : ∃ K, ∀ l ∈ t, l < K := ⟨t.sup id + 1, fun l hl => by
        have := Finset.le_sup (f := id) hl; simp at this; omega⟩
      refine ⟨K, fun k hk => ?_⟩
      rw [← hcard]
      unfold count
      apply Finset.card_le_card
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hK l hl; omega, ht hl⟩
    have h2 : Tendsto (fun k => stick (P.q i) (P.q j) * (count P i s j k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hcount).const_mul_atTop hf
    refine tendsto_atTop_mono (fun k => ?_) h2
    rw [hform k]; linarith [hpos (s k)]
