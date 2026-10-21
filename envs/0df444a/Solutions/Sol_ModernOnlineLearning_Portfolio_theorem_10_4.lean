-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.theorem_10_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:12:39.231898+00:00
-- url     : https://prove2.me/submissions/44a42407-a54d-4732-bb74-d079ef042162

import Definitions.Def_ModernOnlineLearning_Portfolio_Types
set_option autoImplicit false
open ModernOnlineLearning.Portfolio

theorem solution {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (n : Fin d → ℝ) (hn : n ∈ possibleTypes d T) :
    (typeClass (d := d) (T := T) n).card ≤
      ∏ i : Fin d, (n i) ^ (-(n i) * (T : ℝ)) := by
  classical
  have hTR : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  obtain ⟨j₀, hj₀⟩ := hn
  have hnonneg : ∀ i, 0 ≤ n i := by
    intro i
    rw [← hj₀]
    exact div_nonneg (Nat.cast_nonneg _) hTR.le
  have hsum : ∑ i, n i = 1 := by
    rw [← hj₀]
    unfold sequenceType
    rw [← Finset.sum_div]
    have hc : (∑ i : Fin d, ((Finset.univ.filter (fun t : Fin T => j₀ t = i)).card : ℝ)) = T := by
      have hh := Finset.sum_fiberwise (Finset.univ : Finset (Fin T)) j₀ (fun _ => (1 : ℝ))
      simpa using hh
    rw [hc, div_self hTR.ne']
  let p : ℝ := ∏ i : Fin d, (n i) ^ (n i * (T : ℝ))
  have hsame : ∀ j : Fin T → Fin d, sequenceType j = n →
      p = ∏ t : Fin T, n (j t) := by
    intro j hj
    have hc (i : Fin d) : n i * (T : ℝ) =
        ((Finset.univ.filter (fun t : Fin T => j t = i)).card : ℝ) := by
      rw [← hj]
      exact div_mul_cancel₀ _ hTR.ne'
    dsimp [p]
    simp_rw [hc, Real.rpow_natCast]
    have hh := Finset.prod_fiberwise' (Finset.univ : Finset (Fin T)) j n
    simpa using hh
  have hp : 0 < p := by
    rw [hsame j₀ hj₀]
    apply Finset.prod_pos
    intro t ht
    rw [← hj₀]
    apply div_pos _ hTR
    exact_mod_cast Finset.card_pos.mpr ⟨t, by simp⟩
  have hfull : ∑ j : Fin T → Fin d, ∏ t : Fin T, n (j t) = 1 := by
    rw [← Fintype.prod_sum (fun (_ : Fin T) (i : Fin d) => n i)]
    simp [hsum]
  have hpart : ∑ j ∈ typeClass (d := d) (T := T) n, (∏ t : Fin T, n (j t)) ≤ 1 := by
    rw [← hfull]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => Finset.prod_nonneg (fun t _ => hnonneg (j t)))
  have hcard : ((typeClass (d := d) (T := T) n).card : ℝ) * p ≤ 1 := by
    have heq : (∑ j ∈ typeClass (d := d) (T := T) n, (∏ t : Fin T, n (j t))) =
        ((typeClass (d := d) (T := T) n).card : ℝ) * p := by
      calc
        _ = ∑ j ∈ typeClass (d := d) (T := T) n, p := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (hsame j (Finset.mem_filter.mp hj).2).symm
        _ = _ := by simp
    rwa [heq] at hpart
  have hinv : (∏ i : Fin d, (n i) ^ (-(n i) * (T : ℝ))) = p⁻¹ := by
    calc
      _ = ∏ i : Fin d, ((n i) ^ (n i * (T : ℝ)))⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [neg_mul, Real.rpow_neg (hnonneg i)]
      _ = _ := by rw [Finset.prod_inv_distrib]
  rw [hinv]
  simpa only [one_div] using (le_div_iff₀ hp).mpr hcard


