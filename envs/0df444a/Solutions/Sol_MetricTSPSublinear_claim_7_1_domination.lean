-- Prove2me | solution 1 for MetricTSPSublinear.claim_7_1_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:09:33.858367+00:00
-- url     : https://prove2.me/submissions/ef8be8e8-45be-4811-86c5-eab8eec3a78e

import Mathlib

namespace MTSP71

lemma card_le_of_bound {m : ℕ} (S : Finset (Fin m)) (k : ℕ) (h : ∀ i ∈ S, (i : ℕ) ≤ k) :
    S.card ≤ k + 1 := by
  have : S.map Fin.valEmbedding ⊆ Finset.range (k + 1) := by
    intro x hx
    simp only [Finset.mem_map, Fin.valEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h i hi))
  simpa using Finset.card_le_card this

/-- sum of `1 - y` along a list with values in {0, 1/2, 1}. -/
lemma sum_eq {Seg : Type} (y : Seg → ℝ) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1) (L : List Seg) :
    (L.map (fun e => 1 - y e)).sum =
      ((Finset.univ.filter (fun i : Fin L.length => y (L.get i) = 0)).card : ℝ) +
        ((Finset.univ.filter (fun i : Fin L.length => y (L.get i) = 1 / 2)).card : ℝ) / 2 := by
  have h1 : (L.map (fun e => 1 - y e)).sum = ∑ i : Fin L.length, (1 - y (L.get i)) := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_get
    · simp
    · intro k h1 h2; simp
  rw [h1]
  have h2 : ∀ i : Fin L.length, 1 - y (L.get i) =
      (if y (L.get i) = 0 then (1 : ℝ) else 0) + (if y (L.get i) = 1 / 2 then (1 : ℝ) / 2 else 0) := by
    intro i
    rcases hy (L.get i) with h | h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp [Finset.sum_const, div_eq_mul_inv]

end MTSP71

open MTSP71 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) {ι Seg : Type} (σ : ℝ) (hσ : 0 < σ)
    (frag : Fin n → ι) (path : Fin n → List Seg) (y : Seg → ℝ)
    (hsymm : ∀ u v, d u v = d v u) (hy : ∀ e, y e = 0 ∨ y e = 1 / 2 ∨ y e = 1)
    (hcover : ∀ u v, frag u ≠ frag v → ∀ (i : Fin (path u).length) (j : Fin (path v).length),
      d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ → 1 ≤ y ((path u).get i) + y ((path v).get j))
    (hout : ∀ u v, frag u ≠ frag v → ((path u).length : ℝ) * σ ≤ d u v) :
    ∀ u v, frag u ≠ frag v →
      σ * ((path u).map (fun e => 1 - y e)).sum + σ * ((path v).map (fun e => 1 - y e)).sum ≤ d u v := by
  -- Z u = indices with y = 0, H u = indices with y = 1/2, Le u = indices with y ≤ 1/2
  let Z := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) = 0)
  let H := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) = 1 / 2)
  let Le := fun u => Finset.univ.filter (fun i : Fin (path u).length => y ((path u).get i) ≤ 1 / 2)
  have hLe : ∀ u, ((Le u).card : ℝ) = (Z u).card + (H u).card := by
    intro u
    have : Le u = Z u ∪ H u := by
      ext i; simp only [Le, Z, H, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro h; rcases hy ((path u).get i) with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · rw [h'] at h; norm_num at h
      · rintro (h | h) <;> rw [h] <;> norm_num
    rw [this, Finset.card_union_of_disjoint]
    · push_cast; ring
    · rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Z, H, Finset.mem_filter] at h1 h2; rw [h1.2] at h2; norm_num at h2
  have hlen : ∀ u (A : Finset (Fin (path u).length)), (A.card : ℝ) ≤ (path u).length := by
    intro u A; exact_mod_cast (Finset.card_le_univ A).trans (by simp)
  -- key bound (i)
  have key : ∀ u v, frag u ≠ frag v → σ * (((Z u).card : ℝ) + (Le v).card) ≤ d u v := by
    intro u v huv
    by_cases hZ : (Z u).Nonempty
    · by_cases hL : (Le v).Nonempty
      · set i := (Z u).max' hZ
        set j := (Le v).max' hL
        have hi : y ((path u).get i) = 0 := (Finset.mem_filter.mp ((Z u).max'_mem hZ)).2
        have hj : y ((path v).get j) ≤ 1 / 2 := (Finset.mem_filter.mp ((Le v).max'_mem hL)).2
        have hnot : ¬ d u v < ((i : ℝ) + 1 + ((j : ℝ) + 1)) * σ := by
          intro hlt; have := hcover u v huv i j hlt; linarith
        have hci : ((Z u).card : ℝ) ≤ (i : ℝ) + 1 := by
          exact_mod_cast card_le_of_bound (Z u) i (fun k hk => Fin.le_def.mp ((Z u).le_max' k hk))
        have hcj : ((Le v).card : ℝ) ≤ (j : ℝ) + 1 := by
          exact_mod_cast card_le_of_bound (Le v) j (fun k hk => Fin.le_def.mp ((Le v).le_max' k hk))
        push Not at hnot
        nlinarith
      · rw [Finset.not_nonempty_iff_eq_empty] at hL
        rw [hL, Finset.card_empty]; push_cast
        have := hout u v huv; have := hlen u (Z u); nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ
      rw [hZ, Finset.card_empty]; push_cast
      have := hout v u (Ne.symm huv); have := hlen v (Le v); rw [hsymm]; nlinarith
  intro u v huv
  have k1 := key u v huv
  have k2 := key v u (Ne.symm huv)
  rw [← hsymm u v] at k2
  rw [sum_eq y hy (path u), sum_eq y hy (path v)]
  rw [hLe] at k1 k2
  change σ * (((Z u).card : ℝ) + ((H u).card : ℝ) / 2) + σ * (((Z v).card : ℝ) + ((H v).card : ℝ) / 2) ≤ d u v
  nlinarith
