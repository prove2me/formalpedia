-- Prove2me | solution 1 for MPBSelect.theorem_3_zero_ratio
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:41:07.364123+00:00
-- url     : https://prove2.me/submissions/9cf946ae-6c20-4c58-ab53-cac83884d159

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_IsOptimal
import Definitions.Def_MPBSelect_Problem_ZeroRatio

namespace Aux_MPBSelect_zr
open MPBSelect

lemma G_div {k B : ℕ} (P : Problem k B) (β : Fin k → Fin B → ℝ) (s : ℝ) (hs : 0 < s)
    (i : Fin k) (b : Fin B) :
    P.G (fun i b => β i b / s) i b = P.G β i b / s := by
  unfold Problem.G
  have e1 : (0 < β i b / s) ↔ 0 < β i b := div_pos_iff_of_pos_right hs
  have e2 : (0 < β (P.ib b) b / s) ↔ 0 < β (P.ib b) b := div_pos_iff_of_pos_right hs
  by_cases h : 0 < β i b ∧ 0 < β (P.ib b) b
  · rw [if_pos (by rw [e1, e2]; exact h), if_pos h]
    obtain ⟨h1, h2⟩ := h
    field_simp
  · rw [if_neg (by rw [e1, e2]; exact h), if_neg h, zero_div]

lemma G_congr {k B : ℕ} (P : Problem k B) (α β : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (h1 : β i b = α i b) (h2 : β (P.ib b) b = α (P.ib b) b) : P.G β i b = P.G α i b := by
  unfold Problem.G
  rw [h1, h2]

lemma W_pos {k B : ℕ} (P : Problem k B) (i : Fin k) (b : Fin B) : 0 < P.W i b := by
  unfold Problem.W
  split_ifs
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)

lemma ldr_pos_of {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α) :
    0 < P.ldr α := by
  obtain ⟨⟨i0, b0⟩, _⟩ := P.Xi_nonempty
  have hk : (0 : ℝ) < k := by have := P.two_le_k; exact_mod_cast (by omega : 0 < k)
  have hB : (0 : ℝ) < B := by
    have : 0 < B := Fin.pos b0
    exact_mod_cast this
  set u : Fin k → Fin B → ℝ := fun _ _ => 1 / ((k : ℝ) * B) with hu
  have hpos : 0 < 1 / ((k : ℝ) * B) := by positivity
  have hfeas : u ∈ feasibleSet k B := by
    refine ⟨?_, fun i b => hpos.le⟩
    simp only [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine lt_of_lt_of_le ?_ (hα.2 u hfeas)
  unfold Problem.ldr
  rw [Finset.lt_inf'_iff]
  intro x hx
  have hx' : x.1 ≠ P.istar ∧ x.1 ≠ P.ib x.2 := by
    simpa [Problem.Xi] using hx
  refine mul_pos (W_pos P _ _) ?_
  unfold Problem.G
  rw [if_pos ⟨hpos, hpos⟩]
  have hy : P.y x.1 x.2 ≠ P.y (P.ib x.2) x.2 := fun h => hx'.2 (P.y_injective x.2 h)
  have hn : 0 < (P.y x.1 x.2 - P.y (P.ib x.2) x.2) ^ 2 := by
    have : P.y x.1 x.2 - P.y (P.ib x.2) x.2 ≠ 0 := sub_ne_zero.mpr hy
    positivity
  have hl1 := P.lam_pos x.1 x.2
  have hl2 := P.lam_pos (P.ib x.2) x.2
  positivity

end Aux_MPBSelect_zr

open MPBSelect Aux_MPBSelect_zr in
theorem solution {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (hα : P.IsOptimal α) : P.ZeroRatio α := by
  intro b0 hb0
  by_contra hne
  have hc : 0 < α P.istar b0 := lt_of_le_of_ne (hα.1.2 _ _) (Ne.symm hne)
  have hL := ldr_pos_of P α hα
  set c := α P.istar b0 with hcdef
  set β : Fin k → Fin B → ℝ := fun i b => if i = P.istar ∧ b = b0 then 0 else α i b with hβ
  have hβeq : ∀ i b, β i b = α i b - (if i = P.istar then 1 else 0) * (if b = b0 then c else 0) := by
    intro i b
    simp only [hβ]
    by_cases h1 : i = P.istar <;> by_cases h2 : b = b0
    · subst h1; subst h2; simp [hcdef]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hsum : ∑ i, ∑ b, β i b = 1 - c := by
    simp only [hβeq, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [hα.1.1]
  -- some element of Xi has positive α
  obtain ⟨⟨i1, b1⟩, hx1⟩ := P.Xi_nonempty
  have hx1' : i1 ≠ P.istar ∧ i1 ≠ P.ib b1 := by simpa [Problem.Xi] using hx1
  have hle1 : P.ldr α ≤ P.W i1 b1 * P.G α i1 b1 := Finset.inf'_le _ hx1
  have hGpos : 0 < P.G α i1 b1 := by
    have := W_pos P i1 b1
    by_contra hG
    push_neg at hG
    nlinarith
  have hαpos : 0 < α i1 b1 := by
    unfold Problem.G at hGpos
    by_contra h
    rw [if_neg (fun hh => h hh.1)] at hGpos
    exact lt_irrefl _ hGpos
  have hβnn : ∀ i b, 0 ≤ β i b := by
    intro i b; simp only [hβ]; split_ifs
    · exact le_rfl
    · exact hα.1.2 i b
  have hs : 0 < 1 - c := by
    rw [← hsum]
    have h1 : β i1 b1 = α i1 b1 := by simp [hβ, hx1'.1]
    calc (0 : ℝ) < β i1 b1 := h1 ▸ hαpos
      _ = ∑ b ∈ {b1}, β i1 b := by simp
      _ ≤ ∑ b, β i1 b := Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun b _ _ => hβnn i1 b)
      _ = ∑ i ∈ {i1}, ∑ b, β i b := by simp
      _ ≤ ∑ i, ∑ b, β i b := Finset.sum_le_sum_of_subset_of_nonneg (by simp)
            (fun i _ _ => Finset.sum_nonneg (fun b _ => hβnn i b))
  set s := 1 - c with hsdef
  have hs1 : s < 1 := by rw [hsdef]; linarith
  have hfeas : (fun i b => β i b / s) ∈ feasibleSet k B := by
    refine ⟨?_, fun i b => div_nonneg (hβnn i b) hs.le⟩
    simp only [← Finset.sum_div, hsum]
    exact div_self hs.ne'
  have hopt := hα.2 _ hfeas
  have : P.ldr α < P.ldr (fun i b => β i b / s) := by
    unfold Problem.ldr
    rw [Finset.lt_inf'_iff]
    intro x hx
    have hx' : x.1 ≠ P.istar ∧ x.1 ≠ P.ib x.2 := by simpa [Problem.Xi] using hx
    rw [G_div P β s hs]
    have hG : P.G β x.1 x.2 = P.G α x.1 x.2 := by
      apply G_congr
      · simp [hβ, hx'.1]
      · simp only [hβ]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hb0
        rw [← h2]; exact h1
    rw [hG]
    have hle : P.ldr α ≤ P.W x.1 x.2 * P.G α x.1 x.2 := Finset.inf'_le _ hx
    have hge : P.W x.1 x.2 * P.G α x.1 x.2 / s ≥ P.ldr α / s :=
      div_le_div_of_nonneg_right hle hs.le
    have : P.ldr α < P.ldr α / s := by
      rw [lt_div_iff₀ hs]; nlinarith
    rw [mul_div_assoc] at hge
    unfold Problem.ldr at this hge
    linarith
  linarith
