-- Prove2me | solution 1 for ManipPotential.corollary_6_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:03:49.067457+00:00
-- url     : https://prove2.me/submissions/eede6618-465e-42a6-ab14-8e5bbbdff1ff

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycTotal
import Definitions.Def_ManipPotential_extNorm
import Definitions.Def_ManipPotential_delta
import Definitions.Def_ManipPotential_cycL
import Theorems.Thm_ManipPotential_lemma_6_6

open ManipPotential

namespace C67Aux

lemma ell_apply {m : ℕ} [NeZero m] (j c : Fin m) : ell j c = j - c := by simp [ell]

lemma ell_inj {m : ℕ} [NeZero m] {a b : Fin m} (h : ell a = ell b) : a = b := by
  have := congrArg (fun e => e 0) h
  simpa [ell_apply] using this

lemma eq_of_wp_ell {m : ℕ} [NeZero m] (j c : Fin m)
    (h : Ranking.WeaklyPrefers (ell j) c j) : c = j := by
  unfold Ranking.WeaklyPrefers at h
  have hs : ell j j = 0 := by simp [ell_apply]
  rw [hs] at h
  have h0 : ell j c = 0 := le_antisymm h (Fin.le_def.2 (by simp))
  rw [ell_apply, sub_eq_zero] at h0
  exact h0.symm

lemma smul_unit_nonneg {m : ℕ} (a : ℚ) (r : Ranking m) (ha : 0 ≤ a) :
    (0 : Ranking m → ℚ) ≤ a • unitVec r := by
  intro t
  simp only [unitVec, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.single_apply]
  split_ifs <;> simp [ha]

lemma decomp {m : ℕ} [NeZero m] (P : Ranking m → ℚ) :
    P = cycL (fun k => P (ell k)) + ∑ s : ExtRanking m, P s.1 • unitVec s.1 := by
  funext r
  simp only [Pi.add_apply, cycL, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hr : ∃ k, ell k = r
  · obtain ⟨k, rfl⟩ := hr
    rw [Finset.sum_eq_single k, Finset.sum_eq_zero]
    · simp
    · intro s _; rw [if_neg]; exact fun e => s.2 k e
    · intro b _ hb; rw [if_neg]; exact fun e => hb (ell_inj e).symm
    · simp
  · push Not at hr
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨r, hr⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro e; exact hb (Subtype.ext e.symm)
    · simp
    · intro k _; rw [if_neg]; exact fun e => hr k e.symm

end C67Aux

open C67Aux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (P : Ranking m → ℚ) (hP : 0 ≤ P) (hX : 0 < cycTotal P) (j : Fin m)
    (hj : g P = j) :
    delta m K * cycTotal P - ((K : ℚ) + 1) * (1 - delta m K) * extNorm P ≤ P (ell j) := by
  have h9 := (lemma_6_6 hm K g hg).2.1
  obtain ⟨hF, hB, hC⟩ := hg
  have hlam : (0:ℚ) < (K:ℚ) + 1 := by positivity
  set x0 : Fin m → ℚ := fun k => P (ell k) with hx0
  have hcyc0 : (0 : Ranking m → ℚ) ≤ cycL x0 := by
    unfold cycL
    exact Finset.sum_nonneg (fun k _ => smul_unit_nonneg _ _ (hP _))
  have key : ∀ S : Finset (ExtRanking m),
      g (cycL x0 + ∑ s ∈ Finset.univ \ S, P s.1 • unitVec s.1
        + (((K:ℚ) + 1) * ∑ s ∈ S, P s.1) • unitVec (ell j)) = j := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sdiff_empty, Finset.sum_empty, mul_zero, zero_smul, add_zero]
      rw [← decomp P]; exact hj
    | insert s S hs ih =>
      set B : Ranking m → ℚ := cycL x0 + ∑ t ∈ Finset.univ \ insert s S, P t.1 • unitVec t.1
        + (((K:ℚ) + 1) * ∑ t ∈ S, P t.1) • unitVec (ell j) with hBdef
      have hB0 : (0 : Ranking m → ℚ) ≤ B := by
        refine add_nonneg (add_nonneg hcyc0 ?_) (smul_unit_nonneg _ _ ?_)
        · exact Finset.sum_nonneg (fun t _ => smul_unit_nonneg _ _ (hP _))
        · exact mul_nonneg hlam.le (Finset.sum_nonneg (fun t _ => hP _))
      have e1 : Finset.univ \ S = insert s (Finset.univ \ insert s S) := by
        ext t; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases h : t = s
        · subst h; simp [hs]
        · simp [h]
      have hsn : s ∉ Finset.univ \ insert s S := by simp
      have hold : cycL x0 + ∑ t ∈ Finset.univ \ S, P t.1 • unitVec t.1
          + (((K:ℚ) + 1) * ∑ t ∈ S, P t.1) • unitVec (ell j) = B + P s.1 • unitVec s.1 := by
        rw [e1, Finset.sum_insert hsn, hBdef]; abel
      have hnew : cycL x0 + ∑ t ∈ Finset.univ \ insert s S, P t.1 • unitVec t.1
          + (((K:ℚ) + 1) * ∑ t ∈ insert s S, P t.1) • unitVec (ell j)
          = B + (((K:ℚ) + 1) * P s.1) • unitVec (ell j) := by
        rw [Finset.sum_insert hs, hBdef, mul_add, add_smul]; abel
      rw [hold] at ih
      rw [hnew]
      rcases (hP s.1).lt_or_eq with hpos | hzero
      · have := hB B hB0 (ell j) s.1 (((K:ℚ) + 1) * P s.1) (P s.1)
          (mul_pos hlam hpos) hpos le_rfl
        rw [ih] at this
        exact eq_of_wp_ell _ _ this
      · have hz : P s.1 = 0 := by simpa using hzero.symm
        rw [hz, mul_zero, zero_smul]
        rw [hz, zero_smul] at ih
        exact ih
  have hall := key Finset.univ
  set Y : ℚ := ∑ s : ExtRanking m, P s.1 with hY
  simp only [Finset.sdiff_self, Finset.sum_empty, add_zero] at hall
  set x' : Fin m → ℚ := fun k => P (ell k) + if k = j then ((K:ℚ) + 1) * Y else 0 with hx'
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun s _ => hP _)
  have hcx : cycL x' = cycL x0 + (((K:ℚ) + 1) * Y) • unitVec (ell j) := by
    simp only [cycL, hx', hx0, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hx'0 : 0 ≤ x' := by
    intro k; simp only [hx', Pi.zero_apply]
    have := hP (ell k)
    split_ifs
    · exact add_nonneg (by simpa using this) (mul_nonneg hlam.le hY0)
    · simpa using this
  have hsum' : ∑ k, x' k = cycTotal P + ((K:ℚ) + 1) * Y := by
    simp only [hx', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      cycTotal]
  have hpos' : 0 < ∑ k, x' k := by rw [hsum']; positivity
  have hwin : g (cycL x') = j := by rw [hcx]; exact hall
  have := h9 x' hx'0 hpos' j hwin
  have hp2 : 0 < cycTotal P + ((K:ℚ) + 1) * Y := hsum' ▸ hpos'
  rw [hsum', le_div_iff₀ hp2] at this
  have hxj : x' j = P (ell j) + ((K:ℚ) + 1) * Y := by simp [hx']
  rw [hxj] at this
  have hext : extNorm P = Y := by
    unfold extNorm; rw [hY]; exact Finset.sum_congr rfl (fun s _ => abs_of_nonneg (hP _))
  rw [hext]
  nlinarith
