-- Prove2me | solution 1 for ManipPotential.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:03:48.555904+00:00
-- url     : https://prove2.me/submissions/13648140-ec95-45d6-8411-5dfc86a111b8

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_delta
import Theorems.Thm_ManipPotential_lemma_6_5
import Theorems.Thm_ManipPotential_corollary_6_4

open ManipPotential

namespace L66Aux

lemma ell_apply {m : ℕ} [NeZero m] (j c : Fin m) : ell j c = j - c := by simp [ell]

lemma ell_self {m : ℕ} [NeZero m] (j : Fin m) : ell j j = 0 := by simp [ell_apply]

lemma top_ell {m : ℕ} [NeZero m] (j : Fin m) : Ranking.top (ell j) = j := by
  unfold Ranking.top
  rw [Equiv.symm_apply_eq]; simp [ell]

lemma eq_of_wp_ell {m : ℕ} [NeZero m] (j c : Fin m)
    (h : Ranking.WeaklyPrefers (ell j) c j) : c = j := by
  unfold Ranking.WeaklyPrefers at h
  rw [ell_self] at h
  have h0 : ell j c = 0 := le_antisymm h (Fin.le_def.2 (by simp))
  rw [ell_apply, sub_eq_zero] at h0
  exact h0.symm

lemma one_ne_zero' {m : ℕ} [NeZero m] (hm : 3 ≤ m) : (1 : Fin m) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  exact one_ne_zero this

lemma sub_one_ne {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i : Fin m) : i - 1 ≠ i := by
  intro h; rw [sub_eq_self] at h; exact one_ne_zero' hm h

lemma add_one_ne {m : ℕ} [NeZero m] (hm : 3 ≤ m) (i : Fin m) : i + 1 ≠ i := by
  intro h; rw [add_eq_left] at h; exact one_ne_zero' hm h

lemma sum_pair {m : ℕ} [NeZero m] (f : Fin m → Ranking m) (i j : Fin m) (a b : ℚ) :
    ∑ k, (Pi.single i a + Pi.single j b : Fin m → ℚ) k • (unitVec (f k) : Ranking m → ℚ)
      = a • unitVec (f i) + b • unitVec (f j) := by
  simp [Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]

lemma sum_ite_const {m : ℕ} [NeZero m] (c : ℚ) (i : Fin m) :
    ∑ k : Fin m, (if k = i then (0:ℚ) else c) = ((m:ℚ) - 1) * c := by
  simp [Finset.sum_ite, Finset.filter_ne']
  left; rw [Nat.cast_sub NeZero.one_le]; simp

theorem part8 {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (i : Fin m) (xi xim : ℚ) (hxi : 0 < xi) (hxim : 0 ≤ xim)
    (hwin : g (xi • unitVec (ell i) + xim • unitVec (ell (i - 1))) = i - 1) :
    ((m : ℚ) - 2) * xi ≤ ((K : ℚ) + 1) ^ 5 * xim := by
  have hRC := (lemma_6_5 hm K g hg).2
  have hLC := (lemma_6_5 hm K g hg).1
  have h64 := corollary_6_4 hm K g hg
  obtain ⟨hF, hB, hC⟩ := hg
  set lam : ℚ := (K : ℚ) + 1 with hlam_def
  have hlam : 0 < lam := by positivity
  have hxim' : 0 < xim := by
    rcases hxim.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_smul, add_zero, hF _ _ hxi, top_ell] at hwin
      exact sub_one_ne hm i hwin.symm
  have h10 : ∀ j : Fin m, j ≠ i →
      g ((lam * (lam * xim)) • unitVec (ell j) + ((xi / lam) / lam) • unitVec (ell (j - 1)))
        = j := by
    intro j hji
    set x : Fin m → ℚ := Pi.single i (xi / lam) + Pi.single j (lam * xim) with hx
    have hx0 : 0 ≤ x := fun k => by
      simp only [hx, Pi.add_apply, Pi.zero_apply, Pi.single_apply]
      split_ifs <;> positivity
    have hxne : x ≠ 0 := by
      intro h
      have := congrFun h i
      simp [hx, Ne.symm hji] at this
      rcases this with h1 | h1 <;> linarith
    have hw := (h64 x hx0 hxne).2
    have hcyc : cycR x = (xi / lam) • unitVec (rr i) + (lam * xim) • unitVec (rr j) := by
      unfold cycR; rw [hx]; exact sum_pair _ _ _ _ _
    rw [hcyc] at hw
    unfold supp at hw; rw [Finset.mem_filter] at hw
    have hwij : g ((xi / lam) • unitVec (rr i) + (lam * xim) • unitVec (rr j)) = i ∨
        g ((xi / lam) • unitVec (rr i) + (lam * xim) • unitVec (rr j)) = j := by
      by_contra hcon; push Not at hcon
      have h2 := hw.2
      simp only [hx, Pi.add_apply, Pi.single_apply, hcon.1, hcon.2, if_false] at h2
      linarith
    rcases hwij with hwi | hwj
    · exfalso
      have := hRC i j (Ne.symm hji) (xi / lam) (lam * xim) (by positivity) (by positivity) hwi
      have e1 : lam * (xi / lam) = xi := by field_simp
      have e2 : lam * xim / lam = xim := by field_simp
      rw [e1, e2, hwin] at this
      exact sub_one_ne hm i this
    · have hwj' : g ((lam * xim) • unitVec (rr j) + (xi / lam) • unitVec (rr i)) = j := by
        rw [add_comm]; exact hwj
      exact hRC j i hji (lam * xim) (xi / lam) (by positivity) (by positivity) hwj'
  by_contra hcon
  push Not at hcon
  set c : ℚ := xi / lam / lam with hc
  have hc0 : 0 < c := by positivity
  set x : Fin m → ℚ := fun k => if k = i - 1 then 0 else c with hx
  have hx0 : 0 ≤ x := fun k => by
    simp only [hx, Pi.zero_apply]; split_ifs <;> positivity
  have hxi_ne : x i = c := by simp [hx, (sub_one_ne hm i).symm]
  have hxne : x ≠ 0 := fun h => by
    have := congrFun h i; rw [hxi_ne] at this; simp at this; linarith
  have hhs := (h64 x hx0 hxne).1
  unfold supp at hhs; rw [Finset.mem_filter] at hhs
  set h := g (cycL x) with hh
  have hh1 : h ≠ i - 1 := by
    intro e; have := hhs.2; rw [e] at this; simp [hx] at this
  have hxh : x h = c := by simp [hx, hh1]
  have hsum : ∑ k, x k = ((m:ℚ) - 1) * c := sum_ite_const c (i - 1)
  have hL := hLC x hx0 hxne h hh.symm
  rw [hxh, hsum] at hL
  have hj := h10 (h + 1) (fun e => hh1 (by rw [← e, add_sub_cancel_right]))
  rw [add_sub_cancel_right] at hj
  set a : ℚ := (((m:ℚ) - 1) * c - c) / lam - lam * (lam * xim) with ha_def
  have hm3 : (3:ℚ) ≤ m := by exact_mod_cast hm
  have ha : 0 < a := by
    have e : (((m:ℚ) - 1) * c - c) / lam = ((m:ℚ) - 2) * xi / lam ^ 3 := by
      rw [hc]; field_simp; ring
    rw [ha_def, e, sub_pos, lt_div_iff₀ (by positivity)]
    have : lam ^ 5 * xim = lam * (lam * xim) * lam ^ 3 := by ring
    linarith
  have hP' : (0 : Ranking m → ℚ) ≤ (lam * (lam * xim)) • unitVec (ell (h + 1)) + c • unitVec (ell h) := by
      intro r
      simp only [unitVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Pi.single_apply]
      split_ifs <;> positivity
  have hpos : 0 < ((lam * (lam * xim)) • unitVec (ell (h + 1)) + c • unitVec (ell h) :
      Ranking m → ℚ) (ell (h + 1)) := by
    simp only [unitVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> simp <;> positivity
  have hcp := hC _ hP' (ell (h + 1)) a ha hpos
  rw [hj] at hcp
  have hfin := eq_of_wp_ell _ _ hcp
  have heq : ((lam * (lam * xim)) • unitVec (ell (h + 1)) + c • unitVec (ell h) :
      Ranking m → ℚ) + a • unitVec (ell (h + 1))
      = c • unitVec (ell h) + ((((m:ℚ) - 1) * c - c) / lam) • unitVec (ell (h + 1)) := by
    have : (((m:ℚ) - 1) * c - c) / lam = lam * (lam * xim) + a := by rw [ha_def]; ring
    rw [this, add_smul]; abel
  rw [heq, hL] at hfin
  exact add_one_ne hm h hfin.symm

end L66Aux

open L66Aux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    (∀ (i : Fin m) (xi xim : ℚ), 0 < xi → 0 ≤ xim →
      g (xi • unitVec (ell i) + xim • unitVec (ell (i - 1))) = i - 1 →
      ((m : ℚ) - 2) * xi ≤ ((K : ℚ) + 1) ^ 5 * xim) ∧
    (∀ x : Fin m → ℚ, 0 ≤ x → 0 < ∑ j, x j → ∀ i : Fin m, g (cycL x) = i →
      delta m K ≤ x i / ∑ j, x j) ∧
    0 < delta m K := by
  have h8 := part8 hm K g hg
  have hLC := (lemma_6_5 hm K g hg).1
  have h64 := corollary_6_4 hm K g hg
  have hm3 : (3:ℚ) ≤ m := by exact_mod_cast hm
  have hlam : (0:ℚ) < (K:ℚ) + 1 := by positivity
  have hdpos : 0 < delta m K := by
    unfold delta; apply div_pos <;> nlinarith [pow_pos hlam 6]
  refine ⟨h8, ?_, hdpos⟩
  intro x hx0 hX i hi
  have hxne : x ≠ 0 := by intro h; simp [h] at hX
  have hs := (h64 x hx0 hxne).1
  rw [hi] at hs
  unfold supp at hs; rw [Finset.mem_filter] at hs
  have hle : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => hx0 j) (Finset.mem_univ i)
  have hd_le : delta m K ≤ 1 := by
    unfold delta; rw [div_le_one (by nlinarith [pow_pos hlam 6])]; nlinarith [pow_pos hlam 6]
  rcases hle.lt_or_eq with hlt | heq
  · have hL := hLC x hx0 hxne i hi
    have h8' := h8 (i + 1) (((∑ j, x j) - x i) / ((K:ℚ) + 1)) (x i)
      (div_pos (by linarith) hlam) hs.2.le
      (by rw [add_sub_cancel_right, add_comm]; exact hL)
    unfold delta
    rw [div_le_div_iff₀ (by nlinarith [pow_pos hlam 6]) hX]
    have e : ((m:ℚ) - 2) * (((∑ j, x j) - x i) / ((K:ℚ) + 1)) * ((K:ℚ) + 1)
        = ((m:ℚ) - 2) * ((∑ j, x j) - x i) := by field_simp
    have e2 : ((K:ℚ) + 1) ^ 5 * x i * ((K:ℚ) + 1) = ((K:ℚ) + 1) ^ 6 * x i := by ring
    have := mul_le_mul_of_nonneg_right h8' hlam.le
    rw [e, e2] at this
    nlinarith
  · rw [← heq, div_self hs.2.ne']; exact hd_le
