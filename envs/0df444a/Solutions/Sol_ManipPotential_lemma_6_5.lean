-- Prove2me | solution 1 for ManipPotential.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:02:26.68349+00:00
-- url     : https://prove2.me/submissions/2c37ade0-0ed8-4f0c-8926-f47117ddf2c0

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_cycL
import Definitions.Def_ManipPotential_rr
import Theorems.Thm_ManipPotential_corollary_6_4

namespace ManipPotential.Lemma65Aux

open ManipPotential

lemma fin_sub_val {m : ℕ} (a b : Fin m) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else m - b.val + a.val := by
  have ha := a.isLt; have hb := b.isLt
  rw [Fin.val_sub]
  split_ifs with h
  · have : m - b.val + a.val = (a.val - b.val) + m := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

lemma cycL_add {m : ℕ} [NeZero m] (f h : Fin m → ℚ) : cycL (f + h) = cycL f + cycL h := by
  simp [cycL, add_smul, Finset.sum_add_distrib]

lemma cycL_sub {m : ℕ} [NeZero m] (f h : Fin m → ℚ) : cycL (f - h) = cycL f - cycL h := by
  simp [cycL, sub_smul, Finset.sum_sub_distrib]

lemma cycL_single {m : ℕ} [NeZero m] (a : Fin m) (v : ℚ) :
    cycL (Pi.single a v) = v • unitVec (ell a) := by
  unfold cycL
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hb; simp [hb]

lemma cycL_nonneg {m : ℕ} [NeZero m] (f : Fin m → ℚ) (hf : 0 ≤ f) : 0 ≤ cycL f := by
  intro r
  simp only [cycL, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hf i)
  simp only [unitVec, Pi.single_apply]
  split_ifs <;> norm_num

lemma ell_apply {m : ℕ} [NeZero m] (j c : Fin m) : (ell j) c = j - c := rfl

lemma rr_apply {m : ℕ} [NeZero m] (j c : Fin m) : (rr j) c = c - j := rfl

lemma eq_of_weak_top {m : ℕ} [NeZero m] (j c : Fin m)
    (h : Ranking.WeaklyPrefers (ell j) c j) : c = j := by
  unfold Ranking.WeaklyPrefers at h
  rw [ell_apply, ell_apply, sub_self, nonpos_iff_eq_zero] at h
  exact (sub_eq_zero.mp h).symm

def dd {m : ℕ} (j c : Fin m) : ℕ := (j - c).val

def WW {m : ℕ} (lam : ℚ) (x : Fin m → ℚ) (j : Fin m) (k : ℕ) : ℚ :=
  ∑ c, if 0 < dd j c ∧ dd j c ≤ k then x c / lam else 0

def yy {m : ℕ} [NeZero m] (lam : ℚ) (x : Fin m → ℚ) (j : Fin m) (k : ℕ) : Fin m → ℚ :=
  fun c => (if dd j c = 0 ∨ k < dd j c then x c else 0) + (if c = j + 1 then WW lam x j k else 0)

lemma dd_eq_zero {m : ℕ} [NeZero m] (j c : Fin m) : dd j c = 0 ↔ c = j := by
  unfold dd
  constructor
  · intro h
    have : j - c = 0 := Fin.ext h
    exact (sub_eq_zero.mp this).symm
  · intro h; subst h; simp

lemma dd_lt {m : ℕ} (j c : Fin m) : dd j c < m := (j - c).isLt

lemma dd_succ {m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin m) : dd j (j + 1) = m - 1 := by
  unfold dd
  have : j - (j + 1) = (0 : Fin m) - 1 := by abel
  rw [this, fin_sub_val, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  simp

lemma succ_ne {m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin m) : j + 1 ≠ j := by
  intro h
  have := dd_succ hm j
  rw [h, (dd_eq_zero j j).mpr rfl] at this
  omega

theorem lcomp {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (x : Fin m → ℚ) (hx : 0 ≤ x) (hx0 : x ≠ 0) (j : Fin m)
    (hj : g (cycL x) = j) :
    g (x j • unitVec (ell j) +
        (((∑ i, x i) - x j) / ((K : ℚ) + 1)) • unitVec (ell (j + 1))) = j := by
  set lam : ℚ := (K : ℚ) + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  have hxj : 0 < x j := by
    have := (corollary_6_4 hm K g hg x hx hx0).1
    rw [hj] at this
    simpa [supp] using this
  have hsucc := succ_ne (by omega) j
  have hdsucc := dd_succ (by omega) j
  have hWnn : ∀ k, 0 ≤ WW lam x j k := by
    intro k; unfold WW
    apply Finset.sum_nonneg; intro c _
    split_ifs
    · exact div_nonneg (hx c) hlam0.le
    · exact le_refl _
  have hynn : ∀ k, 0 ≤ yy lam x j k := by
    intro k c; unfold yy
    have : (0 : ℚ) ≤ x c := hx c
    have := hWnn k
    simp only [Pi.zero_apply]
    split_ifs <;> linarith
  have hyj : ∀ k, yy lam x j k j = x j := by
    intro k; unfold yy
    simp [(dd_eq_zero j j).mpr rfl, Ne.symm hsucc]
  have hy0 : yy lam x j 0 = x := by
    funext c; unfold yy
    have hW0 : WW lam x j 0 = 0 := by
      unfold WW
      apply Finset.sum_eq_zero; intro c _
      rw [if_neg]; omega
    rw [hW0, if_pos (by omega)]; simp
  -- the step
  have hstep : ∀ k (hk : k + 1 < m),
      yy lam x j (k + 1) = yy lam x j k - Pi.single (j - (⟨k + 1, hk⟩ : Fin m)) (x (j - ⟨k + 1, hk⟩)) +
        Pi.single (j + 1) (x (j - ⟨k + 1, hk⟩) / lam) := by
    intro k hk
    set h : Fin m := j - ⟨k + 1, hk⟩ with hh
    have hdc : ∀ c, dd j c = k + 1 ↔ c = h := by
      intro c; unfold dd
      constructor
      · intro hc
        have : j - c = ⟨k + 1, hk⟩ := Fin.ext hc
        rw [hh, ← this]; abel
      · intro hc; rw [hc, hh]; simp
    have hW : WW lam x j (k + 1) = WW lam x j k + x h / lam := by
      unfold WW
      have e0 : x h / lam = ∑ c, if c = h then x c / lam else 0 := by simp
      rw [e0, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : c = h
      · have := (hdc c).mpr hc
        rw [if_pos (show 0 < dd j c ∧ dd j c ≤ k + 1 by omega),
          if_neg (show ¬(0 < dd j c ∧ dd j c ≤ k) by omega), if_pos hc]
        ring
      · have := mt (hdc c).mp hc
        rw [if_neg hc]
        by_cases h1 : 0 < dd j c ∧ dd j c ≤ k
        · rw [if_pos h1, if_pos (show 0 < dd j c ∧ dd j c ≤ k + 1 by omega)]; ring
        · rw [if_neg h1, if_neg (show ¬(0 < dd j c ∧ dd j c ≤ k + 1) by omega)]; ring
    funext c
    unfold yy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hc : c = h
    · have := (hdc c).mpr hc
      rw [if_neg (show ¬(dd j c = 0 ∨ k + 1 < dd j c) by omega),
        if_pos (show dd j c = 0 ∨ k < dd j c by omega), if_pos hc]
      rw [hc]
      by_cases h1 : h = j + 1
      · rw [if_pos h1, if_pos h1, if_pos h1, hW]; ring
      · rw [if_neg h1, if_neg h1, if_neg h1]; ring
    · have := mt (hdc c).mp hc
      rw [if_neg hc]
      have e : (dd j c = 0 ∨ k + 1 < dd j c) ↔ (dd j c = 0 ∨ k < dd j c) := by omega
      by_cases h1 : c = j + 1
      · rw [if_pos h1, if_pos h1, if_pos h1, hW]
        by_cases h2 : dd j c = 0 ∨ k < dd j c
        · rw [if_pos (e.mpr h2), if_pos h2]; ring
        · rw [if_neg (mt e.mp h2), if_neg h2]; ring
      · rw [if_neg h1, if_neg h1, if_neg h1]
        by_cases h2 : dd j c = 0 ∨ k < dd j c
        · rw [if_pos (e.mpr h2), if_pos h2]; ring
        · rw [if_neg (mt e.mp h2), if_neg h2]; ring
  have key : ∀ k, k < m → g (cycL (yy lam x j k)) = j := by
    intro k
    induction k with
    | zero => intro _; rw [hy0]; exact hj
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      set e : Fin m := ⟨k + 1, hk⟩ with he
      set h : Fin m := j - e with hh
      have hdh : dd j h = k + 1 := by unfold dd; rw [hh]; simp [he]
      have hs := hstep k hk
      rcases (hx h).lt_or_eq with hxh | hxh
      · set z := yy lam x j k - Pi.single h (x h) with hz
        have hznn : 0 ≤ z := by
          intro c
          simp only [hz, Pi.sub_apply, Pi.single_apply, Pi.zero_apply]
          by_cases hc : c = h
          · subst hc
            unfold yy
            rw [if_pos (Or.inr (by omega)), if_pos rfl]
            have := hWnn k
            split_ifs <;> linarith
          · rw [if_neg hc]; simpa using hynn k c
        have hB := cycL_nonneg z hznn
        have e1 : cycL (yy lam x j k) = cycL z + x h • unitVec (ell h) := by
          rw [← cycL_single, ← cycL_add, hz, sub_add_cancel]
        have e2 : cycL (yy lam x j (k + 1)) = cycL z + (x h / lam) • unitVec (ell (j + 1)) := by
          rw [← cycL_single, ← cycL_add, hs, hz]
        have hbmp := hg.2.1 (cycL z) hB (ell h) (ell (j + 1)) (x h) (x h / lam) hxh
          (div_pos hxh hlam0) (by rw [mul_div_cancel₀ _ hlam0.ne'])
        rw [← e1, ← e2, ih] at hbmp
        set w := g (cycL (yy lam x j (k + 1))) with hw
        -- winner in support
        have hsupp : 0 < yy lam x j (k + 1) w := by
          have hne : yy lam x j (k + 1) ≠ 0 := by
            intro h0; have := congrFun h0 j; rw [hyj] at this; simp at this; linarith
          have := (corollary_6_4 hm K g hg _ (hynn (k + 1)) hne).1
          simpa [supp] using this
        by_contra hwj
        have hdw : k + 1 ≤ dd j w := by
          unfold yy at hsupp
          by_cases h1 : w = j + 1
          · rw [h1, hdsucc]; omega
          · rw [if_neg h1] at hsupp
            by_cases h2 : dd j w = 0 ∨ k + 1 < dd j w
            · rcases h2 with h2 | h2
              · exact absurd ((dd_eq_zero j w).mp h2) hwj
              · omega
            · rw [if_neg h2] at hsupp; simp at hsupp
        unfold Ranking.WeaklyPrefers at hbmp
        rw [ell_apply, ell_apply] at hbmp
        have q1 : h - w = (j - w) - e := by rw [hh]; abel
        have q2 : h - j = (0 : Fin m) - e := by rw [hh]; abel
        rw [q1, q2, Fin.le_def, fin_sub_val, fin_sub_val] at hbmp
        have hwlt := dd_lt j w
        unfold dd at hdw hwlt
        simp only [he, Fin.val_zero] at hbmp
        split_ifs at hbmp <;> omega
      · rw [hs, ← hxh]; simpa using ih
  have hfinal : yy lam x j (m - 1) =
      Pi.single j (x j) + Pi.single (j + 1) (((∑ i, x i) - x j) / lam) := by
    have hWf : WW lam x j (m - 1) = ((∑ i, x i) - x j) / lam := by
      unfold WW
      have : ∀ c, (if 0 < dd j c ∧ dd j c ≤ m - 1 then x c / lam else 0) =
          x c / lam - (if c = j then x c / lam else 0) := by
        intro c
        have := dd_lt j c
        by_cases hc : c = j
        · rw [if_pos hc, if_neg (by rw [(dd_eq_zero j c).mpr hc]; omega)]; ring
        · rw [if_neg hc, if_pos (by have := mt (dd_eq_zero j c).mp hc; omega)]; ring
      rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ j, ← Finset.sum_div]
      simp only [Finset.mem_univ, if_true]
      ring
    funext c
    unfold yy
    simp only [Pi.add_apply, Pi.single_apply]
    have := dd_lt j c
    by_cases hc : c = j
    · subst hc
      rw [if_pos (Or.inl ((dd_eq_zero c c).mpr rfl)), if_neg (Ne.symm hsucc), if_pos rfl,
        if_neg (Ne.symm hsucc)]
    · rw [if_neg (by have := mt (dd_eq_zero j c).mp hc; omega), if_neg hc, hWf]
  have := key (m - 1) (by omega)
  rw [hfinal, cycL_add, cycL_single, cycL_single] at this
  exact this

theorem rcomp {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) (i j : Fin m) (hij : i ≠ j) (xi xj : ℚ) (hxi : 0 < xi) (hxj : 0 < xj)
    (hwin : g (xi • unitVec (rr i) + xj • unitVec (rr j)) = i) :
    g ((((K : ℚ) + 1) * xi) • unitVec (ell i) +
        (xj / ((K : ℚ) + 1)) • unitVec (ell (i - 1))) = i := by
  set lam : ℚ := (K : ℚ) + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  have unit_nn : ∀ (r : Ranking m) (a : ℚ), 0 ≤ a → 0 ≤ a • (unitVec r : Ranking m → ℚ) := by
    intro r a ha s
    simp only [unitVec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.zero_apply]
    split_ifs <;> simp [ha]
  -- Step 1
  have hQ : g ((lam * xi) • unitVec (ell i) + xj • unitVec (rr j)) = i := by
    have h1 := hg.2.1 (xj • unitVec (rr j)) (unit_nn _ _ hxj.le) (ell i) (rr i) (lam * xi) xi
      (by positivity) hxi le_rfl
    rw [add_comm (xj • unitVec (rr j)) ((lam * xi) • unitVec (ell i)),
      add_comm (xj • unitVec (rr j)) (xi • unitVec (rr i)), hwin] at h1
    exact eq_of_weak_top i _ h1
  -- Step 2
  have h2 := hg.2.1 ((lam * xi) • unitVec (ell i)) (unit_nn _ _ (by positivity)) (rr j)
    (ell (i - 1)) xj (xj / lam) hxj (div_pos hxj hlam0) (by rw [mul_div_cancel₀ _ hlam0.ne'])
  rw [hQ] at h2
  set w := g ((lam * xi) • unitVec (ell i) + (xj / lam) • unitVec (ell (i - 1))) with hw
  have hne1 : i - 1 ≠ i := by
    intro h
    have : (1 : Fin m) = 0 := by
      have := congrArg (fun t => i - t) h; simpa using this.symm
    have h1 := congrArg Fin.val this
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h1
    simp at h1
  set z : Fin m → ℚ := Pi.single i (lam * xi) + Pi.single (i - 1) (xj / lam) with hz
  have hzc : cycL z = (lam * xi) • unitVec (ell i) + (xj / lam) • unitVec (ell (i - 1)) := by
    rw [hz, cycL_add, cycL_single, cycL_single]
  have hznn : 0 ≤ z := by
    intro c
    simp only [hz, Pi.add_apply, Pi.single_apply, Pi.zero_apply]
    have : 0 ≤ lam * xi := by positivity
    have : 0 ≤ xj / lam := by positivity
    split_ifs <;> linarith
  have hzne : z ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp only [hz, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true, Ne.symm hne1,
      if_false] at this
    have : 0 < lam * xi := by positivity
    linarith
  have hsupp := (corollary_6_4 hm K g hg z hznn hzne).1
  rw [hzc, ← hw] at hsupp
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hsupp
  by_contra hwi
  have hw1 : w = i - 1 := by
    by_contra hw1
    simp only [hz, Pi.add_apply, Pi.single_apply, hwi, hw1, if_false] at hsupp
    simp at hsupp
  unfold Ranking.WeaklyPrefers at h2
  rw [hw1, rr_apply, rr_apply] at h2
  have q : i - 1 - j = (i - j) - 1 := by abel
  rw [q, Fin.le_def, fin_sub_val (i - j) 1, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h2
  have hij' : (i - j).val ≠ 0 := by
    intro h0
    exact hij (sub_eq_zero.mp (Fin.ext h0))
  have := (i - j).isLt
  split_ifs at h2 <;> omega

end ManipPotential.Lemma65Aux

open ManipPotential in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ) (g : (Ranking m → ℚ) → Fin m)
    (hg : GAxioms K g) :
    (∀ x : Fin m → ℚ, 0 ≤ x → x ≠ 0 → ∀ j : Fin m, g (cycL x) = j →
      g (x j • unitVec (ell j) +
        (((∑ i, x i) - x j) / ((K : ℚ) + 1)) • unitVec (ell (j + 1))) = j) ∧
    (∀ i j : Fin m, i ≠ j → ∀ xi xj : ℚ, 0 < xi → 0 < xj →
      g (xi • unitVec (rr i) + xj • unitVec (rr j)) = i →
      g ((((K : ℚ) + 1) * xi) • unitVec (ell i) +
        (xj / ((K : ℚ) + 1)) • unitVec (ell (i - 1))) = i) :=
  ⟨fun x hx hx0 j hj => ManipPotential.Lemma65Aux.lcomp hm K g hg x hx hx0 j hj,
   fun i j hij xi xj hxi hxj hw => ManipPotential.Lemma65Aux.rcomp hm K g hg i j hij xi xj hxi hxj hw⟩
