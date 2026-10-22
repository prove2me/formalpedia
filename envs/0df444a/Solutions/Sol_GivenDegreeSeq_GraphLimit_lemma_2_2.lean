-- Prove2me | solution 1 for GivenDegreeSeq.GraphLimit.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:53.726651+00:00
-- url     : https://prove2.me/submissions/1099e10b-b0fc-4654-87c5-21ba6e883140

import Mathlib
import Definitions.Def_GivenDegreeSeq_GraphLimit_Phi
set_option autoImplicit false

theorem solution (n : ℕ) (d x y : Fin n → ℝ) (K : ℝ) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) :
    ∑ i, |GivenDegreeSeq.GraphLimit.phi d x i - GivenDegreeSeq.GraphLimit.phi d y i|
      ≤ 2 * Real.exp (2 * K) * ∑ i, |x i - y i| := by
  have hxk : ∀ k, |x k| ≤ K := fun k => by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm x k).trans hx
  have hyk : ∀ k, |y k| ≤ K := fun k => by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm y k).trans hy
  have hK0 : 0 ≤ K := (norm_nonneg x).trans hx
  set E : ℝ := Real.exp K with hEdef
  have hE : 0 < E := Real.exp_pos K
  have hE1 : 1 ≤ E := Real.one_le_exp hK0
  have hE2 : Real.exp (2 * K) = E * E := by rw [two_mul, Real.exp_add]
  have hEinv : Real.exp (-K) = E⁻¹ := by rw [hEdef, Real.exp_neg]
  -- basic facts about the exponential
  have hexp : ∀ u w : ℝ, w ≤ u → Real.exp u - Real.exp w ≤ Real.exp u * (u - w) := by
    intro u w _
    have h1 := Real.add_one_le_exp (w - u)
    have h2 : Real.exp (w - u) * Real.exp u = Real.exp w := by
      rw [← Real.exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos u).le
    nlinarith [Real.exp_pos u, Real.exp_pos w]
  -- every denominator is at least 2/E
  have hD : ∀ (z : Fin n → ℝ), (∀ k, |z k| ≤ K) → ∀ i j : Fin n,
      2 / E ≤ Real.exp (-z j) + Real.exp (z i) ∧ Real.exp (-z j) + Real.exp (z i) ≤ 2 * E := by
    intro z hz i j
    have h1 : E⁻¹ ≤ Real.exp (-z j) := by
      rw [← hEinv]; exact Real.exp_le_exp.mpr (by linarith [abs_le.mp (hz j)])
    have h2 : E⁻¹ ≤ Real.exp (z i) := by
      rw [← hEinv]; exact Real.exp_le_exp.mpr (by linarith [abs_le.mp (hz i)])
    have h3 : Real.exp (-z j) ≤ E := Real.exp_le_exp.mpr (by linarith [abs_le.mp (hz j)])
    have h4 : Real.exp (z i) ≤ E := Real.exp_le_exp.mpr (by linarith [abs_le.mp (hz i)])
    refine ⟨?_, by linarith⟩
    have : 2 / E = E⁻¹ + E⁻¹ := by field_simp; ring
    linarith
  -- key estimate for a single exponential
  have hclaim : ∀ (u w p p' : ℝ), 0 ≤ p → 0 ≤ p' → 2 / E ≤ Real.exp u + p →
      2 / E ≤ Real.exp w + p' →
      |Real.exp u - Real.exp w| / ((Real.exp u + p) * (Real.exp w + p')) ≤ E / 2 * |u - w| := by
    intro u w p p' hp hp' hD1 hD2
    have hDpos : 0 < Real.exp u + p := by have : 0 < 2 / E := by positivity
                                          linarith
    have hDpos' : 0 < Real.exp w + p' := by have : 0 < 2 / E := by positivity
                                            linarith
    have hinv1 : 1 / (Real.exp u + p) ≤ E / 2 := by
      rw [div_le_iff₀ hDpos]
      have : 1 ≤ E / 2 * (2 / E) := by field_simp; exact le_refl _
      calc (1 : ℝ) ≤ E / 2 * (2 / E) := this
        _ ≤ E / 2 * (Real.exp u + p) := mul_le_mul_of_nonneg_left hD1 (by positivity)
    have hinv2 : 1 / (Real.exp w + p') ≤ E / 2 := by
      rw [div_le_iff₀ hDpos']
      have : 1 ≤ E / 2 * (2 / E) := by field_simp; exact le_refl _
      calc (1 : ℝ) ≤ E / 2 * (2 / E) := this
        _ ≤ E / 2 * (Real.exp w + p') := mul_le_mul_of_nonneg_left hD2 (by positivity)
    rcases le_total (Real.exp w) (Real.exp u) with hle | hle
    · have hwu : w ≤ u := Real.exp_le_exp.mp hle
      have h1 : |Real.exp u - Real.exp w| ≤ Real.exp u * |u - w| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        calc Real.exp u - Real.exp w ≤ Real.exp u * (u - w) := hexp u w hwu
          _ ≤ Real.exp u * |u - w| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos u).le
      calc |Real.exp u - Real.exp w| / ((Real.exp u + p) * (Real.exp w + p'))
          ≤ Real.exp u * |u - w| / ((Real.exp u + p) * (Real.exp w + p')) := by
            gcongr
        _ = (Real.exp u / (Real.exp u + p)) * (1 / (Real.exp w + p')) * |u - w| := by
            field_simp
        _ ≤ 1 * (E / 2) * |u - w| := by
            have h3 : Real.exp u / (Real.exp u + p) ≤ 1 := by
              rw [div_le_one hDpos]; linarith
            have h4 : 0 ≤ Real.exp u / (Real.exp u + p) := by positivity
            gcongr
        _ = E / 2 * |u - w| := by ring
    · have hwu : u ≤ w := Real.exp_le_exp.mp hle
      have h1 : |Real.exp u - Real.exp w| ≤ Real.exp w * |u - w| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        calc -(Real.exp u - Real.exp w) = Real.exp w - Real.exp u := by ring
          _ ≤ Real.exp w * (w - u) := hexp w u hwu
          _ ≤ Real.exp w * |u - w| := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos w).le
            rw [abs_sub_comm]; exact le_abs_self _
      calc |Real.exp u - Real.exp w| / ((Real.exp u + p) * (Real.exp w + p'))
          ≤ Real.exp w * |u - w| / ((Real.exp u + p) * (Real.exp w + p')) := by
            gcongr
        _ = (Real.exp w / (Real.exp w + p')) * (1 / (Real.exp u + p)) * |u - w| := by
            field_simp
        _ ≤ 1 * (E / 2) * |u - w| := by
            have h3 : Real.exp w / (Real.exp w + p') ≤ 1 := by
              rw [div_le_one hDpos']; linarith
            have h4 : 0 ≤ Real.exp w / (Real.exp w + p') := by positivity
            gcongr
        _ = E / 2 * |u - w| := by ring
  -- difference of two r-values
  have hr : ∀ i j : Fin n, |GivenDegreeSeq.GraphLimit.r x i j - GivenDegreeSeq.GraphLimit.r y i j|
      ≤ E / 2 * (|x j - y j| + |x i - y i|) := by
    intro i j
    unfold GivenDegreeSeq.GraphLimit.r
    obtain ⟨hDx, _⟩ := hD x hxk i j
    obtain ⟨hDy, _⟩ := hD y hyk i j
    set a := Real.exp (-x j) with ha
    set a' := Real.exp (-y j) with ha'
    set b := Real.exp (x i) with hb
    set b' := Real.exp (y i) with hb'
    have hapos : 0 < a := Real.exp_pos _
    have ha'pos : 0 < a' := Real.exp_pos _
    have hbpos : 0 < b := Real.exp_pos _
    have hb'pos : 0 < b' := Real.exp_pos _
    have c1 := hclaim (-x j) (-y j) b b' hbpos.le hb'pos.le hDx hDy
    have c2 := hclaim (x i) (y i) a a' hapos.le ha'pos.le (by linarith) (by linarith)
    have e1 : |-x j - -y j| = |x j - y j| := by
      rw [show -x j - -y j = -(x j - y j) by ring, abs_neg]
    rw [e1] at c1
    have hD1 : 0 < a + b := by linarith
    have hD2 : 0 < a' + b' := by linarith
    have : 1 / (a + b) - 1 / (a' + b') = ((a' + b') - (a + b)) / ((a + b) * (a' + b')) := by
      field_simp
    rw [this, abs_div, abs_of_pos (mul_pos hD1 hD2)]
    have h5 : |(a' + b') - (a + b)| ≤ |a - a'| + |b - b'| := by
      have : (a' + b') - (a + b) = -(a - a') + -(b - b') := by ring
      rw [this]
      calc |-(a - a') + -(b - b')| ≤ |-(a - a')| + |-(b - b')| := abs_add_le _ _
        _ = |a - a'| + |b - b'| := by rw [abs_neg, abs_neg]
    have c3 : |b - b'| / ((a + b) * (a' + b')) ≤ E / 2 * |x i - y i| := by
      have := c2
      rw [show (a + b) * (a' + b') = (b + a) * (b' + a') by ring]
      rw [show (a + b) * (a' + b') = (b + a) * (b' + a') by ring] at *
      simpa [add_comm] using c2
    calc |(a' + b') - (a + b)| / ((a + b) * (a' + b'))
        ≤ (|a - a'| + |b - b'|) / ((a + b) * (a' + b')) := by gcongr
      _ = |a - a'| / ((a + b) * (a' + b')) + |b - b'| / ((a + b) * (a' + b')) := by ring
      _ ≤ E / 2 * |x j - y j| + E / 2 * |x i - y i| := by
          apply add_le_add
          · simpa using c1
          · exact c3
      _ = E / 2 * (|x j - y j| + |x i - y i|) := by ring
  have hlogd : ∀ a b m : ℝ, 0 < m → m ≤ a → m ≤ b → |Real.log a - Real.log b| ≤ |a - b| / m := by
    intro a b m hm ha hb
    have ha0 : 0 < a := lt_of_lt_of_le hm ha
    have hb0 : 0 < b := lt_of_lt_of_le hm hb
    rcases le_total b a with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb0 h)), abs_of_nonneg (sub_nonneg.mpr h)]
      have e : Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
      rw [e]
      calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
        _ = (a - b) / b := by field_simp
        _ ≤ (a - b) / m := div_le_div_of_nonneg_left (sub_nonneg.mpr h) hm hb
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha0 h)), abs_of_nonpos (sub_nonpos.mpr h)]
      have e : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb0.ne' ha0.ne').symm
      rw [neg_sub, neg_sub, e]
      calc Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
        _ = (b - a) / a := by field_simp
        _ ≤ (b - a) / m := div_le_div_of_nonneg_left (sub_nonneg.mpr h) hm ha
  rcases le_or_gt n 1 with hn | hn
  · have hemp : ∀ i : Fin n, (Finset.univ.erase i) = ∅ := by
      intro i
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      rw [Finset.mem_erase] at hj
      apply hj.1
      apply Fin.ext
      have := j.2
      have := i.2
      omega
    have h0 : ∀ i, GivenDegreeSeq.GraphLimit.phi d x i - GivenDegreeSeq.GraphLimit.phi d y i = 0 := by
      intro i; simp [GivenDegreeSeq.GraphLimit.phi, hemp i]
    simp only [h0, abs_zero, Finset.sum_const_zero]
    positivity
  · set N : ℝ := (n : ℝ) - 1 with hN
    have hNpos : 0 < N := by
      have : (1 : ℝ) < n := by exact_mod_cast hn
      linarith
    have hcard : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) = N := by
      intro i
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Nat.cast_sub (by simp; omega)]
      simp [hN]
    have hSlo : ∀ (z : Fin n → ℝ), (∀ k, |z k| ≤ K) → ∀ i,
        N / (2 * E) ≤ ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r z i j := by
      intro z hz i
      have h1 : ∀ j ∈ Finset.univ.erase i, 1 / (2 * E) ≤ GivenDegreeSeq.GraphLimit.r z i j := by
        intro j _
        unfold GivenDegreeSeq.GraphLimit.r
        obtain ⟨_, h2⟩ := hD z hz i j
        exact one_div_le_one_div_of_le (by linarith [Real.exp_pos (-z j), Real.exp_pos (z i)]) h2
      have := Finset.card_nsmul_le_sum _ _ _ h1
      rw [nsmul_eq_mul, hcard i] at this
      calc N / (2 * E) = N * (1 / (2 * E)) := by ring
        _ ≤ _ := this
    have per : ∀ i, |GivenDegreeSeq.GraphLimit.phi d x i - GivenDegreeSeq.GraphLimit.phi d y i|
        ≤ E * E * |x i - y i| + (E * E / N) * ∑ j ∈ Finset.univ.erase i, |x j - y j| := by
      intro i
      have hSx := hSlo x hxk i
      have hSy := hSlo y hyk i
      have hm : 0 < N / (2 * E) := by positivity
      have e1 : GivenDegreeSeq.GraphLimit.phi d x i - GivenDegreeSeq.GraphLimit.phi d y i
          = Real.log (∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r y i j)
            - Real.log (∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r x i j) := by
        unfold GivenDegreeSeq.GraphLimit.phi; ring
      rw [e1]
      refine (hlogd _ _ _ hm hSy hSx).trans ?_
      have hdiff : |(∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r y i j)
          - ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r x i j|
          ≤ E / 2 * (∑ j ∈ Finset.univ.erase i, |x j - y j| + N * |x i - y i|) := by
        rw [← Finset.sum_sub_distrib]
        calc |∑ j ∈ Finset.univ.erase i, (GivenDegreeSeq.GraphLimit.r y i j
              - GivenDegreeSeq.GraphLimit.r x i j)|
            ≤ ∑ j ∈ Finset.univ.erase i, |GivenDegreeSeq.GraphLimit.r y i j
              - GivenDegreeSeq.GraphLimit.r x i j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.univ.erase i, (E / 2 * (|x j - y j| + |x i - y i|)) := by
              apply Finset.sum_le_sum
              intro j _
              rw [abs_sub_comm]; exact hr i j
          _ = E / 2 * (∑ j ∈ Finset.univ.erase i, |x j - y j| + N * |x i - y i|) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
                hcard i]
      calc |(∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r y i j)
            - ∑ j ∈ Finset.univ.erase i, GivenDegreeSeq.GraphLimit.r x i j| / (N / (2 * E))
          ≤ E / 2 * (∑ j ∈ Finset.univ.erase i, |x j - y j| + N * |x i - y i|) / (N / (2 * E)) := by
            gcongr
        _ = E * E * |x i - y i| + (E * E / N) * ∑ j ∈ Finset.univ.erase i, |x j - y j| := by
            field_simp
            ring
    have hsum : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, |x j - y j|
        = N * ∑ j, |x j - y j| := by
      have : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, |x j - y j|
          = ∑ j, |x j - y j| - |x i - y i| := fun i =>
        Finset.sum_erase_eq_sub (Finset.mem_univ i)
      simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hN]
      ring
    calc ∑ i, |GivenDegreeSeq.GraphLimit.phi d x i - GivenDegreeSeq.GraphLimit.phi d y i|
        ≤ ∑ i, (E * E * |x i - y i| + (E * E / N) * ∑ j ∈ Finset.univ.erase i, |x j - y j|) :=
          Finset.sum_le_sum (fun i _ => per i)
      _ = E * E * ∑ i, |x i - y i| + (E * E / N) * (N * ∑ j, |x j - y j|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
      _ = 2 * Real.exp (2 * K) * ∑ i, |x i - y i| := by
          rw [hE2]; field_simp; ring
