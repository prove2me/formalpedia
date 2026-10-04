-- Prove2me | solution 1 for MetodosNumericos.picard_error_bound_classical
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:40:55.251425+00:00
-- url     : https://prove2.me/submissions/edb15fc9-16d1-4b8e-8dfc-066f0dcc4ee6

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

set_option autoImplicit false

lemma p9f69_int_bound (F : ℝ → ℝ) (x0 x C : ℝ) (n : ℕ) (hC : 0 ≤ C)
    (hF : IntervalIntegrable F MeasureTheory.volume x0 x)
    (hb : ∀ t ∈ Set.uIcc x0 x, |F t| ≤ C * |t - x0| ^ n) :
    |∫ t in x0..x, F t| ≤ C * |x - x0| ^ (n + 1) / ((n : ℝ) + 1) := by
  rcases le_total x0 x with hx | hx
  · have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (f := F)
      (g := fun t => C * (t - x0) ^ n) hx
      (Filter.Eventually.of_forall (fun t ht => by
        have := hb t (by rw [Set.uIcc_of_le hx]; exact Set.Ioc_subset_Icc_self ht)
        rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - x0)] at this
        simpa [Real.norm_eq_abs] using this))
      (by apply Continuous.intervalIntegrable; fun_prop)
    have h2 : ∫ t in x0..x, C * (t - x0) ^ n = C * (x - x0) ^ (n + 1) / ((n : ℝ) + 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ n) x0, integral_pow]
      simp
      ring
    rw [Real.norm_eq_abs, h2] at h1
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - x0)]
  · rw [intervalIntegral.integral_symm, abs_neg]
    have hb' : ∀ t ∈ Set.uIcc x x0, |F t| ≤ C * |t - x0| ^ n :=
      fun t ht => hb t (by rwa [Set.uIcc_comm])
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (f := F)
      (g := fun t => C * (x0 - t) ^ n) hx
      (Filter.Eventually.of_forall (fun t ht => by
        have := hb' t (by rw [Set.uIcc_of_le hx]; exact Set.Ioc_subset_Icc_self ht)
        rw [abs_of_nonpos (by linarith [ht.2] : t - x0 ≤ 0), neg_sub] at this
        simpa [Real.norm_eq_abs] using this))
      (by apply Continuous.intervalIntegrable; fun_prop)
    have h2 : ∫ t in x..x0, C * (x0 - t) ^ n = C * (x0 - x) ^ (n + 1) / ((n : ℝ) + 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) x0, integral_pow]
      simp
      ring
    rw [Real.norm_eq_abs, h2] at h1
    rwa [abs_of_nonpos (by linarith : x - x0 ≤ 0), neg_sub]

open MetodosNumericos in
theorem solution (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)) :
    |phi x - picardSeq f x0 y0 k x| ≤ M * N ^ k * h ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
  have hh0 : 0 < h := by rw [hh]; exact lt_min ha (div_pos hb hM)
  have hha : h ≤ a := by rw [hh]; exact min_le_left _ _
  have hMh : M * h ≤ b := by
    have : h ≤ b / M := by rw [hh]; exact min_le_right _ _
    rw [le_div_iff₀ hM] at this; linarith
  set I := Set.Icc (x0 - h) (x0 + h) with hI
  have hx0I : x0 ∈ I := ⟨by linarith, by linarith⟩
  have hIa : ∀ t ∈ I, t ∈ Set.Icc (x0 - a) (x0 + a) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsub : ∀ x ∈ I, Set.uIcc x0 x ⊆ I := fun x hx => Set.uIcc_subset_Icc hx0I hx
  have hdist : ∀ t ∈ I, |t - x0| ≤ h :=
    fun t ht => abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcomp : ∀ u : ℝ → ℝ, ContinuousOn u I → (∀ t ∈ I, u t ∈ Set.Icc (y0 - b) (y0 + b)) →
      ContinuousOn (fun t => f t (u t)) I := by
    intro u hu hr
    exact hcont.comp (continuousOn_id.prodMk hu) (fun t ht => ⟨hIa t ht, hr t ht⟩)
  have hinv : ∀ j : ℕ, ContinuousOn (picardSeq f x0 y0 j) I ∧
      ∀ t ∈ I, picardSeq f x0 y0 j t ∈ Set.Icc (y0 - b) (y0 + b) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, fun t _ => ?_⟩
      · show ContinuousOn (fun _ => y0) I
        exact continuousOn_const
      · show y0 ∈ Set.Icc (y0 - b) (y0 + b)
        constructor <;> linarith
    | succ j ih =>
      have hg := hcomp _ ih.1 ih.2
      have hgI : IntervalIntegrable (fun t => f t (picardSeq f x0 y0 j t))
          MeasureTheory.volume (x0 - h) (x0 + h) :=
        ContinuousOn.intervalIntegrable (hg.mono (by rw [Set.uIcc_of_le (by linarith)]))
      have e : picardSeq f x0 y0 (j + 1) =
          fun x => y0 + ∫ t in x0..x, f t (picardSeq f x0 y0 j t) := rfl
      rw [e]
      constructor
      · have := intervalIntegral.continuousOn_primitive_interval' hgI (a := x0)
          (by rw [Set.uIcc_of_le (by linarith)]; exact hx0I)
        rw [Set.uIcc_of_le (by linarith)] at this
        exact continuousOn_const.add this
      · intro t ht
        have hb2 := p9f69_int_bound _ x0 t M 0 hM.le
          ((hg.mono (hsub t ht)).intervalIntegrable)
          (fun s hs => by
            simpa using hbound s (hIa s (hsub t ht hs)) _ (ih.2 s (hsub t ht hs)))
        have hd := mul_le_mul_of_nonneg_left (hdist t ht) hM.le
        norm_num at hb2
        have := abs_le.mp (le_trans hb2 (le_trans hd hMh))
        constructor <;> linarith [this.1, this.2]
  have hphic : ContinuousOn phi I :=
    fun t ht => (hsol t ht).continuousAt.continuousWithinAt
  have hphig := hcomp phi hphic hrange
  have hphiint : ∀ x ∈ I, ∫ t in x0..x, f t (phi t) = phi x - y0 := by
    intro x hx
    rw [← hphi0]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hsol t (hsub x hx ht))
      ((hphig.mono (hsub x hx)).intervalIntegrable)
  have key : ∀ j : ℕ, ∀ x ∈ I, |phi x - picardSeq f x0 y0 j x| ≤
      M * N ^ j * |x - x0| ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro x hx
      have e : phi x - picardSeq f x0 y0 0 x = ∫ t in x0..x, f t (phi t) := by
        rw [hphiint x hx]; rfl
      rw [e]
      have := p9f69_int_bound _ x0 x M 0 hM.le ((hphig.mono (hsub x hx)).intervalIntegrable)
        (fun s hs => by simpa using hbound s (hIa s (hsub x hx hs)) _ (hrange s (hsub x hx hs)))
      simpa using this
    | succ j ih =>
      intro x hx
      have hgj := hcomp _ (hinv j).1 (hinv j).2
      have e : phi x - picardSeq f x0 y0 (j + 1) x =
          ∫ t in x0..x, (f t (phi t) - f t (picardSeq f x0 y0 j t)) := by
        rw [intervalIntegral.integral_sub ((hphig.mono (hsub x hx)).intervalIntegrable)
          ((hgj.mono (hsub x hx)).intervalIntegrable), hphiint x hx]
        show phi x - (y0 + ∫ t in x0..x, f t (picardSeq f x0 y0 j t)) = _
        ring
      rw [e]
      have hC : 0 ≤ M * N ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by positivity
      have hbd := p9f69_int_bound _ x0 x (M * N ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) (j + 1) hC
        (((hphig.sub hgj).mono (hsub x hx)).intervalIntegrable) (fun s hs => by
          have hsI := hsub x hx hs
          calc |f s (phi s) - f s (picardSeq f x0 y0 j s)|
              ≤ N * |phi s - picardSeq f x0 y0 j s| :=
                hlip s (hIa s hsI) _ (hrange s hsI) _ ((hinv j).2 s hsI)
            _ ≤ N * (M * N ^ j * |s - x0| ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)) :=
                mul_le_mul_of_nonneg_left (ih s hsI) hN
            _ = M * N ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) * |s - x0| ^ (j + 1) := by ring)
      calc _ ≤ _ := hbd
        _ = _ := by
          rw [Nat.factorial_succ (j + 1)]
          push_cast
          field_simp
  calc _ ≤ _ := key k x hx
    _ ≤ _ := by
      gcongr
      exact hdist x hx
