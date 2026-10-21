-- Prove2me | solution 1 for ModernOnlineLearning.ToX.eg_regret_6_6
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T05:54:34.118062+00:00
-- url     : https://prove2.me/submissions/06ed6676-71fd-4a9c-82e8-08d20e5197ff

import Definitions.Def_ModernOnlineLearning_ToX_Algorithms
open MeasureTheory ProbabilityTheory

private lemma weighted_exp_bound {d : ℕ} (w g : Fin d → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (G η : ℝ) (hG : 0 ≤ G) (hg : ∀ i, |g i| ≤ G) :
    Real.log (∑ i, w i * Real.exp (-η * g i)) ≤
      -η * (∑ i, w i * g i) + η^2 * G^2 / 2 := by
  let p : PMF (Fin d) := PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum]
    norm_num)
  have hint (f : Fin d → ℝ) : ∫ i, f i ∂p.toMeasure = ∑ i, w i * f i := by
    rw [PMF.integral_eq_sum]
    simp only [p, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  have hm := hasSubgaussianMGF_of_mem_Icc (μ := p.toMeasure) (X := g)
    (measurable_of_finite g).aemeasurable (Filter.Eventually.of_forall (fun i => abs_le.mp (hg i)))
  have hb := hm.mgf_le (-η)
  rw [mgf, hint, hint] at hb
  have hnorm : (((‖G - -G‖₊ / 2) ^ 2 : NNReal) : ℝ) = G^2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [hnorm] at hb
  let m : ℝ := ∑ i, w i * g i
  have heq : (∑ i, w i * Real.exp (-η*(g i-m))) =
      Real.exp (η*m) * (∑ i, w i * Real.exp (-η*g i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show -η*(g i-m)=η*m+(-η*g i) by ring, Real.exp_add]
    ring
  change (∑ i, w i * Real.exp (-η*(g i-m))) ≤ _ at hb
  rw [heq] at hb
  have hZ : 0 < ∑ i, w i * Real.exp (-η*g i) := by
    have hex : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
      linarith [hsum]
    obtain ⟨i, hwi⟩ := hex
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hw j) (Real.exp_pos _).le
    · exact ⟨i, Finset.mem_univ i, mul_pos hwi (Real.exp_pos _)⟩
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hZ) hb
  rw [Real.log_mul (Real.exp_pos _).ne' hZ.ne', Real.log_exp, Real.log_exp] at hl
  dsimp [m] at hl
  nlinarith



open ModernOnlineLearning.ToX

private lemma sum_log_steps (f : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (f (t+1)-f t))=f (T+1)-f 1 := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem solution {d T : ℕ} [NeZero d] (hT : 1 ≤ T)
    (η : ℝ) (g x : ℕ → Fin d → ℝ)
    (loss : ℕ → (Fin d → ℝ) → ℝ)
    (hRun : IsEGRun T η g x)
    (hsub : ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ simplex d,
      loss t (x t) + pairing (g t) (y - x t) ≤ loss t y) :
    ∀ u ∈ simplex d,
      (∑ t ∈ Finset.Icc 1 T, (loss t (x t) - loss t u)) ≤
        Real.log (d : ℝ) / η +
          η / 2 * ∑ t ∈ Finset.Icc 1 T,
            (Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => |g t i|)) ^ 2 := by
  classical
  have hη := hRun.1
  have hd : 0 < (d : ℝ) := by exact_mod_cast (NeZero.pos d)
  let G : ℕ → ℝ := fun t => Finset.univ.sup' Finset.univ_nonempty (fun i : Fin d => |g t i|)
  let Z : ℕ → ℝ := fun t => ∑ i, x t i * Real.exp (-η*g t i)
  have hxmem (t : ℕ) (ht : t ∈ Finset.Icc 1 (T+1)) :
      (∀ i, 0 ≤ x t i) ∧ ∑ i, x t i = 1 := hRun.2.1 t ht
  have hZ (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : 0 < Z t := by
    have hm := hxmem t (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, by have := (Finset.mem_Icc.mp ht).2; omega⟩)
    have hex : ∃ i, 0 < x t i := by
      by_contra h
      push Not at h
      have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
      linarith [hm.2]
    obtain ⟨i, hxi⟩ := hex
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hm.1 j) (Real.exp_pos _).le
    · exact ⟨i, Finset.mem_univ i, mul_pos hxi (Real.exp_pos _)⟩
  have hxpos_succ : ∀ n : ℕ, n ≤ T → ∀ i, 0 < x (n+1) i := by
    intro n
    induction n with
    | zero => intro hn i; simpa [hRun.2.2.1 i] using one_div_pos.mpr hd
    | succ n ih =>
      intro hn i
      have ht : n+1 ∈ Finset.Icc 1 T := by simp only [Finset.mem_Icc]; omega
      rw [hRun.2.2.2 (n+1) ht i]
      exact div_pos (mul_pos (ih (by omega) i) (Real.exp_pos _)) (hZ _ ht)
  have hxpos (t : ℕ) (ht : t ∈ Finset.Icc 1 (T+1)) (i : Fin d) : 0 < x t i := by
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    simpa [Nat.sub_add_cancel ht1] using hxpos_succ (t-1) (by omega) i
  have hi_bound (i : Fin d) :
      (∑ t ∈ Finset.Icc 1 T, (pairing (g t) (x t) - g t i)) ≤
        Real.log (d : ℝ) / η + η / 2 * ∑ t ∈ Finset.Icc 1 T, (G t)^2 := by
    have hs := Finset.sum_le_sum (s := Finset.Icc 1 T) (f := fun t => η*(pairing (g t) (x t)-g t i))
      (g := fun t => Real.log (x (t+1) i)-Real.log (x t i)+η^2/2*(G t)^2) (fun t ht => by
        have ht' : t ∈ Finset.Icc 1 (T+1) := Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1, by have := (Finset.mem_Icc.mp ht).2; omega⟩
        have hG (j : Fin d) : |g t j| ≤ G t := Finset.le_sup' (s := Finset.univ) (f := fun j => |g t j|) (Finset.mem_univ j)
        have hG0 : 0 ≤ G t := (abs_nonneg (g t (0 : Fin d))).trans (hG 0)
        have he := weighted_exp_bound (x t) (g t) (hxmem t ht').1 (hxmem t ht').2 (G t) η hG0 hG
        have hl : Real.log (x (t+1) i)=Real.log (x t i)-η*g t i-Real.log (Z t) := by
          rw [hRun.2.2.2 t ht i, Real.log_div (mul_pos (hxpos t ht' i) (Real.exp_pos _)).ne' (hZ t ht).ne',
            Real.log_mul (hxpos t ht' i).ne' (Real.exp_pos _).ne', Real.log_exp]
          ring
        have hp : (∑ j, x t j*g t j)=pairing (g t) (x t) := by simp only [pairing, mul_comm]
        change Real.log (Z t) ≤ _ at he
        rw [hp] at he
        nlinarith)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_steps (fun t => Real.log (x t i)) T] at hs
    have hlast := hxmem (T+1) (by simp)
    have hle : x (T+1) i ≤ 1 := by
      rw [← hlast.2]
      exact Finset.single_le_sum (fun j hj => hlast.1 j) (Finset.mem_univ i)
    have hloglast := Real.log_nonpos (hlast.1 i) hle
    rw [hRun.2.2.1 i, one_div, Real.log_inv] at hs
    apply (mul_le_mul_iff_right₀ hη).mp
    have halg : η*(Real.log (d:ℝ)/η+η/2*(∑ t ∈ Finset.Icc 1 T, (G t)^2)) =
        Real.log (d:ℝ)+η^2/2*(∑ t ∈ Finset.Icc 1 T, (G t)^2) := by field_simp
    rw [halg]
    linarith
  intro u hu
  have hunon : ∀ i, 0 ≤ u i := hu.1
  have husum : ∑ i, u i = 1 := hu.2
  have hlin : (∑ t ∈ Finset.Icc 1 T, (loss t (x t)-loss t u)) ≤
      ∑ t ∈ Finset.Icc 1 T, (pairing (g t) (x t)-pairing (g t) u) := by
    apply Finset.sum_le_sum
    intro t ht
    have h := hsub t ht u hu
    have hp : pairing (g t) (u-x t)=pairing (g t) u-pairing (g t) (x t) := by
      simp [pairing, mul_sub, Finset.sum_sub_distrib]
    rw [hp] at h
    linarith
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hi_bound i) (hunon i))
  have hright : (∑ i, u i*(Real.log (d:ℝ)/η+η/2*(∑ t ∈ Finset.Icc 1 T, (G t)^2))) =
      Real.log (d:ℝ)/η+η/2*(∑ t ∈ Finset.Icc 1 T, (G t)^2) := by rw [← Finset.sum_mul, husum, one_mul]
  rw [hright] at hi
  have hleft : (∑ i, u i * ∑ t ∈ Finset.Icc 1 T, (pairing (g t) (x t)-g t i)) =
      ∑ t ∈ Finset.Icc 1 T, (pairing (g t) (x t)-pairing (g t) u) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, husum, one_mul]
    simp only [pairing, mul_comm]
  rw [hleft] at hi
  exact hlin.trans hi

