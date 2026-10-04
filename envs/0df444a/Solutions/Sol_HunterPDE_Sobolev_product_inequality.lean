-- Prove2me | solution 1 for HunterPDE.Sobolev.product_inequality
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:03:34.157087+00:00
-- url     : https://prove2.me/submissions/76bd6b88-a7c2-4970-8a55-bc0525284446

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace LWAux

/-- Splitting off the first coordinate in a Lebesgue integral over `Fin (n+1) → ℝ`. -/
lemma lintegral_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : Fin (n + 1) → ℝ, F x = ∫⁻ t : ℝ, ∫⁻ y : Fin n → ℝ, F (Fin.cons t y) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  rw [← h.lintegral_comp hF]
  have hm : Measurable (fun a : ℝ × (Fin n → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm a)) :=
    hF.comp (MeasurableEquiv.measurable _)
  have key := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
    _ hm.aemeasurable
  rw [Measure.volume_eq_prod]
  refine key.trans ?_
  refine lintegral_congr fun t => lintegral_congr fun y => ?_
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

lemma removeNth_zero_cons {n : ℕ} (t : ℝ) (y : Fin n → ℝ) :
    Fin.removeNth 0 (Fin.cons t y : Fin (n + 1) → ℝ) = y := by
  ext k
  simp [Fin.removeNth]

lemma removeNth_succ_cons {n : ℕ} (j : Fin (n + 1)) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    Fin.removeNth j.succ (Fin.cons t y : Fin (n + 2) → ℝ) =
      (Fin.cons t (Fin.removeNth j y) : Fin (n + 1) → ℝ) := by
  ext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

lemma measurable_cons {n : ℕ} (t : ℝ) :
    Measurable (fun y : Fin n → ℝ => (Fin.cons t y : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_iff.2 fun k => ?_
  refine Fin.cases ?_ (fun k' => ?_) k
  · simp
  · simpa using measurable_pi_apply k'

lemma measurable_removeNth {n : ℕ} (j : Fin (n + 1)) :
    Measurable (fun y : Fin (n + 1) → ℝ => Fin.removeNth j y) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

lemma measurable_cons_snd {n : ℕ} :
    Measurable (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
  refine measurable_pi_iff.2 fun k => ?_
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using measurable_fst
  · exact (measurable_pi_apply k).comp measurable_snd

/-- Base case `m = 1`. -/
lemma lw_one (g : Fin 2 → (Fin 1 → ℝ) → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : Fin 2 → ℝ, ∏ i, g i (Fin.removeNth i x) ≤
      ∏ i, (∫⁻ y : Fin 1 → ℝ, g i y ^ ((1 : ℕ) : ℝ)) ^ (1 / ((1 : ℕ) : ℝ)) := by
  have hmeas : Measurable (fun x : Fin 2 → ℝ => ∏ i, g i (Fin.removeNth i x)) :=
    Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  rw [lintegral_cons _ hmeas]
  simp only [Nat.cast_one, ENNReal.rpow_one, div_one, Fin.prod_univ_two]
  set H : ℝ → ℝ≥0∞ := fun t => g 1 (Fin.cons t default) with hH
  have h1 : ∀ (t : ℝ) (y : Fin 1 → ℝ),
      g 0 (Fin.removeNth 0 (Fin.cons t y : Fin 2 → ℝ)) * g 1 (Fin.removeNth 1 (Fin.cons t y : Fin 2 → ℝ))
        = g 0 y * H t := by
    intro t y
    have e1 : Fin.removeNth 0 (Fin.cons t y : Fin 2 → ℝ) = y := removeNth_zero_cons t y
    have e2 : Fin.removeNth 1 (Fin.cons t y : Fin 2 → ℝ) = Fin.cons t default := by
      show Fin.removeNth (Fin.succ 0) (Fin.cons t y : Fin 2 → ℝ) = _
      rw [removeNth_succ_cons]
      congr 1
      exact Subsingleton.elim _ _
    rw [e1, e2]
  simp_rw [h1]
  have hH : Measurable H := (hg 1).comp (measurable_pi_iff.2 fun k => by
    refine Fin.cases ?_ (fun k => ?_) k
    · exact measurable_id'
    · exact absurd k.isLt (by omega))
  have h2 : ∀ t, ∫⁻ y : Fin 1 → ℝ, g 0 y * H t = (∫⁻ y : Fin 1 → ℝ, g 0 y) * H t := fun t =>
    lintegral_mul_const _ (hg 0)
  simp_rw [h2]
  rw [lintegral_const_mul _ hH]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  rw [lintegral_cons (n := 0) (g 1) (hg 1)]
  refine lintegral_congr fun t => ?_
  have h3 : ∀ y : Fin 0 → ℝ, g 1 (Fin.cons t y) = H t := fun y => by
    simp only [H]
    congr 1
    exact congrArg _ (Subsingleton.elim _ _)
  simp_rw [h3]
  have h4 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  simp [h4]

/-- The Hölder step: the inner integral over the remaining `m + 1` variables. -/
lemma key_bound (m : ℕ) (hm : 1 ≤ m)
    (IH : ∀ g : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞, (∀ i, Measurable (g i)) →
      ∫⁻ x : Fin (m + 1) → ℝ, ∏ i, g i (Fin.removeNth i x) ≤
        ∏ i, (∫⁻ y : Fin m → ℝ, g i y ^ (m : ℝ)) ^ (1 / (m : ℝ)))
    (g0 : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hg0 : Measurable g0)
    (G : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞) (hG : ∀ j, Measurable (G j)) :
    ∫⁻ x' : Fin (m + 1) → ℝ, g0 x' * ∏ j, G j (Fin.removeNth j x') ≤
      (∫⁻ x' : Fin (m + 1) → ℝ, g0 x' ^ ((m : ℝ) + 1)) ^ (1 / ((m : ℝ) + 1)) *
        ∏ j, (∫⁻ y : Fin m → ℝ, G j y ^ ((m : ℝ) + 1)) ^ (1 / ((m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM1 : 1 < M := by rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  set q : ℝ := M / (M - 1) with hq
  have hMm : M - 1 = m := by rw [hM]; ring
  have hq' : q = M / m := by rw [hq, hMm]
  have hpq : M.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hM1).2 hq
  have hq0 : 0 < q := by rw [hq']; positivity
  have hPmeas : Measurable (fun x' : Fin (m + 1) → ℝ => ∏ j, G j (Fin.removeNth j x')) :=
    Finset.measurable_prod _ fun j _ => (hG j).comp (measurable_removeNth j)
  -- Hölder
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Fin (m + 1) → ℝ)) hpq
    hg0.aemeasurable hPmeas.aemeasurable
  -- the second factor via the induction hypothesis
  have h2 : ∫⁻ x' : Fin (m + 1) → ℝ, (∏ j, G j (Fin.removeNth j x')) ^ q ≤
      ∏ j, (∫⁻ y : Fin m → ℝ, G j y ^ M) ^ (1 / (m : ℝ)) := by
    have h3 := IH (fun j y => G j y ^ q) fun j => (hG j).pow_const q
    have h4 : ∀ x' : Fin (m + 1) → ℝ, (∏ j, G j (Fin.removeNth j x')) ^ q =
        ∏ j, G j (Fin.removeNth j x') ^ q := fun x' => (ENNReal.prod_rpow_of_nonneg hq0.le).symm
    simp_rw [h4]
    refine h3.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hq']
    field_simp
  have h5 : (∫⁻ x' : Fin (m + 1) → ℝ, (∏ j, G j (Fin.removeNth j x')) ^ q) ^ (1 / q) ≤
      ∏ j, (∫⁻ y : Fin m → ℝ, G j y ^ M) ^ (1 / M) := by
    calc (∫⁻ x' : Fin (m + 1) → ℝ, (∏ j, G j (Fin.removeNth j x')) ^ q) ^ (1 / q)
        ≤ (∏ j, (∫⁻ y : Fin m → ℝ, G j y ^ M) ^ (1 / (m : ℝ))) ^ (1 / q) :=
          ENNReal.rpow_le_rpow h2 (by positivity)
      _ = ∏ j, (∫⁻ y : Fin m → ℝ, G j y ^ M) ^ (1 / M) := by
          rw [← ENNReal.prod_rpow_of_nonneg (by positivity)]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← ENNReal.rpow_mul]
          congr 1
          rw [hq']
          field_simp
  calc ∫⁻ x' : Fin (m + 1) → ℝ, g0 x' * ∏ j, G j (Fin.removeNth j x')
      ≤ (∫⁻ x' : Fin (m + 1) → ℝ, g0 x' ^ M) ^ (1 / M) *
          (∫⁻ x' : Fin (m + 1) → ℝ, (∏ j, G j (Fin.removeNth j x')) ^ q) ^ (1 / q) := h1
    _ ≤ _ := mul_le_mul' le_rfl h5

/-- The inductive step `m → m + 1`. -/
lemma lw_step (m : ℕ) (hm : 1 ≤ m)
    (IH : ∀ g : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞, (∀ i, Measurable (g i)) →
      ∫⁻ x : Fin (m + 1) → ℝ, ∏ i, g i (Fin.removeNth i x) ≤
        ∏ i, (∫⁻ y : Fin m → ℝ, g i y ^ (m : ℝ)) ^ (1 / (m : ℝ)))
    (g : Fin (m + 2) → (Fin (m + 1) → ℝ) → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : Fin (m + 2) → ℝ, ∏ i, g i (Fin.removeNth i x) ≤
      ∏ i, (∫⁻ y : Fin (m + 1) → ℝ, g i y ^ ((m + 1 : ℕ) : ℝ)) ^ (1 / ((m + 1 : ℕ) : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM0 : 0 < M := by rw [hM]; linarith
  have hmeas : Measurable (fun x : Fin (m + 2) → ℝ => ∏ i, g i (Fin.removeNth i x)) :=
    Finset.measurable_prod _ fun i _ =>
      (hg i).comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  rw [lintegral_cons _ hmeas]
  set G : Fin (m + 1) → ℝ → (Fin m → ℝ) → ℝ≥0∞ := fun j t y => g j.succ (Fin.cons t y) with hG
  have hGm : ∀ j t, Measurable (G j t) := fun j t => (hg j.succ).comp (measurable_cons t)
  set h : Fin (m + 1) → ℝ → ℝ≥0∞ := fun j t => ∫⁻ y : Fin m → ℝ, G j t y ^ M with hh
  have hhm : ∀ j, Measurable (h j) := fun j => by
    have : Measurable (fun p : ℝ × (Fin m → ℝ) => g j.succ (Fin.cons p.1 p.2) ^ M) :=
      ((hg j.succ).comp measurable_cons_snd).pow_const M
    exact this.lintegral_prod_right'
  set A : ℝ≥0∞ := (∫⁻ x' : Fin (m + 1) → ℝ, g 0 x' ^ M) ^ (1 / M) with hA
  -- the pointwise bound on the inner integral
  have hpt : ∀ t : ℝ, ∫⁻ x' : Fin (m + 1) → ℝ, ∏ i, g i (Fin.removeNth i (Fin.cons t x' : Fin (m + 2) → ℝ))
      ≤ A * ∏ j, (h j t) ^ (1 / M) := by
    intro t
    have e : ∀ x' : Fin (m + 1) → ℝ, ∏ i, g i (Fin.removeNth i (Fin.cons t x' : Fin (m + 2) → ℝ))
        = g 0 x' * ∏ j, G j t (Fin.removeNth j x') := by
      intro x'
      rw [Fin.prod_univ_succ, removeNth_zero_cons]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [removeNth_succ_cons]
    simp_rw [e]
    exact key_bound m hm IH (g 0) (hg 0) (G · t) (hGm · t)
  calc ∫⁻ t : ℝ, ∫⁻ x' : Fin (m + 1) → ℝ,
        ∏ i, g i (Fin.removeNth i (Fin.cons t x' : Fin (m + 2) → ℝ))
      ≤ ∫⁻ t : ℝ, A * ∏ j, (h j t) ^ (1 / M) := lintegral_mono hpt
    _ = A * ∫⁻ t : ℝ, ∏ j, (h j t) ^ (1 / M) :=
        lintegral_const_mul _ (Finset.measurable_prod _ fun j _ => (hhm j).pow_const _)
    _ ≤ A * ∏ j, (∫⁻ t : ℝ, h j t) ^ (1 / M) := by
        refine mul_le_mul' le_rfl ?_
        refine ENNReal.lintegral_prod_norm_pow_le Finset.univ (fun j _ => (hhm j).aemeasurable)
          (p := fun _ => 1 / M) ?_ (fun _ _ => by positivity)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
        linarith [hM]
    _ = ∏ i, (∫⁻ y : Fin (m + 1) → ℝ, g i y ^ M) ^ (1 / M) := by
        conv_rhs => rw [Fin.prod_univ_succ]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        congr 1
        rw [lintegral_cons (n := m) (fun z => g j.succ z ^ M) ((hg j.succ).pow_const M)]

/-- Loomis–Whitney for `Fin`-indexed functions, all `m ≥ 1`. -/
theorem lw_all : ∀ m : ℕ, 1 ≤ m → ∀ g : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞,
    (∀ i, Measurable (g i)) →
    ∫⁻ x : Fin (m + 1) → ℝ, ∏ i, g i (Fin.removeNth i x) ≤
      ∏ i, (∫⁻ y : Fin m → ℝ, g i y ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact lw_one
  | succ m hm ih => exact lw_step m hm ih

end LWAux

namespace LWAux

lemma lintegral_euclid {m : ℕ} (F : (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y : EuclideanSpace ℝ (Fin m), F (WithLp.ofLp y) = ∫⁻ z : Fin m → ℝ, F z :=
  (PiLp.volume_preserving_ofLp (Fin m)).lintegral_comp hF

lemma eLpNorm_eq {m : ℕ} (hm : 1 ≤ m) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : Continuous f) (hnn : ∀ y, 0 ≤ f y) :
    eLpNorm f (m : ℝ≥0∞) volume =
      (∫⁻ z : Fin m → ℝ, ENNReal.ofReal (f (WithLp.toLp 2 z)) ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
  have h0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h1 : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 h1]
  simp only [ENNReal.toReal_natCast]
  congr 1
  have hmeas : Measurable (fun z : Fin m → ℝ => ENNReal.ofReal (f (WithLp.toLp 2 z)) ^ (m : ℝ)) :=
    (ENNReal.measurable_ofReal.comp (hf.comp (PiLp.continuous_toLp 2 _)).measurable).pow_const _
  have := lintegral_euclid (m := m)
    (fun z => ENNReal.ofReal (f (WithLp.toLp 2 z)) ^ (m : ℝ)) hmeas
  simp only [WithLp.toLp_ofLp] at this
  rw [← this]
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal (hnn y)]

end LWAux

open MeasureTheory in
theorem solution {m : ℕ} (hm : 1 ≤ m)
    (g : Fin (m + 1) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i))
    (hcpt : ∀ i, HasCompactSupport (g i))
    (hnonneg : ∀ i y, 0 ≤ g i y) :
    ∫⁻ x : EuclideanSpace ℝ (Fin (m + 1)),
        ∏ i, ENNReal.ofReal (g i (WithLp.toLp 2 (Fin.removeNth i (WithLp.ofLp x)))) ≤
      ∏ i, eLpNorm (g i) (m : ENNReal) volume := by
  have hcont : ∀ i, Continuous (g i) := fun i => (hsmooth i).continuous
  set g' : Fin (m + 1) → (Fin m → ℝ) → ℝ≥0∞ :=
    fun i z => ENNReal.ofReal (g i (WithLp.toLp 2 z)) with hg'
  have hg'm : ∀ i, Measurable (g' i) := fun i =>
    ENNReal.measurable_ofReal.comp ((hcont i).comp (PiLp.continuous_toLp 2 _)).measurable
  have hmeas : Measurable (fun z : Fin (m + 1) → ℝ => ∏ i, g' i (Fin.removeNth i z)) :=
    Finset.measurable_prod _ fun i _ =>
      (hg'm i).comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  have h1 := LWAux.lintegral_euclid (m := m + 1) (fun z => ∏ i, g' i (Fin.removeNth i z)) hmeas
  have h2 : ∫⁻ x : EuclideanSpace ℝ (Fin (m + 1)),
        ∏ i, ENNReal.ofReal (g i (WithLp.toLp 2 (Fin.removeNth i (WithLp.ofLp x)))) =
      ∫⁻ z : Fin (m + 1) → ℝ, ∏ i, g' i (Fin.removeNth i z) := h1
  rw [h2]
  refine (LWAux.lw_all m hm g' hg'm).trans (le_of_eq ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LWAux.eLpNorm_eq hm (g i) (hcont i) (hnonneg i)]
