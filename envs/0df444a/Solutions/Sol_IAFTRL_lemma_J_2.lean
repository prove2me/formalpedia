-- Prove2me | solution 1 for IAFTRL.lemma_J_2
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T16:16:11.112661+00:00
-- url     : https://prove2.me/submissions/539dd08e-f28d-43b9-ab14-3df3d50d3c9d

import Mathlib

open Real Finset MeasureTheory

namespace J2

/-! ### Telescoping -/

lemma tele (a b c D lin : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hlin : ∀ t, 1 ≤ t → lin t = D t + a t - b t)
    (hc : ∀ t, 2 ≤ t → a (t - 1) - b t ≤ c t) :
    ∑ t ∈ Icc 1 T, lin t ≤ ∑ t ∈ Icc 1 T, D t + a T - b 1 + ∑ t ∈ Icc 2 T, c t := by
  induction T with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Finset.Icc_self, Finset.Icc_eq_empty (by norm_num)]
      simp only [Finset.sum_singleton, Finset.sum_empty, zero_add]
      linarith [hlin 1 le_rfl]
    · have h0 := ih hn
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have h1 := hlin (n + 1) (by omega)
      have h2 := hc (n + 1) (by omega)
      rw [Nat.add_sub_cancel] at h2
      linarith

lemma sum_diff (f : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Icc 2 T, (f t - f (t - 1)) = f T - f 1 := by
  induction T with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Finset.Icc_eq_empty (by norm_num)]; simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih hn, Nat.add_sub_cancel]; ring

/-! ### Finite Gibbs variational inequality -/

lemma gibbs_fin {K : ℕ} (p V : Fin K → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (b : ℝ) (hb : 0 < b) :
    -b * Real.log (∑ a, Real.exp (-(V a) / b)) ≤ ∑ a, p a * V a + b * ∑ a, p a * Real.log (p a) := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hp1; norm_num at hp1
  set Z := ∑ a, Real.exp (-(V a) / b) with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun a _ => Real.exp_pos _) hne
  have key : ∑ a, p a * (-(V a) / b - Real.log Z - Real.log (p a)) ≤ 0 := by
    calc ∑ a, p a * (-(V a) / b - Real.log Z - Real.log (p a))
        ≤ ∑ a, p a * (Real.exp (-(V a) / b - Real.log Z - Real.log (p a)) - 1) := by
          apply Finset.sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left _ (hp a).le
          linarith [Real.add_one_le_exp (-(V a) / b - Real.log Z - Real.log (p a))]
      _ = ∑ a, Real.exp (-(V a) / b) / Z - ∑ a, p a := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _
          rw [Real.exp_sub, Real.exp_sub, Real.exp_log hZpos, Real.exp_log (hp a)]
          have := (hp a).ne'
          field_simp
      _ = 0 := by rw [← Finset.sum_div, ← hZ, div_self hZpos.ne', hp1]; ring
  have e1 : ∀ a, p a * (-(V a) / b - Real.log Z - Real.log (p a)) =
      -(p a * V a) / b - p a * Real.log Z - p a * Real.log (p a) := fun a => by ring
  have s1 : ∑ a, -(p a * V a) / b = -(∑ a, p a * V a) / b := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have s2 : ∑ a, p a * Real.log Z = Real.log Z := by rw [← Finset.sum_mul, hp1, one_mul]
  rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    s1, s2] at key
  have h3 : b * (-(∑ a, p a * V a) / b) = -(∑ a, p a * V a) := by field_simp
  have h4 := mul_le_mul_of_nonneg_left key hb.le
  have h5 : b * (-(∑ a, p a * V a) / b - Real.log Z - ∑ a, p a * Real.log (p a)) =
      b * (-(∑ a, p a * V a) / b) - b * Real.log Z - b * ∑ a, p a * Real.log (p a) := by ring
  rw [h5, h3, mul_zero] at h4
  linarith

lemma gibbs_eq_fin {K : ℕ} (p V : Fin K → ℝ) (b : ℝ) (hb : 0 < b)
    (hp : ∀ a, p a = Real.exp (-(V a) / b) / ∑ c, Real.exp (-(V c) / b)) :
    -b * Real.log (∑ a, Real.exp (-(V a) / b)) =
      ∑ a, p a * V a + b * ∑ a, p a * Real.log (p a) := by
  set Z := ∑ c, Real.exp (-(V c) / b) with hZdef
  by_cases hK : (Finset.univ : Finset (Fin K)).Nonempty
  · have hZ : 0 < Z := Finset.sum_pos (fun a _ => Real.exp_pos _) hK
    have hl : ∀ a, Real.log (p a) = -(V a) / b - Real.log Z := fun a => by
      rw [hp a, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
    have hp1 : ∑ a, p a = 1 := by
      simp only [hp]; rw [← Finset.sum_div]; exact div_self hZ.ne'
    simp only [hl]
    have e : ∀ a, p a * (-(V a) / b - Real.log Z) = -(p a * V a) / b - p a * Real.log Z :=
      fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_neg_distrib, ← Finset.sum_mul, hp1]
    field_simp
    ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hK
    simp [hZdef, hK]

/-! ### Bounded functions -/

def Bdd {X : Type*} (f : X → ℝ) : Prop := ∃ C, ∀ x, |f x| ≤ C

namespace Bdd
variable {X : Type*} {f g : X → ℝ}

lemma add (hf : Bdd f) (hg : Bdd g) : Bdd fun x => f x + g x := by
  obtain ⟨A, hA⟩ := hf; obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩

lemma neg (hf : Bdd f) : Bdd fun x => -f x := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun x => by rw [abs_neg]; exact hA x⟩

lemma const (c : ℝ) : Bdd fun _ : X => c := ⟨|c|, fun _ => le_rfl⟩

lemma mul (hf : Bdd f) (hg : Bdd g) : Bdd fun x => f x * g x := by
  obtain ⟨A, hA⟩ := hf; obtain ⟨B, hB⟩ := hg
  exact ⟨A * B, fun x => by
    rw [abs_mul]; exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x))⟩

lemma sub (hf : Bdd f) (hg : Bdd g) : Bdd fun x => f x - g x := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma div_const (hf : Bdd f) (c : ℝ) : Bdd fun x => f x / c := by
  have := hf.mul (const (X := X) c⁻¹)
  simpa [div_eq_mul_inv] using this

lemma exp (hf : Bdd f) : Bdd fun x => Real.exp (f x) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨Real.exp A, fun x => by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hA x))⟩

lemma int [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (hf : Bdd f)
    (hm : Measurable f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

end Bdd

section Rel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma Zpos {V : X → ℝ} (hV : Measurable V) (hVb : Bdd V) {b : ℝ} (hb : 0 < b) :
    0 < ∫ x, Real.exp (-(V x) / b) ∂μ := by
  obtain ⟨C, hC⟩ := hVb
  have hi : Integrable (fun x => Real.exp (-(V x) / b)) μ :=
    ((Bdd.neg ⟨C, hC⟩).div_const b).exp.int μ (by fun_prop)
  have h1 : ∫ _x : X, Real.exp (-C / b) ∂μ ≤ ∫ x, Real.exp (-(V x) / b) ∂μ := by
    refine integral_mono (integrable_const _) hi (fun x => ?_)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hb.le
    linarith [le_abs_self (V x), hC x]
  rw [integral_const, probReal_univ, one_smul] at h1
  exact lt_of_lt_of_le (Real.exp_pos _) h1

lemma wd_int {d : X → ℝ} (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x) (f : X → ℝ) :
    ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (d x)) = ∫ x, d x * f x ∂μ := by
  have hm : Measurable fun x => ENNReal.ofReal (d x) := ENNReal.measurable_ofReal.comp hd
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  congr 1; funext x; rw [ENNReal.toReal_ofReal (hd0 x), smul_eq_mul]

lemma core {w y : X → ℝ} (hw : Measurable w) (hwb : Bdd w) (hw0 : ∀ x, 0 ≤ w x)
    (hy : Measurable y) (hyb : Bdd y) (hw1 : ∫ x, w x ∂μ = 1) :
    ∫ x, w x * y x ∂μ ≤ ∫ x, w x * Real.exp (y x) ∂μ - 1 := by
  have i1 : Integrable (fun x => w x * y x) μ := (hwb.mul hyb).int μ (hw.mul hy)
  have i2 : Integrable (fun x => w x * Real.exp (y x)) μ := (hwb.mul hyb.exp).int μ (hw.mul hy.exp)
  have i3 : Integrable (fun x => w x) μ := hwb.int μ hw
  have h := integral_mono i1 (i2.sub i3) (fun x => by
    have := Real.add_one_le_exp (y x)
    have := hw0 x
    show w x * y x ≤ w x * Real.exp (y x) - w x
    nlinarith)
  have e : ∫ x, (fun x => w x * Real.exp (y x)) x - (fun x => w x) x ∂μ =
      ∫ x, w x * Real.exp (y x) ∂μ - ∫ x, w x ∂μ := integral_sub i2 i3
  simp only [Pi.sub_apply] at h
  rw [e, hw1] at h
  exact h

lemma atom [MeasurableSingletonClass X] {W : X → ℝ} (hW : Measurable W) (hWb : Bdd W) {b : ℝ}
    (hb : 0 < b) (u : X) (hu : 0 < μ {u}) :
    -b * Real.log (∫ x, Real.exp (-(W x) / b) ∂μ) ≤ W u + b * Real.log (1 / (μ {u}).toReal) := by
  have hi : Integrable (fun x => Real.exp (-(W x) / b)) μ :=
    (hWb.neg.div_const b).exp.int μ (by fun_prop)
  have h1 : ∫ x in {u}, Real.exp (-(W x) / b) ∂μ ≤ ∫ x, Real.exp (-(W x) / b) ∂μ :=
    setIntegral_le_integral hi (ae_of_all _ fun x => (Real.exp_pos _).le)
  rw [integral_singleton, smul_eq_mul, measureReal_def] at h1
  have hp : 0 < (μ {u}).toReal := ENNReal.toReal_pos hu.ne' (measure_ne_top μ _)
  have h2 := Real.log_le_log (mul_pos hp (Real.exp_pos _)) h1
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [one_div, Real.log_inv]
  have e : b * (-(W u) / b) = -(W u) := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h2 hb.le
  rw [mul_add, e] at h3
  linarith

end Rel

/-! ### The finite part -/

theorem fin_core {K : ℕ} (β : ℕ → ℝ) (g : ℕ → Fin K → ℝ) (u : Fin K) (T : ℕ)
    (hβ : ∀ t, 1 ≤ t → 0 < β t) (hmono : ∀ t, 1 ≤ t → β t ≤ β (t + 1)) (hT : 1 ≤ T)
    (S : ℕ → Fin K → ℝ) (hS : ∀ t a, S t a = ∑ s ∈ Finset.Icc 1 t, g s a)
    (q : ℕ → Fin K → ℝ)
    (hq : ∀ t a, q t a = Real.exp (-(S (t - 1) a) / β t) / ∑ b, Real.exp (-(S (t - 1) b) / β t))
    (D : ℕ → ℝ)
    (hD : ∀ t, D t = ∑ a, q t a * g t a + β t * Real.log (∑ a, q t a * Real.exp (-(g t a) / β t)))
    (H : (Fin K → ℝ) → ℝ) (hH : ∀ p, H p = -∑ a, p a * Real.log (p a)) :
    (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
        β T * Real.log K + ∑ t ∈ Finset.Icc 1 T, D t) ∧
    (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
        β 1 * Real.log K + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * H (q t) +
          ∑ t ∈ Finset.Icc 1 T, D t) := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty := ⟨u, Finset.mem_univ _⟩
  have hZpos : ∀ (b : ℝ) (V : Fin K → ℝ), 0 < ∑ a, Real.exp (-(V a) / b) :=
    fun b V => Finset.sum_pos (fun a _ => Real.exp_pos _) hne
  obtain ⟨F, hF⟩ : ∃ F : ℝ → (Fin K → ℝ) → ℝ,
      ∀ b V, F b V = -b * Real.log (∑ a, Real.exp (-(V a) / b)) := ⟨_, fun _ _ => rfl⟩
  have hSsucc : ∀ t a, 1 ≤ t → S t a = S (t - 1) a + g t a := by
    intro t a ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    rw [hS, hS, Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
  have hS0 : ∀ a, S 0 a = 0 := fun a => by rw [hS]; simp
  have hqpos : ∀ t a, 0 < q t a := fun t a => by
    rw [hq]; exact div_pos (Real.exp_pos _) (hZpos _ _)
  have hq1 : ∀ t, ∑ a, q t a = 1 := fun t => by
    simp only [hq]; rw [← Finset.sum_div]; exact div_self (hZpos _ _).ne'
  have F1 : ∀ t, 1 ≤ t → ∑ a, q t a * g t a = D t + F (β t) (S t) - F (β t) (S (t - 1)) := by
    intro t ht
    have e1 : ∑ a, q t a * Real.exp (-(g t a) / β t) =
        (∑ a, Real.exp (-(S t a) / β t)) / ∑ b, Real.exp (-(S (t - 1) b) / β t) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro a _
      rw [hq, hSsucc t a ht, div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
    rw [hD t, e1, Real.log_div (hZpos _ _).ne' (hZpos _ _).ne', hF, hF]; ring
  have F4 : ∀ t, 2 ≤ t →
      F (β (t - 1)) (S (t - 1)) - F (β t) (S (t - 1)) ≤ (β t - β (t - 1)) * H (q t) := by
    intro t ht
    have h1 := gibbs_fin (q t) (S (t - 1)) (hqpos t) (hq1 t) (β (t - 1)) (hβ _ (by omega))
    have h2 := gibbs_eq_fin (q t) (S (t - 1)) (β t) (hβ t (by omega)) (fun a => hq t a)
    rw [hF, hF, hH]; linarith
  have hHle : ∀ t, H (q t) ≤ Real.log K := by
    intro t
    have h := gibbs_fin (q t) (fun _ => 0) (hqpos t) (hq1 t) 1 one_pos
    have e : ∑ _a : Fin K, Real.exp (-(0 : ℝ) / 1) = K := by simp
    rw [e] at h
    simp only [mul_zero, Finset.sum_const_zero, zero_add, one_mul, neg_mul] at h
    rw [hH]; linarith
  have F5 : F (β T) (S T) ≤ S T u := by
    have hb := hβ T hT
    have h1 : Real.exp (-(S T u) / β T) ≤ ∑ a, Real.exp (-(S T a) / β T) :=
      Finset.single_le_sum (f := fun a => Real.exp (-(S T a) / β T))
        (fun a _ => (Real.exp_pos _).le) (Finset.mem_univ u)
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hF]
    have e : β T * (-(S T u) / β T) = -(S T u) := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h2 hb.le
    rw [e] at h3
    linarith
  have F6 : F (β 1) (S (1 - 1)) = -β 1 * Real.log K := by
    rw [hF]
    have e : ∑ a, Real.exp (-(S (1 - 1) a) / β 1) = K := by simp [hS0]
    rw [e]
  have hT' := tele (fun t => F (β t) (S t)) (fun t => F (β t) (S (t - 1)))
    (fun t => (β t - β (t - 1)) * H (q t)) D (fun t => ∑ a, q t a * g t a) T hT F1 F4
  rw [F6] at hT'
  have hsum : ∑ t ∈ Icc 1 T, (∑ a, q t a * g t a - g t u) =
      ∑ t ∈ Icc 1 T, ∑ a, q t a * g t a - S T u := by
    rw [Finset.sum_sub_distrib, hS T u]
  have hcK : ∑ t ∈ Icc 2 T, (β t - β (t - 1)) * H (q t) ≤ (β T - β 1) * Real.log K := by
    rw [← sum_diff β T hT, Finset.sum_mul]
    apply Finset.sum_le_sum; intro t ht; rw [Finset.mem_Icc] at ht
    have h1 : β (t - 1) ≤ β t := by
      have := hmono (t - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this
    exact mul_le_mul_of_nonneg_left (hHle t) (by linarith)
  constructor
  · rw [hsum]; nlinarith
  · rw [hsum]; linarith

/-! ### The relative (measure) part -/

theorem rel_core {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
    [IsProbabilityMeasure μ] (β : ℕ → ℝ) (g : ℕ → X → ℝ) (u : X) (T : ℕ)
    (hβ : ∀ t, 1 ≤ t → 0 < β t) (hmono : ∀ t, 1 ≤ t → β t ≤ β (t + 1)) (hT : 1 ≤ T)
    (hu : 0 < μ {u}) (hmeas : ∀ t, Measurable (g t)) (hbdd : ∀ t, ∃ M : ℝ, ∀ x, |g t x| ≤ M)
    (S : ℕ → X → ℝ) (hS : ∀ t x, S t x = ∑ s ∈ Finset.Icc 1 t, g s x)
    (Z : ℕ → ℝ) (hZ : ∀ t, Z t = ∫ x, Real.exp (-(S (t - 1) x) / β t) ∂μ)
    (dens : ℕ → X → ℝ) (hdens : ∀ t x, dens t x = Real.exp (-(S (t - 1) x) / β t) / Z t)
    (q : ℕ → Measure X) (hq : ∀ t, q t = μ.withDensity fun x => ENNReal.ofReal (dens t x))
    (D : ℕ → ℝ) (hD : ∀ t, D t = ∫ x, g t x ∂(q t) +
        β t * Real.log (∫ x, Real.exp (-(g t x) / β t) ∂(q t)))
    (KL : ℕ → ℝ) (hKL : ∀ t, KL t = ∫ x, Real.log (dens t x) ∂(q t))
    (h : ℝ) (hh : h = Real.log (1 / (μ {u}).toReal)) :
    (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
        β T * h + ∑ t ∈ Finset.Icc 1 T, D t) ∧
    (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
        β 1 * h + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * (h - KL t) +
          ∑ t ∈ Finset.Icc 1 T, D t) := by
  have hSm : ∀ t, Measurable (S t) := by
    intro t
    have e : S t = fun x => ∑ s ∈ Finset.Icc 1 t, g s x := funext (hS t)
    rw [e]; exact Finset.measurable_sum _ fun s _ => hmeas s
  have hSb : ∀ t, Bdd (S t) := by
    intro t
    choose M hM using hbdd
    refine ⟨∑ s ∈ Finset.Icc 1 t, M s, fun x => ?_⟩
    rw [hS]; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => hM s x)
  have hSsucc : ∀ t x, 1 ≤ t → S t x = S (t - 1) x + g t x := by
    intro t x ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    rw [hS, hS, Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]
  have hS0 : ∀ x, S 0 x = 0 := fun x => by rw [hS]; simp
  have hZpos : ∀ t, 1 ≤ t → 0 < Z t := fun t ht => by
    rw [hZ]; exact Zpos μ (hSm _) (hSb _) (hβ t ht)
  have hdeq : ∀ t, dens t = fun x => Real.exp (-(S (t - 1) x) / β t) / Z t :=
    fun t => funext (hdens t)
  have hdm : ∀ t, Measurable (dens t) := by
    intro t; rw [hdeq]; have := hSm (t - 1); fun_prop
  have hdb : ∀ t, Bdd (dens t) := by
    intro t; rw [hdeq]; exact ((hSb _).neg.div_const _).exp.div_const _
  have hd0 : ∀ t, 1 ≤ t → ∀ x, 0 ≤ dens t x := fun t ht x => by
    rw [hdens]; exact div_nonneg (Real.exp_pos _).le (hZpos t ht).le
  have hqi : ∀ t, 1 ≤ t → ∀ f : X → ℝ, ∫ x, f x ∂(q t) = ∫ x, dens t x * f x ∂μ := by
    intro t ht f; rw [hq t]; exact wd_int μ (hdm t) (hd0 t ht) f
  have hd1 : ∀ t, 1 ≤ t → ∫ x, dens t x ∂μ = 1 := by
    intro t ht
    simp only [hdens]
    rw [integral_div, ← hZ t]; exact div_self (hZpos t ht).ne'
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ t, A t = -β t * Real.log (∫ x, Real.exp (-(S t x) / β t) ∂μ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, ∀ t, B t = -β t * Real.log (Z t) := ⟨_, fun _ => rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ, ∀ t, I t = ∫ x, dens t x * S (t - 1) x ∂μ := ⟨_, fun _ => rfl⟩
  have hIint : ∀ t, Integrable (fun x => dens t x * S (t - 1) x) μ := fun t =>
    ((hdb t).mul (hSb _)).int μ ((hdm t).mul (hSm _))
  have hdint : ∀ t (c : ℝ), Integrable (fun x => dens t x * c) μ := fun t c =>
    ((hdb t).mul (Bdd.const c)).int μ ((hdm t).mul measurable_const)
  -- (F1) the potential identity
  have F1 : ∀ t, 1 ≤ t → ∫ x, g t x ∂(q t) = D t + A t - B t := by
    intro t ht
    have hZt := hZpos t ht
    have hZ't : 0 < ∫ x, Real.exp (-(S t x) / β t) ∂μ := Zpos μ (hSm t) (hSb t) (hβ t ht)
    have e1 : ∫ x, Real.exp (-(g t x) / β t) ∂(q t) =
        (∫ x, Real.exp (-(S t x) / β t) ∂μ) / Z t := by
      rw [hqi t ht, ← integral_div]
      congr 1; funext x
      rw [hdens, hSsucc t x ht, div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring
    rw [hD t, e1, Real.log_div hZ't.ne' hZt.ne', hA t, hB t]; ring
  -- (F2) the relative entropy
  have F2 : ∀ t, 1 ≤ t → KL t = -I t / β t - Real.log (Z t) := by
    intro t ht
    have hZt := hZpos t ht
    have e : ∀ x, dens t x * Real.log (dens t x) =
        -(dens t x * S (t - 1) x) / β t - dens t x * Real.log (Z t) := by
      intro x
      have : Real.log (dens t x) = -(S (t - 1) x) / β t - Real.log (Z t) := by
        rw [hdens, Real.log_div (Real.exp_pos _).ne' hZt.ne', Real.log_exp]
      rw [this]; ring
    have i1 : Integrable (fun x => -(dens t x * S (t - 1) x) / β t) μ :=
      ((hIint t).neg).div_const _
    rw [hKL t, hqi t ht]
    simp only [e]
    rw [integral_sub i1 (hdint t _), integral_div, integral_neg, integral_mul_const, hd1 t ht,
      hI t]
    ring
  -- (F3) nonnegativity of the relative entropy
  have F3 : ∀ t, 1 ≤ t → I t / β t + Real.log (Z t) ≤ 0 := by
    intro t ht
    have hZt := hZpos t ht
    have hc := core μ (hdm t) (hdb t) (hd0 t ht)
      (y := fun x => S (t - 1) x / β t + Real.log (Z t))
      (by have := hSm (t - 1); fun_prop) (((hSb _).div_const _).add (Bdd.const _)) (hd1 t ht)
    have e1 : ∀ x, dens t x * Real.exp (S (t - 1) x / β t + Real.log (Z t)) = 1 := by
      intro x
      have h0 : Real.exp (-(S (t - 1) x) / β t) * Real.exp (S (t - 1) x / β t) = 1 := by
        rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
      rw [hdens, Real.exp_add, Real.exp_log hZt]
      rw [show Real.exp (-(S (t - 1) x) / β t) / Z t * (Real.exp (S (t - 1) x / β t) * Z t) =
        (Real.exp (-(S (t - 1) x) / β t) * Real.exp (S (t - 1) x / β t)) * (Z t / Z t) by ring,
        h0, div_self hZt.ne', one_mul]
    have e2 : ∀ x, dens t x * (S (t - 1) x / β t + Real.log (Z t)) =
        dens t x * S (t - 1) x / β t + dens t x * Real.log (Z t) := fun x => by ring
    simp only [e1, e2] at hc
    rw [integral_add ((hIint t).div_const _) (hdint t _), integral_div, integral_mul_const,
      hd1 t ht, ← hI t] at hc
    have h1 : ∫ _x : X, (1 : ℝ) ∂μ = 1 := by simp
    rw [h1] at hc
    linarith
  -- (F4) the Gibbs variational inequality across a change of temperature
  have F4 : ∀ t, 2 ≤ t → A (t - 1) - B t ≤ -(β t - β (t - 1)) * KL t := by
    intro t ht
    have ht1 : 1 ≤ t := by omega
    have hb := hβ t ht1
    have hb' := hβ (t - 1) (by omega)
    have hZt := hZpos t ht1
    set Z'' := ∫ x, Real.exp (-(S (t - 1) x) / β (t - 1)) ∂μ with hZ''
    have hZ''p : 0 < Z'' := Zpos μ (hSm _) (hSb _) hb'
    have hc := core μ (hdm t) (hdb t) (hd0 t ht1)
      (y := fun x => S (t - 1) x * (1 / β t - 1 / β (t - 1)) + (Real.log (Z t) - Real.log Z''))
      (by have := hSm (t - 1); fun_prop)
      (((hSb _).mul (Bdd.const _)).add (Bdd.const _)) (hd1 t ht1)
    have e1 : ∀ x, dens t x * Real.exp (S (t - 1) x * (1 / β t - 1 / β (t - 1)) +
        (Real.log (Z t) - Real.log Z'')) = Real.exp (-(S (t - 1) x) / β (t - 1)) / Z'' := by
      intro x
      have h0 : Real.exp (-(S (t - 1) x) / β t) *
          Real.exp (S (t - 1) x * (1 / β t - 1 / β (t - 1))) =
          Real.exp (-(S (t - 1) x) / β (t - 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hdens, Real.exp_add, Real.exp_sub, Real.exp_log hZt, Real.exp_log hZ''p]
      rw [show Real.exp (-(S (t - 1) x) / β t) / Z t *
          (Real.exp (S (t - 1) x * (1 / β t - 1 / β (t - 1))) * (Z t / Z'')) =
        (Real.exp (-(S (t - 1) x) / β t) * Real.exp (S (t - 1) x * (1 / β t - 1 / β (t - 1)))) *
          (Z t / Z t) / Z'' by ring, h0, div_self hZt.ne', mul_one]
    have e2 : ∀ x, dens t x * (S (t - 1) x * (1 / β t - 1 / β (t - 1)) +
        (Real.log (Z t) - Real.log Z'')) =
        dens t x * S (t - 1) x * (1 / β t - 1 / β (t - 1)) +
          dens t x * (Real.log (Z t) - Real.log Z'') := fun x => by ring
    simp only [e1, e2] at hc
    rw [integral_add ((hIint t).mul_const _) (hdint t _), integral_mul_const, integral_mul_const,
      hd1 t ht1, ← hI t, integral_div, ← hZ'', div_self hZ''p.ne'] at hc
    have key := mul_le_mul_of_nonneg_left hc hb'.le
    rw [hA (t - 1), hB t, F2 t ht1]
    have e3 : -(β t - β (t - 1)) * (-I t / β t - Real.log (Z t)) -
        (-β (t - 1) * Real.log Z'' - -β t * Real.log (Z t)) =
        -(β (t - 1) * (I t * (1 / β t - 1 / β (t - 1)) + 1 * (Real.log (Z t) - Real.log Z''))) := by
      field_simp; ring
    have e4 : β (t - 1) * (1 - 1 : ℝ) = 0 := by ring
    rw [e4] at key
    linarith
  -- (F5), (F6) boundary terms
  have F5 : A T ≤ S T u + β T * h := by
    rw [hA, hh]; exact atom μ (hSm T) (hSb T) (hβ T hT) u hu
  have F6 : B 1 = 0 := by
    have : Z 1 = 1 := by rw [hZ]; simp [hS0]
    rw [hB, this, Real.log_one, mul_zero]
  have hT' := tele A B (fun t => -(β t - β (t - 1)) * KL t) D (fun t => ∫ x, g t x ∂(q t)) T hT
    F1 F4
  rw [F6] at hT'
  have hsum : ∑ t ∈ Icc 1 T, (∫ x, g t x ∂(q t) - g t u) =
      ∑ t ∈ Icc 1 T, ∫ x, g t x ∂(q t) - S T u := by
    rw [Finset.sum_sub_distrib, hS T u]
  constructor
  · have hc0 : ∑ t ∈ Icc 2 T, -(β t - β (t - 1)) * KL t ≤ 0 := by
      apply Finset.sum_nonpos; intro t ht; rw [Finset.mem_Icc] at ht
      have h1 : β (t - 1) ≤ β t := by
        have := hmono (t - 1) (by omega); rwa [Nat.sub_add_cancel (by omega)] at this
      have h2 : 0 ≤ KL t := by rw [F2 t (by omega), neg_div]; linarith [F3 t (by omega)]
      have : 0 ≤ (β t - β (t - 1)) * KL t := mul_nonneg (by linarith) h2
      linarith
    rw [hsum]; linarith
  · have e : ∑ t ∈ Icc 2 T, (β t - β (t - 1)) * (h - KL t) =
        (∑ t ∈ Icc 2 T, (β t - β (t - 1))) * h + ∑ t ∈ Icc 2 T, -(β t - β (t - 1)) * KL t := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro t _; ring
    rw [hsum, e, sum_diff β T hT]
    linarith

end J2

namespace IAFTRL

open MeasureTheory

theorem _root_.solution :
    (∀ {K : ℕ} (β : ℕ → ℝ) (g : ℕ → Fin K → ℝ) (u : Fin K) (T : ℕ),
      (∀ t, 1 ≤ t → 0 < β t) → (∀ t, 1 ≤ t → β t ≤ β (t + 1)) → 1 ≤ T →
      let S : ℕ → Fin K → ℝ := fun t a => ∑ s ∈ Finset.Icc 1 t, g s a
      let q : ℕ → Fin K → ℝ := fun t a =>
        Real.exp (-(S (t - 1) a) / β t) / ∑ b, Real.exp (-(S (t - 1) b) / β t)
      let D : ℕ → ℝ := fun t =>
        ∑ a, q t a * g t a + β t * Real.log (∑ a, q t a * Real.exp (-(g t a) / β t))
      let H : (Fin K → ℝ) → ℝ := fun p => -∑ a, p a * Real.log (p a)
      (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
          β T * Real.log K + ∑ t ∈ Finset.Icc 1 T, D t) ∧
      (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
          β 1 * Real.log K + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * H (q t) +
            ∑ t ∈ Finset.Icc 1 T, D t)) ∧
    (∀ {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
      [IsProbabilityMeasure μ] (β : ℕ → ℝ) (g : ℕ → X → ℝ) (u : X) (T : ℕ),
      (∀ t, 1 ≤ t → 0 < β t) → (∀ t, 1 ≤ t → β t ≤ β (t + 1)) → 1 ≤ T → 0 < μ {u} →
      (∀ t, Measurable (g t)) → (∀ t, ∃ M : ℝ, ∀ x, |g t x| ≤ M) →
      let S : ℕ → X → ℝ := fun t x => ∑ s ∈ Finset.Icc 1 t, g s x
      let Z : ℕ → ℝ := fun t => ∫ x, Real.exp (-(S (t - 1) x) / β t) ∂μ
      let dens : ℕ → X → ℝ := fun t x => Real.exp (-(S (t - 1) x) / β t) / Z t
      let q : ℕ → Measure X := fun t => μ.withDensity fun x => ENNReal.ofReal (dens t x)
      let D : ℕ → ℝ := fun t =>
        ∫ x, g t x ∂(q t) + β t * Real.log (∫ x, Real.exp (-(g t x) / β t) ∂(q t))
      let KL : ℕ → ℝ := fun t => ∫ x, Real.log (dens t x) ∂(q t)
      let h : ℝ := Real.log (1 / (μ {u}).toReal)
      (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
          β T * h + ∑ t ∈ Finset.Icc 1 T, D t) ∧
      (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
          β 1 * h + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * (h - KL t) +
            ∑ t ∈ Finset.Icc 1 T, D t)) := by
  refine ⟨?_, ?_⟩
  · intro K β g u T hβ hmono hT S q D H
    exact J2.fin_core β g u T hβ hmono hT S (fun _ _ => rfl) q (fun _ _ => rfl) D (fun _ => rfl)
      H (fun _ => rfl)
  · intro X _ _ μ _ β g u T hβ hmono hT hu hmeas hbdd S Z dens q D KL h
    exact J2.rel_core μ β g u T hβ hmono hT hu hmeas hbdd S (fun _ _ => rfl) Z (fun _ => rfl)
      dens (fun _ _ => rfl) q (fun _ => rfl) D (fun _ => rfl) KL (fun _ => rfl) h rfl

end IAFTRL
