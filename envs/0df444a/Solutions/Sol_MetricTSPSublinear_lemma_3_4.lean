-- Prove2me | solution 1 for MetricTSPSublinear.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:47:10.424843+00:00
-- url     : https://prove2.me/submissions/2940fd7b-f2a8-4e74-8107-105e0dab63ea

import Mathlib

open MeasureTheory

namespace MTSPL34

lemma cat_singleton {N : ℕ} (p : Fin N → ℝ) (i : Fin N) :
    (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)) {i} = ENNReal.ofReal (p i) := by
  simp [Finset.sum_apply, Pi.single_apply]

lemma cat_univ {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    IsProbabilityMeasure (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)) := by
  constructor
  simp [Finset.sum_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), h1, ENNReal.ofReal_one]

lemma cat_integral {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) (g : Fin N → ℝ) :
    ∫ i, g i ∂(∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)) = ∑ i, p i * g i := by
  have := cat_univ p hp h1
  rw [integral_fintype (hf := Integrable.of_finite)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [measureReal_def, cat_singleton, ENNReal.toReal_ofReal (hp i), smul_eq_mul]

lemma exp_bound3 (y : ℝ) (hy : |y| ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 / 9 * |y| ^ 3 := by
  have := Real.exp_bound hy (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  have h2 := (abs_le.mp this).2
  norm_num at h2
  linarith


lemma exp_convex_bound (B y t : ℝ) (hB : 0 < B) (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    Real.exp (t * y) ≤ 1 + y / B * (Real.exp (t * B) - 1) := by
  have ha : 0 ≤ 1 - y / B := by rw [sub_nonneg, div_le_one hB]; exact hyB
  have hb : 0 ≤ y / B := div_nonneg hy0 hB.le
  have := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (t * B)) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  have e : y / B * (t * B) = t * y := by field_simp
  rw [e] at this
  linarith

lemma mgf_sum_le {N s : ℕ} (p f : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (B X : ℝ) (hB : 0 < B) (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) (hX : ∑ i, p i * f i = X)
    (t : ℝ) :
    ProbabilityTheory.mgf (fun I : Fin s → Fin N => ∑ j, f (I j))
      (Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)))) t
      ≤ Real.exp (s * (X / B * (Real.exp (t * B) - 1))) := by
  have := cat_univ p hp h1
  set cat : Measure (Fin N) := ∑ k, ENNReal.ofReal (p k) • Measure.dirac k with hcat
  have hind : ProbabilityTheory.iIndepFun (fun j (I : Fin s → Fin N) => f (I j))
      (Measure.pi (fun _ : Fin s => cat)) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => f) (fun _ => (measurable_of_finite f).aemeasurable)
  have hsum : (fun I : Fin s → Fin N => ∑ j, f (I j)) = ∑ j, (fun (I : Fin s → Fin N) => f (I j)) := by
    ext I; simp
  rw [hsum, hind.mgf_sum (fun j => (measurable_of_finite f).comp (measurable_pi_apply j))]
  have hM : ∀ j : Fin s, ProbabilityTheory.mgf (fun (I : Fin s → Fin N) => f (I j))
      (Measure.pi (fun _ : Fin s => cat)) t = ∑ i, p i * Real.exp (t * f i) := by
    intro j
    rw [ProbabilityTheory.mgf]
    rw [integral_comp_eval (μ := fun _ : Fin s => cat) (i := j) (f := fun i => Real.exp (t * f i)) (measurable_of_finite _).aestronglyMeasurable]
    exact cat_integral p hp h1 _
  simp only [hM, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.exp_nat_mul]
  have hpos : 0 ≤ ∑ i, p i * Real.exp (t * f i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Real.exp_pos _).le
  refine pow_le_pow_left₀ hpos ?_ s
  calc ∑ i, p i * Real.exp (t * f i) ≤ ∑ i, p i * (1 + f i / B * (Real.exp (t * B) - 1)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (exp_convex_bound B (f i) t hB (hf0 i) (hfB i)) (hp i)
    _ = ∑ i, p i + (∑ i, p i * f i) / B * (Real.exp (t * B) - 1) := by
        rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = X / B * (Real.exp (t * B) - 1) + 1 := by rw [h1, hX]; ring
    _ ≤ Real.exp (X / B * (Real.exp (t * B) - 1)) := Real.add_one_le_exp _


lemma upper_tail {N s : ℕ} (p f : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (B X : ℝ) (hB : 0 < B) (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) (hX : ∑ i, p i * f i = X)
    (a l : ℝ) (hl : 0 ≤ l) :
    (Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)))).real
      {I | s * (X + a) ≤ ∑ j, f (I j)}
      ≤ Real.exp (-(s / B) * (l * a - X * (Real.exp l - 1 - l))) := by
  have := cat_univ p hp h1
  have h := ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := fun I : Fin s → Fin N => ∑ j, f (I j))
    (μ := Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N))))
    (s * (X + a)) (t := l / B) (div_nonneg hl hB.le) Integrable.of_finite
  refine h.trans ?_
  have hm := mgf_sum_le (s := s) p f hp h1 B X hB hf0 hfB hX (l / B)
  have e : l / B * B = l := by field_simp
  rw [e] at hm
  calc _ ≤ Real.exp (-(l / B) * (s * (X + a))) * Real.exp (s * (X / B * (Real.exp l - 1))) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]; congr 1; field_simp; ring

lemma lower_tail {N s : ℕ} (p f : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (B X : ℝ) (hB : 0 < B) (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) (hX : ∑ i, p i * f i = X)
    (a l : ℝ) (hl : 0 ≤ l) :
    (Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N)))).real
      {I | ∑ j, f (I j) ≤ s * (X - a)}
      ≤ Real.exp (-(s / B) * (l * a - X * (Real.exp (-l) - 1 + l))) := by
  have := cat_univ p hp h1
  have h := ProbabilityTheory.measure_le_le_exp_mul_mgf (X := fun I : Fin s → Fin N => ∑ j, f (I j))
    (μ := Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N))))
    (s * (X - a)) (t := -(l / B)) (by have := div_nonneg hl hB.le; linarith) Integrable.of_finite
  refine h.trans ?_
  have hm := mgf_sum_le (s := s) p f hp h1 B X hB hf0 hfB hX (-(l / B))
  have e : -(l / B) * B = -l := by field_simp
  rw [e] at hm
  calc _ ≤ Real.exp (-(-(l / B)) * (s * (X - a))) * Real.exp (s * (X / B * (Real.exp (-l) - 1))) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]; congr 1; field_simp; ring


lemma key_exponent (ε U X y : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 ≤ X) (hXU : X ≤ U)
    (hy : |y| = 4 * ε / 5) :
    U * ε ^ 2 / 3 ≤ 4 * ε / 5 * (ε * U) - X * (Real.exp y - 1 - y) := by
  have hy1 : |y| ≤ 1 := by rw [hy]; linarith
  have hb := exp_bound3 y hy1
  have hg0 : 0 ≤ Real.exp y - 1 - y := by have := Real.add_one_le_exp y; linarith
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [hy2, hy] at hb
  have hU : 0 ≤ U := hX.trans hXU
  have h1 : X * (Real.exp y - 1 - y) ≤ U * (Real.exp y - 1 - y) :=
    mul_le_mul_of_nonneg_right hXU hg0
  have h2 : U * (Real.exp y - 1 - y) ≤ U * ((4 * ε / 5) ^ 2 / 2 + 2 / 9 * (4 * ε / 5) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hU
  have h3 : U * ε ^ 2 / 3 ≤ 4 * ε / 5 * (ε * U) - U * ((4 * ε / 5) ^ 2 / 2 + 2 / 9 * (4 * ε / 5) ^ 3) := by
    have : 0 ≤ U * ε ^ 2 * (1 - ε) := by positivity
    nlinarith [mul_nonneg hU (sq_nonneg ε)]
  linarith

lemma main_generic {N s : ℕ} (p f : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1)
    (B X U ε δ : ℝ) (hB : 0 < B) (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) (hX : ∑ i, p i * f i = X)
    (hX0 : 0 ≤ X) (hXU : X ≤ U) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hs0 : 0 < s)
    (hs : Real.log (2 / δ) ≤ s / B * (U * ε ^ 2 / 3)) :
    (Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N))))
      {I | ε * U < |(1 / (s : ℝ)) * ∑ j, f (I j) - X|} ≤ ENNReal.ofReal δ := by
  have := cat_univ p hp h1
  set μ := (Measure.pi (fun _ : Fin s => (∑ k, ENNReal.ofReal (p k) • Measure.dirac k : Measure (Fin N))))
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hsub : {I : Fin s → Fin N | ε * U < |(1 / (s : ℝ)) * ∑ j, f (I j) - X|} ⊆
      {I : Fin s → Fin N | s * (X + ε * U) ≤ ∑ j, f (I j)} ∪ {I | ∑ j, f (I j) ≤ s * (X - ε * U)} := by
    intro I hI
    simp only [Set.mem_ofPred_eq] at hI
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases lt_abs.mp hI with h | h
    · left
      have : X + ε * U < (1 / (s : ℝ)) * ∑ j, f (I j) := by linarith
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hsR] at this
      linarith
    · right
      have : (1 / (s : ℝ)) * ∑ j, f (I j) < X - ε * U := by linarith
      rw [one_div, inv_mul_eq_div, div_lt_iff₀ hsR] at this
      linarith
  have hu := upper_tail (s := s) p f hp h1 B X hB hf0 hfB hX (ε * U) (4 * ε / 5) (by positivity)
  have hl := lower_tail (s := s) p f hp h1 B X hB hf0 hfB hX (ε * U) (4 * ε / 5) (by positivity)
  have k1 := key_exponent ε U X (4 * ε / 5) hε hε1 hX0 hXU (abs_of_pos (by positivity))
  have k2 := key_exponent ε U X (-(4 * ε / 5)) hε hε1 hX0 hXU (by rw [abs_neg]; exact abs_of_pos (by positivity))
  have hsB : 0 ≤ (s : ℝ) / B := by positivity
  have hd : Real.exp (-Real.log (2 / δ)) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have bound : ∀ c : ℝ, U * ε ^ 2 / 3 ≤ c → Real.exp (-(s / B) * c) ≤ δ / 2 := by
    intro c hc
    rw [← hd]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hc hsB]
  have hu' := hu.trans (bound _ k1)
  have hl' := hl.trans (bound _ (by simpa [sub_neg_eq_add] using k2))
  have hreal : μ.real {I : Fin s → Fin N | ε * U < |(1 / (s : ℝ)) * ∑ j, f (I j) - X|} ≤ δ :=
    calc _ ≤ μ.real ({I : Fin s → Fin N | s * (X + ε * U) ≤ ∑ j, f (I j)} ∪ {I | ∑ j, f (I j) ≤ s * (X - ε * U)}) :=
          measureReal_mono hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hu' hl'
      _ = δ := by ring
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

end MTSPL34

theorem solution (N : ℕ) (x b : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) (hxb : ∀ i, x i ≤ b i) (hb : ∀ i, 0 < b i)
    (U : ℝ) (hU : 0 < U) (hXU : ∑ i, x i ≤ U) (ε δ : ℝ) (hε : 0 < ε ∧ ε < 1) (hδ : 0 < δ ∧ δ < 1) (s : ℕ)
    (hs : ⌈3 * (∑ i, b i) / (ε ^ 2 * U) * Real.log (2 / δ)⌉₊ ≤ s) :
    let B := ∑ i, b i
    let X := ∑ i, x i
    let cat : Measure (Fin N) := ∑ i, ENNReal.ofReal (b i / B) • Measure.dirac i
    let Xhat : (Fin s → Fin N) → ℝ := fun I => (1 / (s : ℝ)) * ∑ j, x (I j) / (b (I j) / B)
    (Measure.pi (fun _ : Fin s => cat)) {I | ε * U < |Xhat I - X|} ≤ ENNReal.ofReal δ := by
  intro B X cat Xhat
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hempty : {I : Fin s → Fin 0 | ε * U < |Xhat I - X|} = ∅ := by
      ext I
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hX0 : X = 0 := by simp [X]
      have hXh : Xhat I = 0 := by
        rcases Nat.eq_zero_or_pos s with hs0 | hs0
        · subst hs0; simp [Xhat]
        · exact (I ⟨0, hs0⟩).elim0
      rw [hXh, hX0, sub_zero, abs_zero]
      exact (mul_pos hε.1 hU).le
    rw [hempty, measure_empty]
    exact zero_le
  · have hB : 0 < B := Finset.sum_pos (fun i _ => hb i) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    set p : Fin N → ℝ := fun i => b i / B with hpdef
    set f : Fin N → ℝ := fun i => x i / (b i / B) with hfdef
    have hp : ∀ i, 0 ≤ p i := fun i => (div_pos (hb i) hB).le
    have h1 : ∑ i, p i = 1 := by
      simp only [p]; rw [← Finset.sum_div]; exact div_self hB.ne'
    have hf0 : ∀ i, 0 ≤ f i := fun i => div_nonneg (hx i) (div_pos (hb i) hB).le
    have hfB : ∀ i, f i ≤ B := by
      intro i
      simp only [f]
      rw [div_le_iff₀ (div_pos (hb i) hB)]
      rw [mul_div_cancel₀ _ hB.ne']
      exact hxb i
    have hXf : ∑ i, p i * f i = X := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [p, f]
      exact mul_div_cancel₀ _ (div_pos (hb i) hB).ne'
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => hx i
    have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ.1]; linarith)
    have hc : 3 * B / (ε ^ 2 * U) * Real.log (2 / δ) ≤ s :=
      (Nat.le_ceil _).trans (by exact_mod_cast hs)
    have hcpos : 0 < 3 * B / (ε ^ 2 * U) * Real.log (2 / δ) := by
      have := hε.1; positivity
    have hs0 : 0 < s := by exact_mod_cast hcpos.trans_le hc
    have hs' : Real.log (2 / δ) ≤ s / B * (U * ε ^ 2 / 3) := by
      have hk : 0 < ε ^ 2 * U / (3 * B) := by have := hε.1; positivity
      have := mul_le_mul_of_nonneg_right hc hk.le
      have e : 3 * B / (ε ^ 2 * U) * Real.log (2 / δ) * (ε ^ 2 * U / (3 * B)) = Real.log (2 / δ) := by
        have := hε.1; field_simp
      have e2 : (s : ℝ) * (ε ^ 2 * U / (3 * B)) = s / B * (U * ε ^ 2 / 3) := by ring
      linarith
    exact MTSPL34.main_generic p f hp h1 B X U ε δ hB hf0 hfB hXf hX0 hXU hε.1 hε.2 hδ.1 hs0 hs'
