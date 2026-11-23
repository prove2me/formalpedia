-- Prove2me | solution 3 for GrothendieckLB.Supplement.limitingScheme_bound_of_coefficient_gap
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:50:37.433718+00:00
-- url     : https://prove2.me/submissions/971040ae-0909-4db6-b205-cb2e36d8d228

import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_rounding_inequality
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Complex.TaylorSeries

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement Filter MeasureTheory
open scoped Topology Matrix ENNReal NNReal

/- The Gram factorization, entrywise powers, and elementary order bounds are
   adapted from Prove2Me c85a8429-0642-4db2-8539-0cf94b08f926. The Taylor
   expansion and parity argument adapt e5be45ba-30d4-4759-b81c-18c40f16b01e.
   Both are public submissions under Apache 2.0. -/
namespace DirectSchemeBound
private theorem unit_near {x : ℝ} (hx : |x| < 1) : ∀ᶠ y in 𝓝 x, |y| < 1 :=
  (isOpen_lt continuous_abs continuous_const).mem_nhds hx

private theorem allowable_odd {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ)
    {t : ℝ} (ht : |t| < 1) : ρ (-t) = -ρ t := by
  obtain ⟨c, hev, _, _, heq⟩ := hρ
  rw [heq (-t) (by simpa using ht), heq t ht, ← tsum_neg]
  apply tsum_congr
  intro n
  rcases Nat.even_or_odd n with he | ho
  · simp [hev n he]
  · rw [ho.neg_pow, mul_neg]

private theorem normalized_corr_odd {k : ℕ} (S : LimitingScheme k) {t : ℝ} (ht : |t| < 1) :
    S.corr (-t) = -S.corr t := by
  let P (t : ℝ) (x y : Fin k → ℝ) := ∏ i : Fin k,
    GrothendieckConstant.gaussianPairDensity 1 (S.ρ i t) (fun _ => x i) (fun _ => y i)
  have hP (x y : Fin k → ℝ) : P (-t) x (-y) = P t x y := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [allowable_odd (S.ρ_allowable i) ht]
    simp only [GrothendieckConstant.gaussianPairDensity, Fin.prod_univ_one, Pi.neg_apply]
    ring_nf
  have hint (x : Fin k → ℝ) :
      (∫ y, S.f x * S.g y * P (-t) x y) = -(∫ y, S.f x * S.g y * P t x y) := by
    calc
      _ = ∫ y, S.f x * S.g (-y) * P (-t) x (-y) :=
        (integral_neg_eq_self (fun y => S.f x * S.g y * P (-t) x y) volume).symm
      _ = ∫ y, -(S.f x * S.g y * P t x y) := by
        apply integral_congr_ae
        filter_upwards [S.g_odd] with y hy
        rw [hy, hP]
        ring
      _ = _ := integral_neg _
  change Real.pi / 2 * (∫ x, ∫ y, S.f x * S.g y * P (-t) x y) =
    -(Real.pi / 2 * (∫ x, ∫ y, S.f x * S.g y * P t x y))
  simp only [hint, integral_neg, mul_neg]

private theorem real_taylor_on_disk (H : ℝ → ℝ) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hreal : ∀ t : ℝ, |t| < 1 → F t = (H t : ℂ)) :
    AnalyticAt ℝ H 0 ∧
      ∀ t : ℝ, |t| < 1 → H t = ∑' n, taylorCoeff n H * t^n := by
  have hmem {x : ℝ} (hx : |x| < 1) : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, Real.norm_eq_abs] using hx
  have hiter (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n F) (Metric.ball 0 1) := by
    induction n with
    | zero => simpa using hF.analyticOnNhd Metric.isOpen_ball
    | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hjets (n : ℕ) : ∀ t : ℝ, |t| < 1 →
      iteratedDeriv n H t = (iteratedDeriv n F (t : ℂ)).re := by
    induction n with
    | zero => intro t ht; simp [hreal t ht]
    | succ n ih =>
      intro t ht
      have hlocal : iteratedDeriv n H =ᶠ[𝓝 t] fun y : ℝ => (iteratedDeriv n F (y : ℂ)).re :=
        (unit_near ht).mono fun y hy => ih y hy
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact hlocal.deriv_eq.trans ((hiter n _ (hmem ht)).differentiableAt.hasDerivAt.real_of_complex.deriv)
  have hzero : |(0 : ℝ)| < 1 := by norm_num
  constructor
  · have hf0 : AnalyticAt ℂ F ((0 : ℝ) : ℂ) := (hF.analyticOnNhd Metric.isOpen_ball) _ (hmem hzero)
    apply hf0.re_ofReal.congr
    filter_upwards [unit_near hzero] with t ht
    simp [hreal t ht]
  · intro t ht
    have hc := Complex.hasSum_taylorSeries_on_ball hF (hmem ht)
    have hr := RCLike.hasSum_re ℂ hc
    rw [hreal t ht] at hr
    have hs : HasSum (fun n : ℕ => taylorCoeff n H * t^n) (H t) := by
      apply hr.congr_fun
      intro n
      rw [taylorCoeff, hjets n 0 hzero]
      change ((iteratedDeriv n F (0 : ℂ)).re / n.factorial) * t^n =
        (((n.factorial : ℂ)⁻¹) * (((t : ℂ) - 0)^n * iteratedDeriv n F 0)).re
      simp only [sub_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
        Complex.re_ofReal_mul]
      ring
    exact hs.tsum_eq.symm


section Matrices
open Matrix
variable {ι : Type*} [Fintype ι]

lemma psd_entrywise_pow (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => G i j ^ k) := by
  induction k with
  | zero =>
    have he : (fun i j => G i j ^ 0 : Matrix ι ι ℝ) =
        Matrix.vecMulVec (fun _ : ι => (1:ℝ)) (star (fun _ : ι => (1:ℝ))) := by
      ext i j; simp [Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  | succ k hk =>
    have he : (fun i j => G i j ^ (k+1) : Matrix ι ι ℝ) =
        (fun i j => G i j ^ k) ⊙ G := by
      ext i j; simp [pow_succ, Matrix.hadamard]
    rw [he]
    exact hk.hadamard hG

section Factorization
open scoped MatrixOrder

/-- Columns of the positive square root realize any finite real PSD matrix. -/
lemma exists_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    ∃ w : ι → EuclideanSpace ℝ ι, ∀ i j, inner ℝ (w i) (w j) = B i j := by
  classical
  let R := CFC.sqrt B
  have hR : R.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hsq : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  refine ⟨fun i => WithLp.toLp 2 (R.transpose i), ?_⟩
  intro i j
  rw [inner_matrix_col_col, hR, hsq]

end Factorization

lemma exists_unit_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1) :
    ∃ w : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)),
      (∀ i, ‖w i‖ = 1) ∧ (∀ i j, inner ℝ (w i) (w j) = B i j) := by
  classical
  obtain ⟨w, hw⟩ := exists_gram B hB
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  refine ⟨fun i => e (w i), ?_, ?_⟩
  · intro i
    rw [e.norm_map]
    have h := hw i i
    rw [real_inner_self_eq_norm_sq, hdiag] at h
    nlinarith [norm_nonneg (w i)]
  · intro i j
    rw [e.inner_map_map, hw]


end Matrices
theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith


theorem sdpSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (sdpSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 : |inner ℝ (u i) (v j)| ≤ 1 := by
    have := abs_real_inner_le_norm (u i) (v j)
    rw [hu i, hv j] at this
    simpa using this
  calc A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
    _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |A i j| := mul_one _


theorem one_le_of_isGrothendieckBound {K : ℝ} (hK : IsGrothendieckBound K) : 1 ≤ K := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  have hmem : (1 : ℝ) ∈ optSet A := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
    simp [A]
  have hopt : optValue A = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨1, hmem⟩
      rintro s ⟨x, y, hx, hy, rfl⟩
      simp only [A, Fin.sum_univ_one, one_mul]
      rcases hx 0 with h | h <;> rcases hy 0 with h' | h' <;> rw [h, h'] <;> norm_num
    · exact le_csSup (optSet_bdd A) hmem
  let v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_eq]
  have hsdp : 1 ≤ sdpValue A := by
    apply le_csSup (sdpSet_bdd A)
    refine ⟨1, fun _ => v, fun _ => v, fun _ => hv, fun _ => hv, ?_⟩
    simp [A, hv]
  have h := hK 1 1 A
  rw [hopt, mul_one] at h
  exact hsdp.trans h


lemma sdpSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : (sdpSet A).Nonempty := by
  let e : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq]
  exact ⟨_, 1, (fun _ => e), (fun _ => e), (fun _ => he), (fun _ => he), rfl⟩

private theorem gram_diag {m n d : ℕ}
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (a : Fin m ⊕ Fin n) :
    Matrix.gram ℝ (Sum.elim u v) a a = 1 := by
  cases a with
  | inl i => simp [Matrix.gram_apply, hu]
  | inr j => simp [Matrix.gram_apply, hv]

private theorem gram_scale {m n d : ℕ}
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ (D : ℕ) (U : Fin m → EuclideanSpace ℝ (Fin D)) (V : Fin n → EuclideanSpace ℝ (Fin D)),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
      (∀ i j, inner ℝ (U i) (V j) = r * inner ℝ (u i) (v j)) := by
  classical
  let G := Matrix.gram ℝ (Sum.elim u v)
  let M := r • G + (1-r) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
  have hG : G.PosSemidef := Matrix.posSemidef_gram _ _
  have hM : M.PosSemidef := (hG.smul hr).add (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hr1))
  have hdiag (a) : M a a = 1 := by
    change r * Matrix.gram ℝ (Sum.elim u v) a a + (1-r) * (1 : Matrix _ _ ℝ) a a = 1
    rw [gram_diag u v hu hv, Matrix.one_apply_eq]
    ring
  obtain ⟨w, hw, hgram⟩ := exists_unit_gram _ hM hdiag
  refine ⟨_, fun i => w (.inl i), fun j => w (.inr j), fun i => hw _, fun j => hw _, ?_⟩
  intro i j
  simpa [M, G, Matrix.gram_apply, Matrix.one_apply] using hgram (.inl i) (.inr j)

private theorem gram_power_objective {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) (p : ℕ) :
    |∑ i, ∑ j, A i j * (inner ℝ (u i) (v j))^p| ≤ sdpValue A := by
  classical
  let G := Matrix.gram ℝ (Sum.elim u v)
  let M : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := fun i j => G i j ^ p
  have hM : M.PosSemidef := psd_entrywise_pow G (Matrix.posSemidef_gram _ _) p
  have hd (a) : M a a = 1 := by
    change (Matrix.gram ℝ (Sum.elim u v) a a)^p = 1
    rw [gram_diag u v hu hv, one_pow]
  obtain ⟨w, hw, hgram⟩ := exists_unit_gram _ hM hd
  have hrow (i : Fin m) (j : Fin n) :
      inner ℝ (w (.inl i)) (w (.inr j)) = (inner ℝ (u i) (v j))^p := by
    simpa [M, G, Matrix.gram_apply] using hgram (.inl i) (.inr j)
  apply abs_le.mpr
  constructor
  · apply neg_le.mp
    apply le_csSup (sdpSet_bdd A)
    refine ⟨_, fun i => -w (.inl i), fun j => w (.inr j), fun i => by simp [hw],
      fun j => hw _, ?_⟩
    simp [hrow]
  · apply le_csSup (sdpSet_bdd A)
    refine ⟨_, fun i => w (.inl i), fun j => w (.inr j),
      fun i => hw _, fun j => hw _, ?_⟩
    simp [hrow]

private theorem allowable_extension {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (Metric.ball 0 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖φ z‖ ≤ ‖z‖) ∧
      (∀ x : ℝ, |x| < 1 → φ x = (ρ x : ℂ)) := by
  obtain ⟨c, he, hs, hmass, heq⟩ := hρ
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  have hrad : (1 : ℝ≥0∞) ≤ p.radius := by
    have h := p.le_radius_of_summable_norm (r := (1 : ℝ≥0)) (by
      simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using hs)
    simpa using h
  have hrepr (z : ℂ) : p.sum z = ∑' n, (c n : ℂ) * z^n :=
    FormalMultilinearSeries.ofScalars_sum_eq (fun n => (c n : ℂ)) z
  refine ⟨p.sum, ?_, ?_, ?_⟩
  · intro z hz
    apply (p.analyticOnNhd z ?_).differentiableAt.differentiableWithinAt
    apply Metric.eball_subset_eball hrad
    change z ∈ Metric.eball (0 : ℂ) ((1 : ℝ≥0) : ℝ≥0∞)
    rw [Metric.eball_coe]
    exact hz
  · intro z hz
    rw [hrepr]
    apply le_trans (tsum_of_norm_bounded (hs.hasSum.mul_right ‖z‖) ?_)
      (mul_le_of_le_one_left (norm_nonneg _) hmass)
    intro n
    cases n with
    | zero => simp [he 0 (by decide)]
    | succ n =>
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg z) (pow_le_one₀ (norm_nonneg z) hz.le)) (abs_nonneg _)
  · intro x hx
    rw [hrepr, heq x hx, Complex.ofReal_tsum]
    exact tsum_congr fun n => by push_cast; ring

private noncomputable def gaussPref (w : ℂ) : ℂ :=
  (1 - w^2) ^ ((-(1/2 : ℝ) : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ)

private noncomputable def gaussKernel (w : ℂ) (x y : ℝ) : ℂ :=
  gaussPref w * Complex.exp (-(
    ((((x+y)^2/4 : ℝ) : ℂ) * (1+w)⁻¹) +
    ((((x-y)^2/4 : ℝ) : ℂ) * (1-w)⁻¹)))

private theorem gaussian_factors {w : ℂ} (hw : ‖w‖ < 1) :
    (1+w ≠ 0) ∧ (1-w ≠ 0) ∧ 1-w^2 ∈ Complex.slitPlane := by
  have ht : |w.re| < 1 := (Complex.abs_re_le_norm w).trans_lt hw
  have hre₁ : 0 < (1+w).re := by simp; linarith [(abs_lt.mp ht).1]
  have hre₂ : 0 < (1-w).re := by simp; linarith [(abs_lt.mp ht).2]
  refine ⟨fun h => by rw [h] at hre₁; simpa using hre₁,
    fun h => by rw [h] at hre₂; simpa using hre₂, ?_⟩
  rw [sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_neg, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw (by decide)

private theorem pref_diff {w : ℂ} (hw : ‖w‖ < 1) : DifferentiableAt ℂ gaussPref w := by
  have hslit := (gaussian_factors hw).2.2
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1-z^2) w := by fun_prop
  unfold gaussPref
  exact (hd.cpow_const hslit).div_const _

private theorem kernel_diff {w : ℂ} (hw : ‖w‖ < 1) (x y : ℝ) :
    DifferentiableAt ℂ (fun z => gaussKernel z x y) w := by
  obtain ⟨h₁, h₂, _⟩ := gaussian_factors hw
  unfold gaussKernel
  apply (pref_diff hw).mul
  fun_prop (disch := assumption)

private theorem kernel_real {t : ℝ} (ht : |t| < 1) (x y : ℝ) :
    gaussKernel t x y =
      (((1 / (2 * Real.pi * Real.sqrt (1-t^2))) *
        Real.exp (-(x^2 - 2*t*x*y + y^2)/(2*(1-t^2))) : ℝ) : ℂ) := by
  have h₁ : 0 < 1+t := by linarith [(abs_lt.mp ht).1]
  have h₂ : 0 < 1-t := by linarith [(abs_lt.mp ht).2]
  have hsq : 0 < 1-t^2 := by nlinarith [mul_pos h₁ h₂]
  have hpre : gaussPref t = ((1/(2 * Real.pi * Real.sqrt (1-t^2)) : ℝ) : ℂ) := by
    unfold gaussPref
    rw [show (1 : ℂ) - (t : ℂ)^2 = ((1-t^2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hsq.le, Real.rpow_neg hsq.le, ← Real.sqrt_eq_rpow]
    push_cast
    ring
  have har : -(((x+y)^2/4)*(1+t)⁻¹ + ((x-y)^2/4)*(1-t)⁻¹) =
      -(x^2 - 2*t*x*y + y^2)/(2*(1-t^2)) := by
    field_simp [h₁.ne',h₂.ne',hsq.ne'] <;> ring
  unfold gaussKernel
  rw [hpre, Complex.ofReal_mul]
  congr 1
  rw [← har]
  push_cast
  ring

private theorem inv_re_lower {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    (1-R)/(1+R)^2 ≤ ((1+w)⁻¹).re := by
  have h₁ : 1-R ≤ (1+w).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h₂ : ‖1+w‖ ≤ 1+R := by
    calc
      _ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + R := by rw [norm_one]; linarith
  have hn := (gaussian_factors (hw.trans_lt hR1)).1
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply div_le_div₀ ((sub_nonneg.mpr hR1.le).trans h₁) h₁ (sq_pos_of_pos (norm_pos_iff.mpr hn))
  exact pow_le_pow_left₀ (norm_nonneg _) h₂ 2

private theorem kernel_bound (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ (w : ℂ), ‖w‖ ≤ R → ∀ x y : ℝ, ‖gaussKernel w x y‖ ≤
        C * (Real.exp (-a*x^2) * Real.exp (-a*y^2)) := by
  have hcont : ContinuousOn (fun w : ℂ => ‖gaussPref w‖) (Metric.closedBall 0 R) := by
    intro w hw
    exact (pref_diff ((by simpa using hw : ‖w‖ ≤ R).trans_lt hR1)).continuousAt.norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hcont
  let D := (1-R)/(1+R)^2
  have hD : 0 < D := div_pos (sub_pos.mpr hR1) (by positivity)
  refine ⟨max C 0, D/2, le_max_right _ _, by positivity, ?_⟩
  intro w hw x y
  have hpre : ‖gaussPref w‖ ≤ max C 0 :=
    (hC (Set.mem_image_of_mem _ (show w ∈ Metric.closedBall 0 R by simpa using hw))).trans
      (le_max_left _ _)
  have hplus : D ≤ ((1+w)⁻¹).re := inv_re_lower hR hR1 hw
  have hminus : D ≤ ((1-w)⁻¹).re := by
    simpa only [D, sub_eq_add_neg] using
      (inv_re_lower hR hR1 (show ‖-w‖ ≤ R by rwa [norm_neg]))
  rw [gaussKernel, norm_mul, Complex.norm_exp, ← Real.exp_add]
  apply mul_le_mul hpre _ (Real.exp_pos _).le (le_max_right _ _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.neg_re, Complex.add_re, Complex.re_ofReal_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hplus (sq_nonneg (x+y)),
    mul_le_mul_of_nonneg_left hminus (sq_nonneg (x-y))]

private theorem differentiable_dominated_disk {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : ℂ → X → ℂ) (hm : ∀ z, Measurable (K z))
    (hh : ∀ x, DifferentiableOn ℂ (fun z => K z x) (Metric.ball 0 1))
    (hmajor : ∀ R : ℝ, 0 ≤ R → R < 1 →
      ∃ B : X → ℝ, Integrable B μ ∧ ∀ z : ℂ, ‖z‖ ≤ R → ∀ x, ‖K z x‖ ≤ B x) :
    DifferentiableOn ℂ (fun z => ∫ x, K z x ∂μ) (Metric.ball 0 1) := by
  intro z₀ hz₀
  have hz : ‖z₀‖ < 1 := by simpa using hz₀
  let e := (1-‖z₀‖)/4
  have he : 0 < e := by dsimp [e]; linarith
  let R := ‖z₀‖ + 2*e
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : R < 1 := by dsimp [R,e]; linarith
  obtain ⟨B, hB, hb⟩ := hmajor R hR hR1
  have hKint : Integrable (K z₀) μ :=
    hB.mono' (hm _).aestronglyMeasurable (Filter.Eventually.of_forall (hb _ (by dsimp [R]; linarith)))
  let K' (z : ℂ) (x : X) := deriv (fun w => K w x) z
  have hmeas : AEStronglyMeasurable (K' z₀) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] z₀)
      (f := fun w x => slope (fun z => K z x) z₀ w)
    · intro w
      simp only [slope_def_field]
      exact ((hm w).sub (hm z₀) |>.div_const _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x =>
        hasDerivAt_iff_tendsto_slope.mp ((hh x).differentiableAt (Metric.isOpen_ball.mem_nhds hz₀)).hasDerivAt
  have hrad {z w : ℂ} (hz' : z ∈ Metric.ball z₀ e) (hw : w ∈ Metric.closedBall z e) :
      ‖w‖ ≤ R := by
    have h₁ : dist z z₀ < e := hz'
    have h₂ : dist w z ≤ e := hw
    have ht := dist_triangle w z z₀
    have ht' := dist_triangle w z₀ 0
    simp only [dist_zero_right] at ht'
    dsimp [R]
    linarith
  have hsub {z : ℂ} (hz' : z ∈ Metric.ball z₀ e) :
      Metric.closedBall z e ⊆ Metric.ball 0 1 := by
    intro w hw
    simpa using (hrad hz' hw).trans_lt hR1
  have hder (x : X) (z : ℂ) (hz' : z ∈ Metric.ball z₀ e) : ‖K' z x‖ ≤ B x / e :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le he ((hh x).diffContOnCl_ball (hsub hz'))
      (fun w hw => hb w (hrad hz' (Metric.sphere_subset_closedBall hw)) x)
  have hh' (x : X) (z : ℂ) (hz' : z ∈ Metric.ball z₀ e) : HasDerivAt (fun w => K w x) (K' z x) z :=
    ((hh x).differentiableAt (Metric.isOpen_ball.mem_nhds
      (hsub hz' (Metric.mem_closedBall_self he.le)))).hasDerivAt
  have hdi := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := K) (F' := K')
    (Metric.ball_mem_nhds z₀ he) (Filter.Eventually.of_forall fun w => (hm w).aestronglyMeasurable)
    hKint hmeas (Filter.Eventually.of_forall hder) (hB.div_const _) (Filter.Eventually.of_forall hh')
  exact hdi.2.differentiableAt.differentiableWithinAt

private theorem limiting_holomorphic {k : ℕ} (S : LimitingScheme k) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      ∀ t : ℝ, |t| < 1 → F t = (S.corr t : ℂ) := by
  classical
  choose φ hφ hb hreal using fun i => allowable_extension (S.ρ_allowable i)
  let X := Fin k → ℝ
  let K (z : ℂ) (p : X × X) : ℂ := ((S.f p.1 * S.g p.2 : ℝ) : ℂ) *
      ∏ i, gaussKernel (φ i z) (p.1 i) (p.2 i)
  have hm (z : ℂ) : Measurable (K z) := by
    dsimp only [K]
    apply (Complex.measurable_ofReal.comp ((S.measurable_f.comp measurable_fst).mul
      (S.measurable_g.comp measurable_snd))).mul
    apply Finset.measurable_prod
    intro i _
    unfold gaussKernel
    fun_prop
  have hh (p : X × X) : DifferentiableOn ℂ (fun z => K z p) (Metric.ball 0 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    have hd (i : Fin k) :
        DifferentiableAt ℂ (fun y => gaussKernel (φ i y) (p.1 i) (p.2 i)) z :=
      (kernel_diff ((hb i z hz').trans_lt hz') _ _).comp z
        ((hφ i).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
    exact DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hmajor (R : ℝ) (hR : 0 ≤ R) (hR1 : R < 1) :
      ∃ B : X × X → ℝ, Integrable B volume ∧
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ p, ‖K z p‖ ≤ B p := by
    obtain ⟨C, a, hC, ha, hk⟩ := kernel_bound R hR hR1
    let q (x : X) := ∏ i, Real.exp (-a*(x i)^2)
    have hi : Integrable q (volume : Measure X) :=
      Integrable.fintype_prod fun _ : Fin k => integrable_exp_neg_mul_sq ha
    refine ⟨fun p => C^k * (q p.1 * q p.2), (hi.mul_prod hi).const_mul _, ?_⟩
    intro z hz p
    have hp : ‖((S.f p.1 * S.g p.2 : ℝ) : ℂ)‖ = 1 := by
      rcases S.f_sign p.1 with h|h <;> rcases S.g_sign p.2 with h'|h' <;> simp [h,h']
    simp only [K, norm_mul, hp, one_mul, norm_prod]
    calc
      _ ≤ ∏ i : Fin k, C*(Real.exp (-a*(p.1 i)^2)*Real.exp (-a*(p.2 i)^2)) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
          hk _ ((hb i z (hz.trans_lt hR1)).trans hz) _ _
      _ = _ := by simp [q, Finset.prod_mul_distrib]
  refine ⟨fun z => ((Real.pi/2 : ℝ) : ℂ) * ∫ p, K z p,
    (differentiable_dominated_disk K hm hh hmajor).const_mul _, ?_⟩
  intro t ht
  have htc : ‖(t:ℂ)‖ < 1 := by simpa [Real.norm_eq_abs] using ht
  have hρ (i : Fin k) : |S.ρ i t| < 1 := by
    have h := hb i (t:ℂ) htc
    rw [hreal i t ht] at h
    simpa [Real.norm_eq_abs] using h.trans_lt htc
  obtain ⟨B, hB, hdom⟩ := hmajor ‖(t:ℂ)‖ (norm_nonneg _) htc
  have hI : Integrable (K (t:ℂ)) volume :=
    hB.mono' (hm _).aestronglyMeasurable (Filter.Eventually.of_forall (hdom _ le_rfl))
  change ((Real.pi/2 : ℝ) : ℂ) * (∫ p, K (t:ℂ) p) = _
  rw [Measure.volume_eq_prod, integral_prod _ (show Integrable _ (volume.prod volume) from hI)]
  change ((Real.pi/2 : ℝ) : ℂ) * _ = ((Real.pi/2 * ∫ x : X, ∫ y : X, _) : ℝ)
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  simp only [K, fun i => hreal i t ht, fun i => kernel_real (hρ i), gaussianPairDensity, Fin.prod_univ_one]
  push_cast
  rfl

private theorem matrix_gap {k : ℕ} (S : LimitingScheme k) (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hb1 : 0 < b 1) (hs : Summable fun n => |b n|)
    (hseries : ∀ t : ℝ, |t| < 1 → S.corr t = ∑' n, b n * t^n)
    (γ : ℝ) (hγ : 0 < γ) (hgap : γ + (∑' m, |b (m+2)|) < b 1)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    sdpValue A ≤ Real.pi/(2*γ) * optValue A := by
  classical
  let D := ∑' p : ℕ, |b (p+2)|
  let C := Real.pi/2 * optValue A
  have htail : HasSum (fun p : ℕ => |b (p+2)|) D :=
    ((summable_nat_add_iff 2).2 hs).hasSum
  have hmain : sdpValue A ≤ (C + D*sdpValue A) / b 1 := by
    apply csSup_le (sdpSet_nonempty A)
    rintro _ ⟨d, u, v, hu, hv, rfl⟩
    let t (i : Fin m) (j : Fin n) := inner ℝ (u i) (v j)
    let W (p : ℕ) := ∑ i, ∑ j, A i j * (t i j)^p
    have ht (i j) : |t i j| ≤ 1 := by
      simpa [t, hu i, hv j] using abs_real_inner_le_norm (u i) (v j)
    have hW (p : ℕ) : |W p| ≤ sdpValue A := gram_power_objective A u v hu hv p
    have hrbound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : b 1 * (r * W 1) ≤ C + D*sdpValue A := by
      have hrt (i j) : |r*t i j| < 1 := by
        rw [abs_mul, abs_of_pos hr]
        exact (mul_le_of_le_one_right hr.le (ht i j)).trans_lt hr1
      have hrnd : (∑ i, ∑ j, A i j * S.corr (r*t i j)) ≤ C := by
        obtain ⟨_, U, V, hU, hV, hUV⟩ := gram_scale u v hu hv r hr.le hr1.le
        have hs' (i j) : |inner ℝ (U i) (V j)| < 1 := by rw [hUV]; exact hrt i j
        simpa only [hUV, t, C] using limitingScheme_rounding_inequality A S U V hU hV hs'
      have hp (i j) : HasSum (fun p : ℕ => b p * (r*t i j)^p) (S.corr (r*t i j)) := by
        rw [hseries _ (hrt i j)]
        apply Summable.hasSum
        apply Summable.of_norm_bounded (g := fun p => |b p|) hs
        intro p
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (pow_le_one₀ (abs_nonneg _) (hrt i j).le)
      have hinner (i : Fin m) : HasSum (fun p => ∑ j, A i j * (b p * (r*t i j)^p))
          (∑ j, A i j * S.corr (r*t i j)) := by
        simpa only [Finset.sum_apply] using
          (hasSum_sum (s := Finset.univ) fun (j : Fin n) _ => (hp i j).mul_left (A i j))
      have htots : HasSum (fun p => ∑ i, ∑ j, A i j * (b p * (r*t i j)^p))
          (∑ i, ∑ j, A i j * S.corr (r*t i j)) := by
        simpa only [Finset.sum_apply] using
          (hasSum_sum (s := Finset.univ) fun (i : Fin m) _ => hinner i)
      have hobj : HasSum (fun p => b p * r^p * W p) (∑ i, ∑ j, A i j * S.corr (r*t i j)) := by
        apply htots.congr_fun
        intro p
        simp only [W, Finset.mul_sum, mul_pow]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hrest : |∑' p : ℕ, b (p+2) * r^(p+2) * W (p+2)| ≤ D*sdpValue A := by
        rw [← Real.norm_eq_abs]
        apply tsum_of_norm_bounded (htail.mul_right (sdpValue A))
        intro p
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
        exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _)
          (pow_le_one₀ hr.le hr1.le)) (hW _) (abs_nonneg _) (abs_nonneg _)
      have heq := (hobj.summable.sum_add_tsum_nat_add 2).trans hobj.tsum_eq
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hb0, zero_mul, pow_one] at heq
      linarith only [heq, hrnd, (abs_le.mp hrest).1]
    have hlim : Tendsto (fun r : ℝ => b 1 * (r * W 1)) (𝓝[<]1) (𝓝 (b 1 * W 1)) := by
      simpa only [one_mul] using
        (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds |>.mul_const (W 1)) :
          Tendsto (fun r : ℝ => b 1 * (r * W 1)) (𝓝[<]1) (𝓝 (b 1 * (1 * W 1))))
    have hbound : b 1 * W 1 ≤ C + D*sdpValue A := by
      apply le_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin (s := Set.Iio (1:ℝ)),
        mem_nhdsWithin_of_mem_nhds (eventually_gt_nhds (zero_lt_one : (0:ℝ)<1))] with r hr1 hr
      exact hrbound r hr hr1
    apply (le_div_iff₀ hb1).2
    simpa only [W, t, pow_one, mul_comm (b 1)] using hbound
  have hnonneg : 0 ≤ sdpValue A := by
    obtain ⟨z, d, u, v, hu, hv, hz⟩ := sdpSet_nonempty A
    exact (abs_nonneg _).trans (gram_power_objective A u v hu hv 1)
  have hmul := (le_div_iff₀ hb1).1 hmain
  have hgap' : γ + D ≤ b 1 := hgap.le
  have hfin : γ * sdpValue A ≤ Real.pi/2 * optValue A := by
    dsimp only [C] at hmul
    nlinarith only [hmul, mul_le_mul_of_nonneg_right hgap' hnonneg]
  calc
    sdpValue A ≤ (Real.pi/2 * optValue A)/γ := (le_div_iff₀ hγ).2 (by linarith only [hfin])
    _ = _ := by ring

end DirectSchemeBound

open DirectSchemeBound

theorem solution {k : ℕ} (S : LimitingScheme k)
    (γ : ℝ) (hγ : 0 < γ)
    (hsum : Summable (fun j : ℕ => |taylorCoeff (2*j+3) S.corr|))
    (hgap : γ + (∑' j : ℕ, |taylorCoeff (2*j+3) S.corr|) < taylorCoeff 1 S.corr) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2*γ) := by
  let b (n : ℕ) := taylorCoeff n S.corr
  have hodd : (fun t : ℝ => S.corr (-t)) =ᶠ[𝓝 0] (fun t => -S.corr t) :=
    (unit_near (by norm_num : |(0 : ℝ)| < 1)).mono fun _ ht => normalized_corr_odd S ht
  have h0 : S.corr 0 = 0 := by
    have h := hodd.eq_of_nhds
    change S.corr (-0) = -S.corr 0 at h
    rw [neg_zero] at h
    linarith
  have heven (n : ℕ) (hn : Even n) : b n = 0 := by
    have h := hodd.iteratedDeriv_eq n
    rw [iteratedDeriv_comp_neg, neg_zero, hn.neg_one_pow, one_smul, iteratedDeriv_fun_neg] at h
    have he : iteratedDeriv n S.corr 0 = 0 := by linarith
    simp [b, taylorCoeff, he]
  have htail : HasSum (fun n : ℕ => |b (n+2)|) (∑' j : ℕ, |b (2*j+3)|) := by
    have he : HasSum (fun j : ℕ => |b (2*j+2)|) 0 := by
      have hz (j : ℕ) : b (2*j+2) = 0 := heven _ ⟨j+1, by omega⟩
      simp [hz]
    have ho : HasSum (fun j : ℕ => |b ((2*j+1)+2)|) (∑' j : ℕ, |b (2*j+3)|) := by
      simpa only [Nat.add_assoc] using hsum.hasSum
    simpa only [zero_add] using (HasSum.even_add_odd (f := fun n => |b (n+2)|) he ho)
  have hall : Summable (fun n : ℕ => |b n|) := (summable_nat_add_iff 2).1 htail.summable
  have hgap' : γ + (∑' n : ℕ, |b (n+2)|) < b 1 := by rwa [htail.tsum_eq]
  have hb : 0 < b 1 := lt_trans (add_pos_of_pos_of_nonneg hγ (tsum_nonneg fun _ => abs_nonneg _)) hgap'
  obtain ⟨F, hF, hreal⟩ := limiting_holomorphic S
  obtain ⟨_, hseries⟩ := real_taylor_on_disk S.corr F hF hreal
  apply csInf_le
  · exact ⟨1, fun K hK => one_le_of_isGrothendieckBound hK⟩
  · intro m n A
    exact matrix_gap S b (heven 0 (by decide)) hb hall hseries γ hγ hgap' A
