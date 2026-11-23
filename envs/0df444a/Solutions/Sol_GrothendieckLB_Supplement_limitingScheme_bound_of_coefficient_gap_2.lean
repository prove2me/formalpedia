-- Prove2me | solution 2 for GrothendieckLB.Supplement.limitingScheme_bound_of_coefficient_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:29:17.807865+00:00
-- url     : https://prove2.me/submissions/da602b08-6685-4aec-b5a1-8781cd612e77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_theorem_3_7
import Theorems.Thm_GrothendieckConstant_krivine_scheme_rounding_inequality
import Definitions.Def_GrothendieckLB_taylorCoeff
import Mathlib.Analysis.Complex.TaylorSeries

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement Filter MeasureTheory
open scoped Topology Matrix

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

private theorem limiting_rounding {k m n d : ℕ} (S : LimitingScheme k)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (ht : ∀ i j, |inner ℝ (u i) (v j)| < 1) :
    (∑ i, ∑ j, A i j * S.corr (inner ℝ (u i) (v j))) ≤ Real.pi/2 * optValue A := by
  obtain ⟨F, _, hreal, D, T, FN, _, hFN, hconv⟩ := theorem_3_7 S
  have hp (t : ℝ) (ht : |t| < 1) :
      Tendsto (fun N => correlationFunction (T N) t) atTop (𝓝 (S.corr t)) := by
    have hm : (t : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, Real.norm_eq_abs] using ht
    have h := Complex.continuous_re.continuousAt.tendsto.comp (hconv.tendsto_at hm)
    simpa only [Function.comp_def, hreal t ht, fun N => (hFN N).2 t ht, Complex.ofReal_re] using h
  apply le_of_tendsto (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (hp _ (ht i j)).const_mul (A i j))
  exact Filter.Eventually.of_forall fun N => krivine_scheme_rounding_inequality A (T N) u v hu hv ht

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
        simpa only [hUV, t, C] using limiting_rounding S A U V hU hV hs'
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
  obtain ⟨F, hF, hreal, _⟩ := theorem_3_7 S
  obtain ⟨_, hseries⟩ := real_taylor_on_disk S.corr F hF hreal
  apply csInf_le
  · exact ⟨1, fun K hK => one_le_of_isGrothendieckBound hK⟩
  · intro m n A
    exact matrix_gap S b (heven 0 (by decide)) hb hall hseries γ hγ hgap' A
