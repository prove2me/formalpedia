-- Prove2me | solution 1 for GrothendieckLB.Supplement.limitingScheme_rounding_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T17:45:35.81585+00:00
-- url     : https://prove2.me/submissions/41cd99ec-4848-4b1c-819f-7eab1a5a700a

import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open GrothendieckLB.Supplement GrothendieckConstant MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace LimitingKrivineRounding

/- The characteristic-function proof of projectionPair_law below is from the
   public Prove2Me submission c85a8429-0642-4db2-8539-0cf94b08f926
   (Apache 2.0). The bound on optSet is from Nickrobbins95, submission
   f260128e-39ad-469d-96d6-7bf32941862c, through the same source. -/
lemma dual_pair (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl

lemma charFunDual_standard_real (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (- (L 1 : ℂ) ^ 2 / 2) := by
  have h : charFunDual (gaussianReal 0 1) L = charFun (gaussianReal 0 1) (L 1) := by
    rw [charFunDual_apply, charFun_apply_real]
    congr 1
    ext x
    have hx : L x = x * L 1 := by
      simpa using L.map_smul x (1 : ℝ)
    rw [hx]
    push_cast
    ring_nf
  rw [h, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
    one_mul, zero_sub]
  congr 1
  ring

noncomputable def projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ u).prod (innerSL ℝ v)

noncomputable def planePair (θ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (Real.cos θ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Real.sin θ • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma dual_projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (L : StrongDual ℝ (ℝ × ℝ)) :
    L.comp (projectionPair u v) = innerSL ℝ (L (1, 0) • u + L (0, 1) • v) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply, projectionPair, ContinuousLinearMap.prod_apply,
    innerSL_apply_apply, inner_add_left, real_inner_smul_left]
  rw [dual_pair]
  ring

lemma norm_combination_sq {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (t s : ℝ) :
    ‖t • u + s • v‖ ^ 2 = t ^ 2 + s ^ 2 + 2 * t * s * inner ℝ u v := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hv, real_inner_comm v u]
  ring

/-- Equality of the joint projection laws, including singular Gram matrices. -/
theorem projectionPair_law {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : Real.cos θ = inner ℝ u v) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (projectionPair u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (planePair θ) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_map, dual_projectionPair, charFunDual_stdGaussian,
    innerSL_apply_norm, charFunDual_prod, charFunDual_standard_real,
    charFunDual_standard_real, ← Complex.exp_add]
  have hleft : (L.comp (planePair θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1 =
      L (1, 0) + Real.cos θ * L (0, 1) := by
    change L (1, Real.cos θ * 1 + Real.sin θ * 0) = _
    rw [dual_pair]
    simp
  have hright : (L.comp (planePair θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1 =
      Real.sin θ * L (0, 1) := by
    change L (0, Real.cos θ * 0 + Real.sin θ * 1) = _
    rw [dual_pair]
    simp
  rw [hleft, hright]
  have hnorm := norm_combination_sq u v hu hv (L (1, 0)) (L (0, 1))
  have hgram : ‖L (1, 0) • u + L (0, 1) • v‖ ^ 2 =
      (L (1, 0) + Real.cos θ * L (0, 1)) ^ 2 + (Real.sin θ * L (0, 1)) ^ 2 := by
    rw [hnorm, ← hθ]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  congr 1
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hgram
  push_cast at hc ⊢
  linear_combination -hc / 2

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



private theorem pi_gaussian_density {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  have hi : Integrable (fun x : Fin k → ℝ => ∏ i, gaussianPDFReal (m i) (v i) (x i))
      (Measure.pi fun i => (volume : Measure ℝ).restrict (s i)) :=
    Integrable.fintype_prod fun i => (integrable_gaussianPDFReal (m i) (v i)).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x =>
    Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg (m i) (v i) (x i)),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ =>
      integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _)]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_apply_eq_integral (m i) (hv i) (s i)).symm

private theorem integral_pi_gaussian {k : ℕ} (m : Fin k → ℝ) (v : Fin k → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (f : (Fin k → ℝ) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun i => gaussianReal (m i) (v i))) =
      ∫ x, (∏ i, gaussianPDFReal (m i) (v i) (x i)) * f x := by
  rw [pi_gaussian_density m v hv, integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _)]
    rfl
  · exact Measurable.ennreal_ofReal <| Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal _ _).comp (measurable_pi_apply i)
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem pair_factor (t s : ℝ) (hs : 0 < s) (hsq : s^2 = 1-t^2) (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal (t*x) (NNReal.mk (s^2) (sq_nonneg _)) y =
      (1 / (2 * Real.pi * Real.sqrt (1-t^2))) *
        Real.exp (-(x^2 - 2*t*x*y + y^2)/(2*(1-t^2))) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hsp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hp
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, NNReal.coe_mk]
  rw [← hsq, Real.sqrt_mul hp.le, Real.sqrt_sq hs.le, mul_mul_mul_comm, ← Real.exp_add]
  congr 1
  · field_simp [hs.ne', hsp.ne', Real.pi_ne_zero] <;> nlinarith [Real.sq_sqrt hp.le]
  · congr 1
    field_simp [hs.ne'] <;> rw [hsq] <;> ring

private theorem affine_pi_law {k : ℕ} (t s : Fin k → ℝ) (x : Fin k → ℝ) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).map
        (fun y : Fin k → ℝ => fun i => t i * x i + s i * y i) =
      Measure.pi (fun i => gaussianReal (t i * x i) (NNReal.mk ((s i)^2) (sq_nonneg _))) := by
  have hmap (i : Fin k) :
      (gaussianReal 0 1).map (fun y : ℝ => t i*x i + s i*y) =
        gaussianReal (t i*x i) (NNReal.mk ((s i)^2) (sq_nonneg _)) := by
    change (gaussianReal 0 1).map ((fun w : ℝ => t i*x i + w) ∘ (fun y => s i*y)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp
  rw [Measure.pi_map_pi (f := fun i (y : ℝ) => t i*x i + s i*y) (fun _ => by fun_prop)]
  simp only [hmap]

private theorem sign_product_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfs : ∀ x, f x = 1 ∨ f x = -1) (hgs : ∀ x, g x = 1 ∨ g x = -1) :
    Integrable (fun x => f x * g x) μ := by
  apply (integrable_const (1:ℝ)).mono' (hf.mul hg).aestronglyMeasurable
  filter_upwards with x
  rcases hfs x with h | h <;> rcases hgs x with h' | h' <;> simp [h, h']

private theorem projection_correlation {d k : ℕ} (S : KrivineScheme k)
    (u v : Fin k → EuclideanSpace ℝ (Fin d)) (hu : ∀ l, ‖u l‖ = 1) (hv : ∀ l, ‖v l‖ = 1)
    (ht : ∀ l, |inner ℝ (u l) (v l)| < 1) :
    multiCorr S.f S.g (fun l => inner ℝ (u l) (v l)) = (Real.pi / 2) *
      ∫ ω : Fin k → EuclideanSpace ℝ (Fin d),
        S.f (fun l => inner ℝ (u l) (ω l)) * S.g (fun l => inner ℝ (v l) (ω l))
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  let t (l : Fin k) := inner ℝ (u l) (v l)
  let θ (l : Fin k) := Real.arccos (t l)
  let s (l : Fin k) := Real.sqrt (1 - (t l)^2)
  let ν := gaussianReal 0 1
  let P := Measure.pi fun _ : Fin k => ν
  haveI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  haveI : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin k => ν))
  have hlo (l) : -1 < t l := (abs_lt.mp (ht l)).1
  have hhi (l) : t l < 1 := (abs_lt.mp (ht l)).2
  have hr (l) : 0 < 1-(t l)^2 := by
    nlinarith [mul_pos (sub_pos.mpr (hhi l)) (show 0 < 1+t l by linarith [hlo l])]
  have hs (l) : 0 < s l := Real.sqrt_pos.mpr (hr l)
  have hsq (l) : (s l)^2 = 1-(t l)^2 := Real.sq_sqrt (hr l).le
  have hcos (l) : Real.cos (θ l) = t l := Real.cos_arccos (hlo l).le (hhi l).le
  have hsin (l) : Real.sin (θ l) = s l := Real.sin_arccos (t l)
  let Φ (z : Fin k → ℝ × ℝ) := S.f (fun l => (z l).1) * S.g (fun l => (z l).2)
  have hΦ : Measurable Φ := by
    exact (S.measurable_f.comp (measurable_pi_lambda _ fun l => (measurable_pi_apply l).fst)).mul
      (S.measurable_g.comp (measurable_pi_lambda _ fun l => (measurable_pi_apply l).snd))
  let L (ω : Fin k → EuclideanSpace ℝ (Fin d)) (l : Fin k) := projectionPair (u l) (v l) (ω l)
  let T (z : Fin k → ℝ × ℝ) (l : Fin k) := planePair (θ l) (z l)
  have hL : Measurable L := measurable_pi_lambda _ fun l =>
    (projectionPair (u l) (v l)).continuous.measurable.comp (measurable_pi_apply l)
  have hT : Measurable T := measurable_pi_lambda _ fun l =>
    (planePair (θ l)).continuous.measurable.comp (measurable_pi_apply l)
  have hlaw : (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))).map L =
      (Measure.pi fun _ : Fin k => ν.prod ν).map T := by
    dsimp only [L, T]
    rw [Measure.pi_map_pi (f := fun l => projectionPair (u l) (v l)) (fun l =>
        (projectionPair (u l) (v l)).continuous.measurable.aemeasurable),
      Measure.pi_map_pi (f := fun l => planePair (θ l)) (fun l =>
        (planePair (θ l)).continuous.measurable.aemeasurable)]
    congr 1
    funext l
    exact projectionPair_law (u l) (v l) (hu l) (hv l) (θ l) (hcos l)
  have htransport :
      (∫ ω, Φ (L ω) ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d)))) =
      ∫ z, Φ (T z) ∂Measure.pi (fun _ => ν.prod ν) := by
    rw [← integral_map hL.aemeasurable hΦ.aestronglyMeasurable,
      ← integral_map hT.aemeasurable hΦ.aestronglyMeasurable, hlaw]
  let J (p : (Fin k → ℝ) × (Fin k → ℝ)) := S.f p.1 * S.g (fun l => t l*p.1 l + s l*p.2 l)
  have hJ : Integrable J (P.prod P) :=
    sign_product_integrable _ _ _ (S.measurable_f.comp measurable_fst)
      (S.measurable_g.comp (by fun_prop)) (fun x => S.f_sign _) (fun x => S.g_sign _)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)
  have hcoord (z : Fin k → ℝ × ℝ) : Φ (T z) = J (e z) := by
    change S.f _ * S.g (fun l => Real.cos (θ l) * (z l).1 + Real.sin (θ l) * (z l).2) =
      S.f _ * S.g (fun l => t l * (z l).1 + s l * (z l).2)
    simp only [hcos, hsin]
    rfl
  have hsplit : (∫ z, Φ (T z) ∂Measure.pi (fun _ => ν.prod ν)) =
      ∫ x, ∫ y, S.f x * S.g (fun l => t l*x l + s l*y l) ∂P ∂P := by
    simp_rw [hcoord]
    rw [(measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k) (fun _ => ν) (fun _ => ν)).integral_comp' J,
      integral_prod _ hJ]
  let V (l : Fin k) : ℝ≥0 := NNReal.mk ((s l)^2) (sq_nonneg _)
  have hV (l) : V l ≠ 0 := by
    intro h
    have h' := congrArg ((↑) : ℝ≥0 → ℝ) h
    change (s l)^2 = 0 at h'
    nlinarith [sq_pos_of_pos (hs l)]
  have hinner (x : Fin k → ℝ) :
      (∫ y, S.f x * S.g (fun l => t l*x l + s l*y l) ∂P) =
        ∫ y, (∏ l, gaussianPDFReal (t l*x l) (V l) (y l)) * (S.f x * S.g y) := by
    let A (y : Fin k → ℝ) (l : Fin k) := t l*x l + s l*y l
    have hA : Measurable A := by dsimp [A]; fun_prop
    have hj : Measurable (fun y : Fin k → ℝ => S.f x * S.g y) := measurable_const.mul S.measurable_g
    change (∫ y, (fun z => S.f x * S.g z) (A y) ∂P) = _
    rw [← integral_map hA.aemeasurable hj.aestronglyMeasurable]
    rw [show P.map A = Measure.pi (fun l => gaussianReal (t l*x l) (V l)) from affine_pi_law t s x]
    exact integral_pi_gaussian (fun l => t l*x l) V hV _
  change (Real.pi / 2) * _ = (Real.pi / 2) * (∫ ω, Φ (L ω) ∂_)
  congr 1
  rw [htransport, hsplit]
  simp_rw [hinner]
  rw [show P = Measure.pi (fun _ : Fin k => gaussianReal 0 1) from rfl,
    integral_pi_gaussian (fun _ => 0) (fun _ => 1) (fun _ => one_ne_zero)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change S.f x * S.g y * (∏ l, _) =
    (∏ l, gaussianPDFReal 0 1 (x l)) *
      ((∏ l, gaussianPDFReal (t l*x l) (V l) (y l)) * (S.f x * S.g y))
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  simp_rw [show ∀ l : Fin k, gaussianPDFReal 0 1 (x l) * gaussianPDFReal (t l*x l) (V l) (y l) =
      _ from fun l => pair_factor (t l) (s l) (hs l) (hsq l) (x l) (y l)]
  simp only [gaussianPairDensity, Fin.prod_univ_one]
  ring

private theorem coordinate_rounding {m n d k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (S : KrivineScheme k)
    (u : Fin m → Fin k → EuclideanSpace ℝ (Fin d)) (v : Fin n → Fin k → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i l, ‖u i l‖ = 1) (hv : ∀ j l, ‖v j l‖ = 1)
    (hstrict : ∀ i j l, |inner ℝ (u i l) (v j l)| < 1) :
    (∑ i, ∑ j, A i j * multiCorr S.f S.g (fun l => inner ℝ (u i l) (v j l))) ≤
      (Real.pi / 2) * optValue A := by
  let μ := Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))
  haveI : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d))))
  let f (i : Fin m) (ω : Fin k → EuclideanSpace ℝ (Fin d)) := S.f (fun l => inner ℝ (u i l) (ω l))
  let g (j : Fin n) (ω : Fin k → EuclideanSpace ℝ (Fin d)) := S.g (fun l => inner ℝ (v j l) (ω l))
  have hf (i) : Measurable (f i) := S.measurable_f.comp (by fun_prop)
  have hg (j) : Measurable (g j) := S.measurable_g.comp (by fun_prop)
  have hij (i j) : Integrable (fun ω => A i j * (f i ω * g j ω)) μ :=
    (sign_product_integrable μ _ _ (hf i) (hg j)
      (fun _ => S.f_sign _) (fun _ => S.g_sign _)).const_mul _
  have hi (i) : Integrable (fun ω => ∑ j, A i j * (f i ω * g j ω)) μ :=
    integrable_finsetSum _ fun j _ => hij i j
  have hs : Integrable (fun ω => ∑ i, ∑ j, A i j * (f i ω * g j ω)) μ :=
    integrable_finsetSum _ fun i _ => hi i
  have hval (ω) : ∑ i, ∑ j, A i j * (f i ω * g j ω) ≤ optValue A := by
    apply le_csSup (optSet_bdd A)
    exact ⟨fun i => f i ω, fun j => g j ω, fun _ => S.f_sign _, fun _ => S.g_sign _,
      by simp only [mul_assoc]⟩
  have hmean : (∫ ω, ∑ i, ∑ j, A i j * (f i ω * g j ω) ∂μ) ≤ optValue A := by
    simpa using integral_mono hs (integrable_const (optValue A)) hval
  calc
    _ = (Real.pi/2) * (∫ ω, ∑ i, ∑ j, A i j * (f i ω * g j ω) ∂μ) := by
      rw [integral_finsetSum _ fun i _ => hi i, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ fun j _ => hij i j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [projection_correlation S (u i) (v j) (hu i) (hv j) (hstrict i j),
        integral_const_mul]
      change A i j * (Real.pi / 2 * _) = Real.pi / 2 * (A i j * _)
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (by positivity)

open scoped Matrix
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


lemma psd_limit {M : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hM : ∀ k, (M k).PosSemidef) (hlim : ∀ i j, Tendsto (fun k => M k i j) atTop (nhds (B i j))) :
    B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact tendsto_nhds_unique (hlim j i) ((hlim i j).congr (fun k => by
      have h := congrFun (congrFun (hM k).isHermitian i) j
      simpa using h.symm))
  · intro x
    have hlimq : Tendsto (fun k => star x ⬝ᵥ (M k *ᵥ x)) atTop
        (nhds (star x ⬝ᵥ (B *ᵥ x))) := by
      simp only [dotProduct, mulVec]
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul_const (x j))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun k => (hM k).dotProduct_mulVec_nonneg x)


end Matrices
private theorem allowable_contracts {ρ : ℝ → ℝ} (hρ : IsAllowableCorr ρ) {x : ℝ} (hx : |x| < 1) :
    |ρ x| ≤ |x| := by
  obtain ⟨c, he, hs, hc, heq⟩ := hρ
  rw [heq x hx, ← Real.norm_eq_abs]
  apply le_trans (tsum_of_norm_bounded (hs.hasSum.mul_right |x|) ?_)
    (mul_le_of_le_one_left (abs_nonneg _) hc)
  intro p
  cases p with
  | zero => simp [he 0 (by decide)]
  | succ p =>
    rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_succ]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx.le)

private theorem realize_allowable {m n d : ℕ} (ρ : ℝ → ℝ) (hρ : IsAllowableCorr ρ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hstrict : ∀ i j, |inner ℝ (u i) (v j)| < 1) :
    ∃ (U : Fin m → EuclideanSpace ℝ (Fin (Fintype.card (Fin m ⊕ Fin n))))
      (V : Fin n → EuclideanSpace ℝ (Fin (Fintype.card (Fin m ⊕ Fin n)))),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
      (∀ i j, inner ℝ (U i) (V j) = ρ (inner ℝ (u i) (v j))) := by
  classical
  obtain ⟨c, _, hc, hmass, hrep⟩ := hρ
  let w : (Fin m ⊕ Fin n) → EuclideanSpace ℝ (Fin d) := Sum.elim u v
  let G := Matrix.gram ℝ w
  have hw (i : Fin m ⊕ Fin n) : ‖w i‖ = 1 := by cases i <;> simp [w,hu,hv]
  have hd (i : Fin m ⊕ Fin n) : G i i = 1 := by simp [G, Matrix.gram_apply, hw]
  have hb (i j : Fin m ⊕ Fin n) : |G i j| ≤ 1 := by
    simpa [G, Matrix.gram_apply, hw] using abs_real_inner_le_norm (w i) (w j)
  let sign (p : ℕ) : (Fin m ⊕ Fin n) → ℝ := Sum.elim (fun _ => 1) (fun _ => if c p < 0 then -1 else 1)
  have habs (p : ℕ) (i : Fin m ⊕ Fin n) : |sign p i| = 1 := by
    cases i <;> by_cases h : c p < 0 <;> simp [sign, h]
  have hsq (p : ℕ) (i : Fin m ⊕ Fin n) : sign p i * sign p i = 1 := by
    cases i <;> by_cases h : c p < 0 <;> simp [sign, h]
  let L (p : ℕ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
    |c p| • ((fun i j => G i j ^ p : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) ⊙
      Matrix.vecMulVec (sign p) (star (sign p)))
  have hL (p) : (L p).PosSemidef :=
    ((psd_entrywise_pow G (Matrix.posSemidef_gram _ _) p).hadamard
      (Matrix.posSemidef_vecMulVec_self_star _)).smul (abs_nonneg _)
  have hentry (p : ℕ) (i j : Fin m ⊕ Fin n) : L p i j = |c p| * (G i j ^ p * (sign p i * sign p j)) := by
    simp [L, Matrix.hadamard, Matrix.vecMulVec]
  have hsum (i j : Fin m ⊕ Fin n) : Summable fun p => L p i j := by
    apply Summable.of_norm_bounded (g := fun p => |c p|) hc
    intro p
    rw [Real.norm_eq_abs, hentry]
    simp only [abs_mul, abs_abs, habs, abs_pow, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (hb i j))
  let Q : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := fun i j => ∑' p, L p i j
  have hQ : Q.PosSemidef := by
    apply psd_limit (M := fun q => ∑ p ∈ Finset.range q, L p)
    · intro q
      induction q with
      | zero => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ).PosSemidef)
      | succ q ih => simpa only [Finset.sum_range_succ] using ih.add (hL q)
    · intro i j
      simpa only [Matrix.sum_apply] using (hsum i j).hasSum.tendsto_sum_nat
  let B := Q + (1-∑' p, |c p|) • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ)
  have hB : B.PosSemidef := hQ.add (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hmass))
  have hBdiag (i) : B i i = 1 := by
    have hQdiag : Q i i = ∑' p, |c p| := by
      apply tsum_congr
      intro p
      rw [hentry, hd, one_pow, hsq, mul_one, mul_one]
    simp only [B, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      hQdiag, mul_one]
    ring
  obtain ⟨z, hz, hgram⟩ := exists_unit_gram B hB hBdiag
  refine ⟨fun i => z (.inl i), fun j => z (.inr j), fun i => hz _, fun j => hz _, ?_⟩
  intro i j
  rw [hgram, hrep _ (hstrict i j)]
  change Q (.inl i) (.inr j) + (1-∑' p, |c p|) * (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) (.inl i) (.inr j) = _
  have hne : (Sum.inl i : Fin m ⊕ Fin n) ≠ Sum.inr j := Sum.inl_ne_inr
  rw [Matrix.one_apply_ne hne, mul_zero, add_zero]
  apply tsum_congr
  intro p
  rw [hentry]
  change |c p| * ((inner ℝ (u i) (v j)) ^ p * (1 * (if c p < 0 then -1 else 1))) = _
  by_cases h : c p < 0
  · rw [if_pos h, abs_of_neg h]; ring
  · rw [if_neg h, abs_of_nonneg (le_of_not_gt h)]; ring

end LimitingKrivineRounding

open LimitingKrivineRounding

theorem solution {m n d k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (S : LimitingScheme k)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (hstrict : ∀ i j, |inner ℝ (u i) (v j)| < 1) :
    (∑ i, ∑ j, A i j * S.corr (inner ℝ (u i) (v j))) ≤
      (Real.pi / 2) * GrothendieckConstant.optValue A := by
  choose U V hU hV heq using fun l => realize_allowable (S.ρ l) (S.ρ_allowable l) u v hu hv hstrict
  have hstrict' (i j l) : |inner ℝ (U l i) (V l j)| < 1 := by
    rw [heq]
    exact (allowable_contracts (S.ρ_allowable l) (hstrict i j)).trans_lt (hstrict i j)
  have h := coordinate_rounding A S.toKrivineScheme (fun i l => U l i) (fun j l => V l j)
    (fun i l => hU l i) (fun j l => hV l j) hstrict'
  simpa only [LimitingScheme.corr, heq] using h
