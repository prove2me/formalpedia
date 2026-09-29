-- Prove2me | solution 1 for LesHouchesWidth.conditional_gaussian_next_layer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:01:40.120135+00:00
-- url     : https://prove2.me/submissions/c3fd91ae-8337-45dd-bcf9-b21cdb37b465

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

/-! Supporting lemmas (Gaussian network layer calculus; checked). -/

set_option autoImplicit false

namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory

section gaussMoments

lemma gauss_mom2 (v : NNReal) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at hv
  exact hv

lemma hasDerivAt_expq (c t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) (c * t * Real.exp (c * t ^ 2 / 2)) t := by
  have := (((hasDerivAt_pow 2 t).const_mul c).div_const 2).exp
  convert this using 1; push_cast; ring

lemma gauss_mom4 (v : NNReal) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
    simp [integrableExpSet_id_gaussianReal]
  have h := iteratedDeriv_mgf_zero h0 4
  rw [mgf_id_gaussianReal] at h
  set c : ℝ := (v : ℝ) with hc
  have e : (fun t : ℝ => Real.exp (0 * t + c * t ^ 2 / 2)) = fun t => Real.exp (c * t ^ 2 / 2) := by
    funext t; simp
  rw [e] at h
  have d1 : deriv (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) = fun t => c * t * Real.exp (c * t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_expq c t).deriv
  have d2 : deriv (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2)) =
      fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2))
        ((c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) t := by
      have := ((hasDerivAt_id t).const_mul c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, mul_one]; ring)
    exact hd.deriv
  have d3 : deriv (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by push_cast; ring)
    exact hd.deriv
  have d4 : deriv (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_id t).const_mul (3 * c ^ 2)).add
        ((hasDerivAt_pow 3 t).const_mul (c ^ 3))).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, Pi.add_apply]; push_cast; ring)
    exact hd.deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, d1, d2, d3, d4] at h
  rw [show (∫ x, x ^ 4 ∂(gaussianReal 0 v)) = ∫ x, (id ^ 4) x ∂(gaussianReal 0 v) from rfl, ← h]
  simp

end gaussMoments

/-- polynomially bounded measurable functions. -/
def PB (f : ℝ → ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∃ k : ℕ, ∀ t, |f t| ≤ C * (1 + |t|) ^ k

section split

variable {n : ℕ → ℕ} {L : ℕ}

/-- the layer a parameter belongs to (`ℓ` for `b^{(ℓ+1)}` and `W^{(ℓ+1)}`). -/
def layerOf : ParamIndex n L → ℕ
  | .inl a => a.1.val
  | .inr a => a.1.val

/-- the activation fed into layer `m + 1`. -/
noncomputable def act (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n m)) : ℝ :=
  if m = 0 then mlpZ Cb CW σ θ x m j else σ (mlpZ Cb CW σ θ x m j)

lemma mlpZ_succ (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (i : Fin (n (m + 1))) :
    mlpZ Cb CW σ θ x (m + 1) i = mlpBias Cb θ m i + ∑ j, mlpWeight CW θ m i j * act Cb CW σ θ x m j :=
  rfl

lemma mlpZ_congr (Cb CW : ℝ) (σ : ℝ → ℝ) {θ θ' : Params n L} (x : Fin (n 0) → ℝ) :
    ∀ m : ℕ, (∀ a : ParamIndex n L, layerOf a < m → θ a = θ' a) →
      mlpZ Cb CW σ θ x m = mlpZ Cb CW σ θ' x m
  | 0, _ => rfl
  | m + 1, h => by
    have ih := mlpZ_congr Cb CW σ x m (fun a ha => h a (by omega))
    funext i
    rw [mlpZ_succ, mlpZ_succ]
    have hb : mlpBias Cb θ m i = mlpBias Cb θ' m i := by
      unfold mlpBias; split_ifs with hl
      · rw [h _ (by simp [layerOf])]
      · rfl
    have hw : ∀ j, mlpWeight CW θ m i j = mlpWeight CW θ' m i j := by
      intro j; unfold mlpWeight; split_ifs with hl
      · rw [h _ (by simp [layerOf])]
      · rfl
    rw [hb]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hw, act, act, ih]

/-- the block of layer-`m` parameters, indexed by (output unit, bias or input unit). -/
def blk (m : ℕ) (hm : m < L + 1) : Fin (n (m + 1)) × Option (Fin (n m)) → ParamIndex n L
  | (i, none) => .inl ⟨⟨m, hm⟩, i⟩
  | (i, some j) => .inr ⟨⟨m, hm⟩, (i, j)⟩

lemma layerOf_blk (m : ℕ) (hm : m < L + 1) (p : Fin (n (m + 1)) × Option (Fin (n m))) :
    layerOf (blk m hm p) = m := by
  rcases p with ⟨i, _ | j⟩ <;> rfl

lemma blk_injective (m : ℕ) (hm : m < L + 1) : Function.Injective (blk (n := n) m hm) := by
  rintro ⟨i, _ | j⟩ ⟨i', _ | j'⟩ h <;> simp_all [blk]

lemma blk_surj (m : ℕ) (hm : m < L + 1) (a : ParamIndex n L) (ha : layerOf a = m) :
    ∃ p, blk m hm p = a := by
  rcases a with ⟨⟨ℓ, hl⟩, i⟩ | ⟨⟨ℓ, hl⟩, i, j⟩
  · simp only [layerOf] at ha; subst ha; exact ⟨(i, none), rfl⟩
  · simp only [layerOf] at ha; subst ha; exact ⟨(i, some j), rfl⟩

/-- `blk` as an equivalence onto the layer-`m` parameters. -/
noncomputable def blkEquiv (m : ℕ) (hm : m < L + 1) :
    Fin (n (m + 1)) × Option (Fin (n m)) ≃ {a : ParamIndex n L // layerOf a = m} :=
  Equiv.ofBijective (fun p => ⟨blk m hm p, layerOf_blk m hm p⟩)
    ⟨fun p q h => blk_injective m hm (congrArg Subtype.val h),
     fun a => by
      obtain ⟨p, hp⟩ := blk_surj m hm a.1 a.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- the full reindexing: layer-`m` block ⊕ everything else. -/
noncomputable def splitEquiv (m : ℕ) (hm : m < L + 1) :
    (Fin (n (m + 1)) × Option (Fin (n m))) ⊕ {a : ParamIndex n L // ¬ layerOf a = m} ≃
      ParamIndex n L :=
  (Equiv.sumCongr (blkEquiv m hm) (Equiv.refl _)).trans (Equiv.sumCompl _)

/-- measurable reindexing `Params ≃ (layer-m block, curried) × (the rest)`. -/
noncomputable def splitME (m : ℕ) (hm : m < L + 1) :
    Params n L ≃ᵐ (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
      ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (splitEquiv m hm)).symm.trans
    ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.curry _ _ ℝ) (MeasurableEquiv.refl _)))

lemma splitME_apply (m : ℕ) (hm : m < L + 1) (θ : Params n L) :
    splitME m hm θ = (fun i q => θ (blk m hm (i, q)), fun b => θ b.1) := by
  ext i q <;> rfl

lemma mp_curry {A B : Type*} [Fintype A] [Fintype B] (g : Measure ℝ) [IsProbabilityMeasure g] :
    MeasurePreserving (MeasurableEquiv.curry A B ℝ) (Measure.pi fun _ : A × B => g)
      (Measure.pi fun _ : A => Measure.pi fun _ : B => g) := by
  refine ⟨(MeasurableEquiv.curry A B ℝ).measurable, ?_⟩
  have := Measure.infinitePi_map_curry (ι := A) (κ := B) (X := ℝ) (fun _ _ => g)
  simp only [Measure.infinitePi_eq_pi] at this
  exact this

lemma measurePreserving_splitME (m : ℕ) (hm : m < L + 1) :
    MeasurePreserving (splitME m hm) (stdGaussianParams n L)
      ((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
        (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : ParamIndex n L => gaussianReal 0 1)
    (splitEquiv m hm)).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin (n (m + 1)) × Option (Fin (n m))) ⊕ {a : ParamIndex n L // ¬ layerOf a = m} =>
      gaussianReal 0 1)
  have h3 := (mp_curry (A := Fin (n (m + 1))) (B := Option (Fin (n m))) (gaussianReal 0 1)).prod
    (MeasurePreserving.id (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} =>
      gaussianReal 0 1))
  exact h3.comp (h2.comp h1)


end split

section growth

lemma PB.const (c : ℝ) : PB (fun _ => c) :=
  ⟨measurable_const, |c|, 0, fun t => by simp⟩

lemma PB.id' : PB (fun t => t) :=
  ⟨measurable_id, 1, 1, fun t => by simp⟩

lemma PB.nonneg_const {f : ℝ → ℝ} {C : ℝ} {k : ℕ} (h : ∀ t, |f t| ≤ C * (1 + |t|) ^ k) : 0 ≤ C :=
  (abs_nonneg _).trans (by simpa using h 0)

lemma PB.mul {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t * g t) := by
  obtain ⟨hfm, C1, k1, h1⟩ := hf
  obtain ⟨hgm, C2, k2, h2⟩ := hg
  refine ⟨hfm.mul hgm, C1 * C2, k1 + k2, fun t => ?_⟩
  rw [abs_mul, pow_add]
  have := PB.nonneg_const h1
  calc |f t| * |g t| ≤ (C1 * (1 + |t|) ^ k1) * (C2 * (1 + |t|) ^ k2) :=
        mul_le_mul (h1 t) (h2 t) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma PB.add {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t + g t) := by
  obtain ⟨hfm, C1, k1, h1⟩ := hf
  obtain ⟨hgm, C2, k2, h2⟩ := hg
  refine ⟨hfm.add hgm, C1 + C2, k1 + k2, fun t => ?_⟩
  have c1 := PB.nonneg_const h1
  have c2 := PB.nonneg_const h2
  have e1 : (1 + |t|) ^ k1 ≤ (1 + |t|) ^ (k1 + k2) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  have e2 : (1 + |t|) ^ k2 ≤ (1 + |t|) ^ (k1 + k2) :=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
  calc |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
    _ ≤ C1 * (1 + |t|) ^ k1 + C2 * (1 + |t|) ^ k2 := add_le_add (h1 t) (h2 t)
    _ ≤ C1 * (1 + |t|) ^ (k1 + k2) + C2 * (1 + |t|) ^ (k1 + k2) := by gcongr
    _ = _ := by ring

lemma PB.const_mul {f : ℝ → ℝ} (hf : PB f) (c : ℝ) : PB (fun t => c * f t) :=
  (PB.const c).mul hf

lemma PB.sub {f g : ℝ → ℝ} (hf : PB f) (hg : PB g) : PB (fun t => f t - g t) := by
  have := hf.add (hg.const_mul (-1))
  refine ⟨by simpa [sub_eq_add_neg] using this.1, ?_⟩
  obtain ⟨_, C, k, h⟩ := this
  exact ⟨C, k, fun t => by simpa [sub_eq_add_neg] using h t⟩

lemma PB.pow {f : ℝ → ℝ} (hf : PB f) : ∀ j : ℕ, PB (fun t => f t ^ j)
  | 0 => by simpa using PB.const 1
  | j + 1 => by simpa [pow_succ] using (PB.pow hf j).mul hf

lemma PB.of_polyBounded {σ : ℝ → ℝ} (hm : Measurable σ) (hp : PolyBounded σ) : PB σ := by
  obtain ⟨C, k, h⟩ := hp
  have hC : 0 ≤ C := by
    have h0 := h 0
    have : 0 ≤ C * (1 + |(0:ℝ)| ^ k) := (abs_nonneg _).trans h0
    have h1 : 0 < 1 + |(0:ℝ)| ^ k := by positivity
    exact nonneg_of_mul_nonneg_left this h1
  refine ⟨hm, 2 * C, k, fun t => ?_⟩
  have a1 : (1 : ℝ) ≤ (1 + |t|) ^ k := one_le_pow₀ (by linarith [abs_nonneg t])
  have a2 : |t| ^ k ≤ (1 + |t|) ^ k := pow_le_pow_left₀ (abs_nonneg t) (by linarith) k
  calc |σ t| ≤ C * (1 + |t| ^ k) := h t
    _ ≤ C * (2 * (1 + |t|) ^ k) := by gcongr; linarith
    _ = _ := by ring

lemma integrable_one_add_abs_pow_gauss (v : NNReal) (k : ℕ) :
    Integrable (fun u : ℝ => (1 + |u|) ^ k) (gaussianReal 0 v) := by
  have hm : MemLp (id : ℝ → ℝ) (k : ENNReal) (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) (k : NNReal)
  have hi := ((integrable_const (1 : ℝ)).add hm.integrable_norm_pow').const_mul (2 ^ k)
  refine hi.mono' ((continuous_const.add continuous_abs).pow k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := add_pow_le (zero_le_one) (abs_nonneg u) k
  simp only [one_pow, id, Real.norm_eq_abs] at this ⊢
  calc (1 + |u|) ^ k ≤ 2 ^ (k - 1) * (1 + |u| ^ k) := this
    _ ≤ 2 ^ k * (1 + |u| ^ k) := by
        gcongr
        · norm_num
        · omega

lemma PB.integrable {f : ℝ → ℝ} (hf : PB f) (v : NNReal) : Integrable f (gaussianReal 0 v) := by
  obtain ⟨hm, C, k, h⟩ := hf
  exact ((integrable_one_add_abs_pow_gauss v k).const_mul C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact h t)

lemma gaussAvg_of_nonpos {s : ℝ} (hs : s ≤ 0) (f : ℝ → ℝ) : gaussAvg s f = f 0 := by
  unfold gaussAvg
  rw [Real.toNNReal_of_nonpos hs, gaussianReal_zero_var, integral_dirac]

lemma gaussAvg_scale {s : ℝ} (hs : 0 < s) {f : ℝ → ℝ} (hf : Measurable f) :
    gaussAvg s f = ∫ u, f (Real.sqrt s * u) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun u => Real.sqrt s * u) = gaussianReal 0 s.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hs.le, Real.coe_toNNReal _ hs.le]
  unfold gaussAvg
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]

end growth

section rowLaw

open Complex Matrix
open scoped RealInnerProductSpace

/-- characteristic integral of a linear form of iid standard Gaussians (from c38c8303). -/
lemma integral_cexp_linear {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun k (x : ℝ) => cexp ((c k * x : ℝ) * I)) (μ := fun _ : κ => gaussianReal 0 1)
  have h2 : ∀ k, ∫ x, cexp ((c k * x : ℝ) * I) ∂gaussianReal 0 1 = cexp (-(c k ^ 2 : ℝ) / 2) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := 1) (c k)
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [this]; congr 1; ring
  calc ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = ∫ u : κ → ℝ, ∏ k, cexp ((c k * u k : ℝ) * I)
          ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
        congr 1 with u
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∏ k, cexp (-(c k ^ 2 : ℝ) / 2) := by rw [h]; simp only [h2]
    _ = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma map_pi_gaussian_linear {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => WithLp.toLp 2 (A *ᵥ u)) =
      multivariateGaussian 0 (A * A.transpose) := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_multivariateGaussian hPSD, charFun_apply,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hinner : ∀ u : κ → ℝ,
      ⟪WithLp.toLp 2 (A *ᵥ u), s⟫ = ∑ k, (A.transpose *ᵥ s.ofLp) k * u k := by
    intro u
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      RCLike.inner_apply, conj_trivial, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hinner]
  rw [integral_cexp_linear]
  have hq : ∑ k, (A.transpose *ᵥ s.ofLp) k ^ 2 = s.ofLp ⬝ᵥ (A * A.transpose) *ᵥ s.ofLp := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp [dotProduct, sq]
  rw [hq]
  congr 1
  simp [neg_div]

lemma map_pi_gaussian_linear_eval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => (A *ᵥ u) i) =
      gaussianReal 0 ((A * A.transpose) i i).toNNReal := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  rw [show (fun u => (A *ᵥ u) i) =
      (fun v : EuclideanSpace ℝ ι => v i) ∘ (fun u => WithLp.toLp 2 (A *ᵥ u)) from rfl,
    ← Measure.map_map (PiLp.continuous_apply 2 _ i).measurable hmeas, map_pi_gaussian_linear,
    (measurePreserving_eval_multivariateGaussian hPSD).map_eq]
  simp

/-- law of a linear form of iid standard Gaussians. -/
lemma rowLaw {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => ∑ q, c q * u q) =
      gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  have h := map_pi_gaussian_linear_eval (ι := Fin 1) (Matrix.of fun (_ : Fin 1) q => c q) 0
  have e1 : (fun u : κ → ℝ => ((Matrix.of fun (_ : Fin 1) q => c q) *ᵥ u) 0) =
      fun u => ∑ q, c q * u q := by
    funext u; simp [Matrix.mulVec, dotProduct]
  have e2 : ((Matrix.of fun (_ : Fin 1) q => c q) *
      (Matrix.of fun (_ : Fin 1) q => c q).transpose) 0 0 = ∑ q, c q ^ 2 := by
    simp [Matrix.mul_apply, sq]
  rw [e1, e2] at h
  exact h

/-- joint law of independent rows. -/
lemma rowsLaw {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1).map
      (fun Y i => ∑ q, c q * Y i q) =
      Measure.pi fun _ : ι => gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  rw [Measure.pi_map_pi (f := fun _ (u : κ → ℝ) => ∑ q, c q * u q)
    (fun _ => (Finset.measurable_sum _ fun q _ => by fun_prop).aemeasurable)]
  simp only [rowLaw]

end rowLaw

section condGauss

variable {n : ℕ → ℕ} {L : ℕ}

lemma measurable_mlpZ (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (x : Fin (n 0) → ℝ) :
    ∀ (ℓ : ℕ) (i : Fin (n ℓ)), Measurable (fun θ : Params n L => mlpZ Cb CW σ θ x ℓ i)
  | 0, _ => measurable_const
  | ℓ + 1, i => by
    have ih := measurable_mlpZ Cb CW hσ x ℓ
    have hb : Measurable (fun θ : Params n L => mlpBias Cb θ ℓ i) := by
      by_cases h : ℓ < L + 1
      · simp only [mlpBias, dif_pos h]; exact (measurable_pi_apply _).const_mul _
      · simp only [mlpBias, dif_neg h]; exact measurable_const
    have hw : ∀ j, Measurable (fun θ : Params n L => mlpWeight CW θ ℓ i j) := by
      intro j
      by_cases h : ℓ < L + 1
      · simp only [mlpWeight, dif_pos h]; exact (measurable_pi_apply _).const_mul _
      · simp only [mlpWeight, dif_neg h]; exact measurable_const
    have ha : ∀ j, Measurable (fun θ : Params n L => act Cb CW σ θ x ℓ j) := by
      intro j
      by_cases h : ℓ = 0
      · simp only [act, if_pos h]; exact ih j
      · simp only [act, if_neg h]; exact hσ.comp (ih j)
    exact hb.add (Finset.measurable_sum _ fun j _ => (hw j).mul (ha j))

lemma measurable_act (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n m)) : Measurable (fun θ : Params n L => act Cb CW σ θ x m j) := by
  by_cases h : m = 0
  · simp only [act, if_pos h]; exact measurable_mlpZ Cb CW hσ x m j
  · simp only [act, if_neg h]; exact hσ.comp (measurable_mlpZ Cb CW hσ x m j)

/-- parameters with the layer-`m` block zeroed and the rest given by `r`. -/
noncomputable def fill (m : ℕ) (r : {a : ParamIndex n L // ¬ layerOf a = m} → ℝ) : Params n L :=
  fun a => if h : layerOf a = m then 0 else r ⟨a, h⟩

lemma act_eq_fill (Cb CW : ℝ) (σ : ℝ → ℝ) (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1)
    (θ : Params n L) :
    act Cb CW σ θ x m = act Cb CW σ (fill m (splitME m hm θ).2) x m := by
  have h := mlpZ_congr Cb CW σ (θ := θ) (θ' := fill m (splitME m hm θ).2) x m (fun a ha => by
    rw [splitME_apply]; simp only [fill, dif_neg (show ¬ layerOf a = m by omega)])
  funext j; simp only [act, h]

/-- coefficients of a layer-`(m+1)` preactivation in its (bias, weights) block. -/
noncomputable def coef (Cb CW : ℝ) (n : ℕ → ℕ) (m : ℕ) (a : Fin (n m) → ℝ) :
    Option (Fin (n m)) → ℝ
  | none => Real.sqrt Cb
  | some j => Real.sqrt (CW / n m) * a j

lemma mlpZ_succ_split (Cb CW : ℝ) (σ : ℝ → ℝ) (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1)
    (θ : Params n L) (i : Fin (n (m + 1))) :
    mlpZ Cb CW σ θ x (m + 1) i =
      ∑ q, coef Cb CW n m (act Cb CW σ θ x m) q * (splitME m hm θ).1 i q := by
  rw [mlpZ_succ, Fintype.sum_option, splitME_apply]
  simp only [mlpBias, mlpWeight, dif_pos hm, coef, blk]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

lemma sum_coef_sq (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (n : ℕ → ℕ) (m : ℕ)
    (a : Fin (n m) → ℝ) :
    ∑ q, coef Cb CW n m a q ^ 2 = Cb + CW / n m * ∑ j, a j ^ 2 := by
  rw [Fintype.sum_option]
  simp only [coef, mul_pow, Real.sq_sqrt hCb, Real.sq_sqrt (div_nonneg hCW (Nat.cast_nonneg _)),
    Finset.mul_sum]

/-- F1: conditional Gaussianity of layer `m+1` given the earlier layers. -/
theorem condGauss_integral (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1) {Φ : (Fin (n (m + 1)) → ℝ) → ℝ}
    (hΦ : Measurable Φ)
    (hint : Integrable (fun θ => Φ (mlpZ Cb CW σ θ x (m + 1))) (stdGaussianParams n L)) :
    Integrable (fun θ => ∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal))
      (stdGaussianParams n L) ∧
    ∫ θ, Φ (mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L) =
      ∫ θ, (∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal))
        ∂(stdGaussianParams n L) := by
  have hmp := measurePreserving_splitME (n := n) (L := L) m hm
  let A : ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → Fin (n m) → ℝ :=
    fun r => act Cb CW σ (fill m r) x m
  let G : (Fin (n m) → ℝ) → ℝ := fun a => ∫ y, Φ y ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, a j ^ 2).toNNReal)
  let F : (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
      ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → ℝ :=
    fun p => Φ (fun i => ∑ q, coef Cb CW n m (A p.2) q * p.1 i q)
  have hFe : ∀ θ, F (splitME m hm θ) = Φ (mlpZ Cb CW σ θ x (m + 1)) := by
    intro θ
    simp only [F, A]
    congr 1; funext i
    rw [mlpZ_succ_split Cb CW σ x m hm θ i, ← act_eq_fill]
  have hGe : ∀ θ, G (A (splitME m hm θ).2) = G (act Cb CW σ θ x m) := by
    intro θ; simp only [A]; rw [← act_eq_fill]
  have hFint : Integrable F
      ((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
        (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
    rw [← hmp.integrable_comp_emb (splitME m hm).measurableEmbedding]
    refine hint.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Function.comp]; rw [hFe]
  have hinner : ∀ r, ∫ Y, F (Y, r) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1) = G (A r) := by
    intro r
    have hmY : Measurable (fun Y : Fin (n (m + 1)) → Option (Fin (n m)) → ℝ =>
        fun i => ∑ q, coef Cb CW n m (A r) q * Y i q) := by
      refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun q _ => ?_
      fun_prop
    simp only [F, G]
    rw [← sum_coef_sq Cb CW hCb hCW n m (A r), ← rowsLaw,
      integral_map hmY.aemeasurable hΦ.aestronglyMeasurable]
  have hGint : Integrable (fun r => G (A r))
      (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) := by
    have := hFint.integral_prod_right
    simpa only [hinner] using this
  constructor
  · have h2 := hGint.comp_snd (Measure.pi fun _ : Fin (n (m + 1)) =>
      Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
    rw [← hmp.integrable_comp_emb (splitME m hm).measurableEmbedding] at h2
    refine h2.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Function.comp]; exact hGe θ
  · calc ∫ θ, Φ (mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L)
        = ∫ θ, F (splitME m hm θ) ∂(stdGaussianParams n L) := by simp only [hFe]
      _ = ∫ p, F p ∂((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
          gaussianReal 0 1).prod
          (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) :=
          hmp.integral_comp' F
      _ = ∫ r, ∫ Y, F (Y, r) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
            Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
            ∂(Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) :=
          integral_prod_symm F hFint
      _ = ∫ r, G (A r)
            ∂(Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) := by
          simp only [hinner]
      _ = ∫ p, (1 : ℝ) * G (A p.2)
            ∂((Measure.pi fun _ : Fin (n (m + 1)) => Measure.pi fun _ : Option (Fin (n m)) =>
              gaussianReal 0 1).prod
            (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
          rw [integral_prod_mul (fun _ => (1 : ℝ)) (fun r => G (A r))]; simp
      _ = ∫ θ, (1 : ℝ) * G (A (splitME m hm θ).2) ∂(stdGaussianParams n L) :=
          (hmp.integral_comp' (fun p => (1 : ℝ) * G (A p.2))).symm
      _ = _ := by simp only [one_mul, hGe]; rfl

end condGauss

section integrability

/-- polynomially bounded measurable functions of finitely many real parameters. -/
def PT {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∃ p : ℕ, ∀ θ, |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p

variable {ι : Type*} [Fintype ι]

lemma one_le_base (θ : ι → ℝ) : (1 : ℝ) ≤ 1 + ∑ a, |θ a| := by
  have : 0 ≤ ∑ a, |θ a| := Finset.sum_nonneg fun a _ => abs_nonneg _
  linarith

lemma PT.nonneg_const {F : (ι → ℝ) → ℝ} {C : ℝ} {p : ℕ}
    (h : ∀ θ, |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p) : 0 ≤ C := by
  have h0 := h 0
  simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, add_zero, one_pow, mul_one] at h0
  exact (abs_nonneg _).trans h0

lemma PT.const (c : ℝ) : PT (ι := ι) (fun _ => c) := ⟨measurable_const, |c|, 0, fun θ => by simp⟩

lemma PT.coord (a : ι) : PT (fun θ : ι → ℝ => θ a) := by
  refine ⟨measurable_pi_apply a, 1, 1, fun θ => ?_⟩
  have : |θ a| ≤ ∑ b, |θ b| :=
    Finset.single_le_sum (f := fun b => |θ b|) (fun b _ => abs_nonneg _) (Finset.mem_univ a)
  simp only [pow_one, one_mul]; linarith

lemma PT.mul {F G : (ι → ℝ) → ℝ} (hF : PT F) (hG : PT G) : PT (fun θ => F θ * G θ) := by
  obtain ⟨hFm, C1, k1, h1⟩ := hF
  obtain ⟨hGm, C2, k2, h2⟩ := hG
  refine ⟨hFm.mul hGm, C1 * C2, k1 + k2, fun θ => ?_⟩
  rw [abs_mul, pow_add]
  have := PT.nonneg_const h1
  have hB := one_le_base θ
  calc |F θ| * |G θ| ≤ (C1 * (1 + ∑ a, |θ a|) ^ k1) * (C2 * (1 + ∑ a, |θ a|) ^ k2) :=
        mul_le_mul (h1 θ) (h2 θ) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma PT.add {F G : (ι → ℝ) → ℝ} (hF : PT F) (hG : PT G) : PT (fun θ => F θ + G θ) := by
  obtain ⟨hFm, C1, k1, h1⟩ := hF
  obtain ⟨hGm, C2, k2, h2⟩ := hG
  refine ⟨hFm.add hGm, C1 + C2, k1 + k2, fun θ => ?_⟩
  have c1 := PT.nonneg_const h1
  have c2 := PT.nonneg_const h2
  have hB := one_le_base θ
  have e1 : (1 + ∑ a, |θ a|) ^ k1 ≤ (1 + ∑ a, |θ a|) ^ (k1 + k2) := pow_le_pow_right₀ hB (by omega)
  have e2 : (1 + ∑ a, |θ a|) ^ k2 ≤ (1 + ∑ a, |θ a|) ^ (k1 + k2) := pow_le_pow_right₀ hB (by omega)
  calc |F θ + G θ| ≤ |F θ| + |G θ| := abs_add_le _ _
    _ ≤ C1 * (1 + ∑ a, |θ a|) ^ k1 + C2 * (1 + ∑ a, |θ a|) ^ k2 := add_le_add (h1 θ) (h2 θ)
    _ ≤ C1 * (1 + ∑ a, |θ a|) ^ (k1 + k2) + C2 * (1 + ∑ a, |θ a|) ^ (k1 + k2) := by gcongr
    _ = _ := by ring

lemma PT.sum {κ : Type*} (s : Finset κ) {F : κ → (ι → ℝ) → ℝ} (h : ∀ k ∈ s, PT (F k)) :
    PT (fun θ => ∑ k ∈ s, F k θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PT.const (ι := ι) 0
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma PT.comp {f : ℝ → ℝ} (hf : PB f) {F : (ι → ℝ) → ℝ} (hF : PT F) : PT (fun θ => f (F θ)) := by
  obtain ⟨hfm, Cf, k, hfb⟩ := hf
  obtain ⟨hFm, C, p, hFb⟩ := hF
  have hCf := PB.nonneg_const hfb
  have hC := PT.nonneg_const hFb
  refine ⟨hfm.comp hFm, Cf * (1 + C) ^ k, p * k, fun θ => ?_⟩
  have hB := one_le_base θ
  have hX : (1:ℝ) ≤ (1 + ∑ a, |θ a|) ^ p := one_le_pow₀ hB
  have e : 1 + |F θ| ≤ (1 + C) * (1 + ∑ a, |θ a|) ^ p := by nlinarith [hFb θ]
  calc |f (F θ)| ≤ Cf * (1 + |F θ|) ^ k := hfb _
    _ ≤ Cf * ((1 + C) * (1 + ∑ a, |θ a|) ^ p) ^ k := by gcongr
    _ = Cf * (1 + C) ^ k * (1 + ∑ a, |θ a|) ^ (p * k) := by rw [mul_pow, ← pow_mul]; ring

lemma PT.integrable {F : (ι → ℝ) → ℝ} (hF : PT F) :
    Integrable F (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  obtain ⟨hFm, C, p, hFb⟩ := hF
  have hC := PT.nonneg_const hFb
  have hcoord : ∀ a, Integrable (fun θ : ι → ℝ => |θ a| ^ (p + 1))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    intro a
    have h1 : Integrable (fun t : ℝ => |t| ^ (p + 1)) (gaussianReal 0 1) := by
      have hm : MemLp (id : ℝ → ℝ) ((p + 1 : ℕ) : ENNReal) (gaussianReal 0 1) := by
        simpa using memLp_id_gaussianReal (μ := 0) (v := 1) ((p + 1 : ℕ) : NNReal)
      simpa [Real.norm_eq_abs] using hm.integrable_norm_pow'
    exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).integrable_comp_of_integrable h1
  have hpm : ∀ θ : ι → ℝ, (1 + ∑ a, |θ a|) ^ (p + 1) ≤
      ((Fintype.card ι + 1 : ℕ) : ℝ) ^ p * (1 + ∑ a, |θ a| ^ (p + 1)) := by
    intro θ
    have h := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset (Option ι)))
      (f := fun o => Option.elim o 1 (fun a => |θ a|)) (fun o _ => by cases o <;> simp) p
    simp only [Fintype.sum_option, Option.elim, one_pow, Finset.card_univ, Fintype.card_option] at h
    rw [div_le_iff₀ (by positivity)] at h
    push_cast at h ⊢
    linarith
  have hG : Integrable (fun θ : ι → ℝ => C * ((Fintype.card ι + 1 : ℕ) : ℝ) ^ p *
      (1 + ∑ a, |θ a| ^ (p + 1))) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    ((integrable_const 1).add (integrable_finsetSum _ fun a _ => hcoord a)).const_mul _
  refine hG.mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs]
  have hB := one_le_base θ
  calc |F θ| ≤ C * (1 + ∑ a, |θ a|) ^ p := hFb θ
    _ ≤ C * (1 + ∑ a, |θ a|) ^ (p + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ p)) hC
    _ ≤ C * (((Fintype.card ι + 1 : ℕ) : ℝ) ^ p * (1 + ∑ a, |θ a| ^ (p + 1))) :=
        mul_le_mul_of_nonneg_left (hpm θ) hC
    _ = _ := by ring

end integrability

section network

variable {n : ℕ → ℕ} {L : ℕ}

lemma PT_mlpZ (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) :
    ∀ (ℓ : ℕ) (i : Fin (n ℓ)), PT (fun θ : Params n L => mlpZ Cb CW σ θ x ℓ i)
  | 0, i => PT.const (x i)
  | ℓ + 1, i => by
    have ih := PT_mlpZ Cb CW hσ x ℓ
    have hb : PT (fun θ : Params n L => mlpBias Cb θ ℓ i) := by
      by_cases h : ℓ < L + 1
      · simp only [mlpBias, dif_pos h]; exact (PT.const _).mul (PT.coord _)
      · simp only [mlpBias, dif_neg h]; exact PT.const 0
    have hw : ∀ j, PT (fun θ : Params n L => mlpWeight CW θ ℓ i j) := by
      intro j
      by_cases h : ℓ < L + 1
      · simp only [mlpWeight, dif_pos h]; exact (PT.const _).mul (PT.coord _)
      · simp only [mlpWeight, dif_neg h]; exact PT.const 0
    have ha : ∀ j, PT (fun θ : Params n L => act Cb CW σ θ x ℓ j) := by
      intro j
      by_cases h : ℓ = 0
      · simp only [act, if_pos h]; exact ih j
      · simp only [act, if_neg h]; exact PT.comp hσ (ih j)
    exact hb.add (PT.sum _ fun j _ => (hw j).mul (ha j))

lemma PT_act (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) (m : ℕ) (j : Fin (n m)) :
    PT (fun θ : Params n L => act Cb CW σ θ x m j) := by
  by_cases h : m = 0
  · simp only [act, if_pos h]; exact PT_mlpZ Cb CW hσ x m j
  · simp only [act, if_neg h]; exact PT.comp hσ (PT_mlpZ Cb CW hσ x m j)

/-- the conditional variance of layer `m+1`: `S_m = C_b + C_W/n_m Σ_j act_j²`. -/
noncomputable def Sv (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ) : ℝ :=
  Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2

lemma Sv_nonneg {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) (σ : ℝ → ℝ) (θ : Params n L)
    (x : Fin (n 0) → ℝ) (m : ℕ) : 0 ≤ Sv Cb CW σ θ x m := by
  unfold Sv; positivity

lemma PT_Sv (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) (m : ℕ) :
    PT (fun θ : Params n L => Sv Cb CW σ θ x m) :=
  (PT.const Cb).add ((PT.const _).mul (PT.sum _ fun j _ =>
    PT.comp (PB.id'.pow 2) (PT_act Cb CW hσ x m j)))

/-- M7: the normalized fourth cumulant of layer `m+1` is the variance of `S_m`. -/
theorem kappa4_succ {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : PB σ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1) (i : Fin (n (m + 1))) :
    kappa4 Cb CW σ n L x (m + 1) i =
      ∫ θ, Sv Cb CW σ θ x m ^ 2 ∂(stdGaussianParams n L) -
        (∫ θ, Sv Cb CW σ θ x m ∂(stdGaussianParams n L)) ^ 2 := by
  have hz := PT_mlpZ (L := L) Cb CW hσ x (m + 1) i
  have h4 := condGauss_integral Cb CW hCb hCW σ x m hm (Φ := fun y => y i ^ 4) (by fun_prop)
    (PT.integrable (PT.comp (PB.id'.pow 4) hz))
  have h2 := condGauss_integral Cb CW hCb hCW σ x m hm (Φ := fun y => y i ^ 2) (by fun_prop)
    (PT.integrable (PT.comp (PB.id'.pow 2) hz))
  have e4 : ∀ θ : Params n L, ∫ y, y i ^ 4 ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal) =
      3 * Sv Cb CW σ θ x m ^ 2 := by
    intro θ
    rw [integral_comp_eval (μ := fun _ => gaussianReal 0 _) (i := i) (f := fun t => t ^ 4)
      (by fun_prop), gauss_mom4, Real.coe_toNNReal _ (show (0:ℝ) ≤ Cb + CW / n m * ∑ j,
        act Cb CW σ θ x m j ^ 2 from Sv_nonneg hCb hCW σ θ x m)]
    rfl
  have e2 : ∀ θ : Params n L, ∫ y, y i ^ 2 ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal) =
      Sv Cb CW σ θ x m := by
    intro θ
    rw [integral_comp_eval (μ := fun _ => gaussianReal 0 _) (i := i) (f := fun t => t ^ 2)
      (by fun_prop), gauss_mom2, Real.coe_toNNReal _ (show (0:ℝ) ≤ Cb + CW / n m * ∑ j,
        act Cb CW σ θ x m j ^ 2 from Sv_nonneg hCb hCW σ θ x m)]
    rfl
  beta_reduce at h4 h2
  unfold kappa4
  rw [h4.2, h2.2]
  simp only [e4, e2]
  rw [integral_const_mul]
  ring

end network



section netTrans

variable {n : ℕ → ℕ} {L : ℕ}

lemma act_succ (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) (m : ℕ)
    (j : Fin (n (m + 1))) : act Cb CW σ θ x (m + 1) j = σ (mlpZ Cb CW σ θ x (m + 1) j) := by
  simp [act]

lemma Sv_zero (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L) (x : Fin (n 0) → ℝ) :
    Sv Cb CW σ θ x 0 = Cb + CW / n 0 * ∑ j, x j ^ 2 := by
  simp only [Sv, act]
  rfl

/-- the one-step transition of the collective variance `S_m ↦ S_{m+1}`. -/
theorem trans_S {Cb CW : ℝ} (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : PB σ)
    (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m + 1 < L + 1) {Φ : ℝ → ℝ} (hΦ : PB Φ) :
    Integrable (fun θ => ∫ y, Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)
        ∂(Measure.pi fun _ : Fin (n (m + 1)) => gaussianReal 0 (Sv Cb CW σ θ x m).toNNReal))
      (stdGaussianParams n L) ∧
    ∫ θ, Φ (Sv Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L) =
      ∫ θ, (∫ y, Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)
        ∂(Measure.pi fun _ : Fin (n (m + 1)) => gaussianReal 0 (Sv Cb CW σ θ x m).toNNReal))
        ∂(stdGaussianParams n L) := by
  have hmeas : Measurable (fun y : Fin (n (m + 1)) → ℝ => Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)) :=
    hΦ.1.comp (measurable_const.add (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (hσ.1.comp (measurable_pi_apply j)).pow_const 2)))
  have e : ∀ θ : Params n L, Φ (Sv Cb CW σ θ x (m + 1)) =
      Φ (Cb + CW / n (m + 1) * ∑ j, σ (mlpZ Cb CW σ θ x (m + 1) j) ^ 2) := by
    intro θ; simp only [Sv, act_succ]
  have hint : Integrable (fun θ : Params n L =>
      Φ (Cb + CW / n (m + 1) * ∑ j, σ (mlpZ Cb CW σ θ x (m + 1) j) ^ 2)) (stdGaussianParams n L) := by
    refine (PT.integrable (PT.comp hΦ (PT_Sv Cb CW hσ x (m + 1)))).congr
      (Filter.Eventually.of_forall fun θ => ?_)
    exact e θ
  have h := condGauss_integral Cb CW hCb hCW σ x m (by omega)
    (Φ := fun y => Φ (Cb + CW / n (m + 1) * ∑ j, σ (y j) ^ 2)) hmeas hint
  refine ⟨h.1, ?_⟩
  simp only [e]
  exact h.2

end netTrans



end FW
end LesHouchesWidth


set_option autoImplicit false

namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory

section condLaw

variable {n : ℕ → ℕ} {L : ℕ}

lemma measurable_fill (m : ℕ) : Measurable (fill (n := n) (L := L) m) := by
  refine measurable_pi_lambda _ fun a => ?_
  by_cases h : layerOf a = m
  · simp only [fill, dif_pos h]; exact measurable_const
  · simp only [fill, dif_neg h]; exact measurable_pi_apply _

/-- joint version of `condGauss_integral`: the layer-`m` preactivations are a function of the
parameters of the earlier layers, and layer `m+1` is conditionally Gaussian given them. -/
theorem condGauss_lintegral (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ}
    (hσ : Measurable σ) (x : Fin (n 0) → ℝ) (m : ℕ) (hm : m < L + 1)
    {Φ : (Fin (n m) → ℝ) × (Fin (n (m + 1)) → ℝ) → ENNReal} (hΦ : Measurable Φ) :
    ∫⁻ θ, Φ (mlpZ Cb CW σ θ x m, mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L) =
      ∫⁻ θ, (∫⁻ y, Φ (mlpZ Cb CW σ θ x m, y) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
        gaussianReal 0 (Cb + CW / n m * ∑ j, act Cb CW σ θ x m j ^ 2).toNNReal))
        ∂(stdGaussianParams n L) := by
  have hmp := measurePreserving_splitME (n := n) (L := L) m hm
  let Zr : ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → Fin (n m) → ℝ :=
    fun r => mlpZ Cb CW σ (fill m r) x m
  let A : ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → Fin (n m) → ℝ :=
    fun r => act Cb CW σ (fill m r) x m
  let F : (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
      ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → ENNReal :=
    fun p => Φ (Zr p.2, fun i => ∑ q, coef Cb CW n m (A p.2) q * p.1 i q)
  have hZ : ∀ θ, mlpZ Cb CW σ θ x m = Zr (splitME m hm θ).2 := by
    intro θ
    exact mlpZ_congr Cb CW σ x m (fun a ha => by
      rw [splitME_apply]; simp only [fill, dif_neg (show ¬ layerOf a = m by omega)])
  have hFe : ∀ θ, F (splitME m hm θ) = Φ (mlpZ Cb CW σ θ x m, mlpZ Cb CW σ θ x (m + 1)) := by
    intro θ
    simp only [F, A]
    rw [← hZ]
    congr 2; funext i
    rw [mlpZ_succ_split Cb CW σ x m hm θ i, ← act_eq_fill]
  have hZr : Measurable Zr :=
    measurable_pi_lambda _ fun j => (measurable_mlpZ Cb CW hσ x m j).comp (measurable_fill m)
  have hA : Measurable A :=
    measurable_pi_lambda _ fun j => (measurable_act Cb CW hσ x m j).comp (measurable_fill m)
  have hcoef : ∀ q, Measurable (fun r => coef Cb CW n m (A r) q) := by
    intro q
    cases q with
    | none => exact measurable_const
    | some j => exact measurable_const.mul ((measurable_pi_apply j).comp hA)
  have hF : Measurable F := by
    refine hΦ.comp (Measurable.prodMk (hZr.comp measurable_snd) ?_)
    refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun q _ => ?_
    have hc : Measurable (fun c : (Fin (n (m + 1)) → Option (Fin (n m)) → ℝ) ×
        ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) => c.1 i q) := by fun_prop
    exact ((hcoef q).comp measurable_snd).mul hc
  let H : ({a : ParamIndex n L // ¬ layerOf a = m} → ℝ) → ENNReal :=
    fun r => ∫⁻ Y, F (Y, r) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
  have hH : Measurable H := hF.lintegral_prod_left'
  have hinner : ∀ r, H r = ∫⁻ y, Φ (Zr r, y) ∂(Measure.pi fun _ : Fin (n (m + 1)) =>
      gaussianReal 0 (Cb + CW / n m * ∑ j, A r j ^ 2).toNNReal) := by
    intro r
    have hmY : Measurable (fun Y : Fin (n (m + 1)) → Option (Fin (n m)) → ℝ =>
        fun i => ∑ q, coef Cb CW n m (A r) q * Y i q) := by
      refine measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun q _ => ?_
      fun_prop
    simp only [H, F]
    rw [← sum_coef_sq Cb CW hCb hCW n m (A r), ← rowsLaw,
      lintegral_map (show Measurable (fun y => Φ (Zr r, y)) from
        hΦ.comp (measurable_const.prodMk measurable_id)) hmY]
  calc ∫⁻ θ, Φ (mlpZ Cb CW σ θ x m, mlpZ Cb CW σ θ x (m + 1)) ∂(stdGaussianParams n L)
      = ∫⁻ θ, F (splitME m hm θ) ∂(stdGaussianParams n L) := by simp only [hFe]
    _ = ∫⁻ p, F p ∂((Measure.pi fun _ : Fin (n (m + 1)) =>
          Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1).prod
          (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) :=
        hmp.lintegral_comp_emb (splitME m hm).measurableEmbedding F
    _ = ∫⁻ r, H r
          ∂(Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1) :=
        lintegral_prod_symm F hF.aemeasurable
    _ = ∫⁻ p, H p.2 ∂((Measure.pi fun _ : Fin (n (m + 1)) =>
          Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1).prod
          (Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)) := by
        have := lintegral_prod_symm (μ := Measure.pi fun _ : Fin (n (m + 1)) =>
            Measure.pi fun _ : Option (Fin (n m)) => gaussianReal 0 1)
          (ν := Measure.pi fun _ : {a : ParamIndex n L // ¬ layerOf a = m} => gaussianReal 0 1)
          (fun p => H p.2) (hH.comp measurable_snd).aemeasurable
        simp only [lintegral_const, measure_univ, mul_one] at this
        exact this.symm
    _ = ∫⁻ θ, H (splitME m hm θ).2 ∂(stdGaussianParams n L) :=
        (hmp.lintegral_comp_emb (splitME m hm).measurableEmbedding (fun p => H p.2)).symm
    _ = _ := by
        congr 1; funext θ
        rw [hinner, ← hZ]
        simp only [A]
        rw [← act_eq_fill]

open Matrix in
lemma mvG_scalar {k : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    multivariateGaussian 0 (c • (1 : Matrix (Fin k) (Fin k) ℝ)) =
      (Measure.pi fun _ : Fin k => gaussianReal 0 1).map
        (fun u => WithLp.toLp 2 (fun i => Real.sqrt c * u i)) := by
  have h := map_pi_gaussian_linear (Real.sqrt c • (1 : Matrix (Fin k) (Fin k) ℝ))
  have e1 : (Real.sqrt c • (1 : Matrix (Fin k) (Fin k) ℝ)) *
      (Real.sqrt c • (1 : Matrix (Fin k) (Fin k) ℝ)).transpose = c • 1 := by
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul, Matrix.mul_one,
      Real.mul_self_sqrt hc]
  have e2 : (fun u : Fin k → ℝ => WithLp.toLp 2
      ((Real.sqrt c • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ u)) =
      fun u => WithLp.toLp 2 (fun i => Real.sqrt c * u i) := by
    funext u
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [e1, e2] at h
  exact h.symm

lemma pi_scale {k : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun u i => Real.sqrt c * u i) =
      Measure.pi fun _ : Fin k => gaussianReal 0 c.toNNReal := by
  rw [Measure.pi_map_pi (f := fun _ (t : ℝ) => Real.sqrt c * t) (fun _ => by fun_prop)]
  congr 1; funext _
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp [Real.sq_sqrt hc, Real.coe_toNNReal _ hc]

/-- the conditional law of the next layer, as a kernel. -/
noncomputable def nextKernel (Cb CW : ℝ) (σ : ℝ → ℝ) (n : ℕ → ℕ) (ℓ : ℕ) (_hσ : Measurable σ) :
    Kernel (Fin (n ℓ) → ℝ) (EuclideanSpace ℝ (Fin (n (ℓ + 1)))) :=
  Kernel.map (Kernel.deterministic id measurable_id ×ₖ
      Kernel.const (Fin (n ℓ) → ℝ) (Measure.pi fun _ : Fin (n (ℓ + 1)) => gaussianReal 0 1))
    (fun p => WithLp.toLp 2 (fun i => Real.sqrt (collectiveSigma Cb CW σ n ℓ p.1) * p.2 i))

lemma measurable_collectiveSigma (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (n : ℕ → ℕ)
    (ℓ : ℕ) : Measurable (collectiveSigma Cb CW σ n ℓ) := by
  unfold collectiveSigma
  exact measurable_const.add (measurable_const.mul
    (Finset.measurable_sum _ fun j _ => (hσ.comp (measurable_pi_apply j)).pow_const 2))

lemma measurable_nextFun (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (n : ℕ → ℕ) (ℓ : ℕ) :
    Measurable (fun p : (Fin (n ℓ) → ℝ) × (Fin (n (ℓ + 1)) → ℝ) =>
      WithLp.toLp 2 (fun i => Real.sqrt (collectiveSigma Cb CW σ n ℓ p.1) * p.2 i)) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i => ?_)
  exact (((measurable_collectiveSigma Cb CW hσ n ℓ).comp measurable_fst).sqrt).mul
    ((measurable_pi_apply i).comp measurable_snd)

lemma nextKernel_apply (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (n : ℕ → ℕ) (ℓ : ℕ)
    (y : Fin (n ℓ) → ℝ) :
    nextKernel Cb CW σ n ℓ hσ y = (Measure.pi fun _ : Fin (n (ℓ + 1)) => gaussianReal 0 1).map
      (fun u => WithLp.toLp 2 (fun i => Real.sqrt (collectiveSigma Cb CW σ n ℓ y) * u i)) := by
  unfold nextKernel
  rw [Kernel.map_apply _ (measurable_nextFun Cb CW hσ n ℓ), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_nextFun Cb CW hσ n ℓ) measurable_prodMk_left]
  rfl

instance (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : Measurable σ) (n : ℕ → ℕ) (ℓ : ℕ) :
    IsMarkovKernel (nextKernel Cb CW σ n ℓ hσ) :=
  Kernel.IsMarkovKernel.map _ (measurable_nextFun Cb CW hσ n ℓ)

lemma nextKernel_eq_pi (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : Measurable σ)
    (n : ℕ → ℕ) (ℓ : ℕ) (y : Fin (n ℓ) → ℝ) :
    nextKernel Cb CW σ n ℓ hσ y =
      (Measure.pi fun _ : Fin (n (ℓ + 1)) =>
        gaussianReal 0 (collectiveSigma Cb CW σ n ℓ y).toNNReal).map (WithLp.toLp 2) := by
  have hc : 0 ≤ collectiveSigma Cb CW σ n ℓ y := by unfold collectiveSigma; positivity
  have hf : Measurable (fun (u : Fin (n (ℓ + 1)) → ℝ) i =>
      Real.sqrt (collectiveSigma Cb CW σ n ℓ y) * u i) :=
    measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i)
  rw [nextKernel_apply, ← pi_scale hc, Measure.map_map (PiLp.continuous_toLp 2 _).measurable hf]
  rfl

theorem cond_main (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 ≤ CW) {σ : ℝ → ℝ} (hσ : Measurable σ)
    (x : Fin (n 0) → ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    (stdGaussianParams n L).map (fun θ => (mlpZ Cb CW σ θ x ℓ,
        WithLp.toLp 2 (mlpZ Cb CW σ θ x (ℓ + 1)))) =
      (stdGaussianParams n L).map (fun θ => mlpZ Cb CW σ θ x ℓ) ⊗ₘ nextKernel Cb CW σ n ℓ hσ := by
  have hZ : Measurable (fun θ : Params n L => mlpZ Cb CW σ θ x ℓ) :=
    measurable_pi_lambda _ fun j => measurable_mlpZ Cb CW hσ x ℓ j
  have hZ1 : Measurable (fun θ : Params n L => mlpZ Cb CW σ θ x (ℓ + 1)) :=
    measurable_pi_lambda _ fun j => measurable_mlpZ Cb CW hσ x (ℓ + 1) j
  have hY : Measurable (fun θ : Params n L => WithLp.toLp 2 (mlpZ Cb CW σ θ x (ℓ + 1))) :=
    (PiLp.continuous_toLp 2 _).measurable.comp hZ1
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.compProd_apply_prod hs ht, Measure.map_apply (hZ.prodMk hY) (hs.prod ht),
    ← lintegral_indicator hs, lintegral_map
      ((Kernel.measurable_coe _ ht).indicator hs) hZ]
  -- the left side as a lintegral of a product of indicators
  have hT : MeasurableSet ((WithLp.toLp 2 : (Fin (n (ℓ + 1)) → ℝ) → _) ⁻¹' t) :=
    (PiLp.continuous_toLp 2 _).measurable ht
  let Φ : (Fin (n ℓ) → ℝ) × (Fin (n (ℓ + 1)) → ℝ) → ENNReal :=
    fun p => s.indicator 1 p.1 * ((WithLp.toLp 2 : (Fin (n (ℓ + 1)) → ℝ) → _) ⁻¹' t).indicator 1 p.2
  have hΦ : Measurable Φ :=
    ((measurable_const.indicator hs).comp measurable_fst).mul
      ((measurable_const.indicator hT).comp measurable_snd)
  have hpre : (stdGaussianParams n L) ((fun θ => (mlpZ Cb CW σ θ x ℓ,
      WithLp.toLp 2 (mlpZ Cb CW σ θ x (ℓ + 1)))) ⁻¹' s ×ˢ t) =
      ∫⁻ θ, Φ (mlpZ Cb CW σ θ x ℓ, mlpZ Cb CW σ θ x (ℓ + 1)) ∂(stdGaussianParams n L) := by
    classical
    rw [← lintegral_indicator_one ((hZ.prodMk hY) (hs.prod ht))]
    congr 1; funext θ
    simp only [Φ, Set.indicator_apply, Set.mem_preimage, Set.mem_prod, Pi.one_apply]
    split_ifs <;> simp_all
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  rw [hpre, condGauss_lintegral Cb CW hCb hCW hσ x (m + 1) (by omega) hΦ]
  congr 1; funext θ
  simp only [Φ]
  rw [lintegral_const_mul _ (measurable_one.indicator hT), lintegral_indicator_one hT]
  have e : (Cb + CW / n (m + 1) * ∑ j, act Cb CW σ θ x (m + 1) j ^ 2) =
      collectiveSigma Cb CW σ n (m + 1) (mlpZ Cb CW σ θ x (m + 1)) := by
    simp only [collectiveSigma, act_succ]
  by_cases h : mlpZ Cb CW σ θ x (m + 1) ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul,
      nextKernel_eq_pi Cb CW hCb hCW hσ n (m + 1),
      Measure.map_apply (PiLp.continuous_toLp 2 _).measurable ht, e]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

lemma memLp_two_Sv (Cb CW : ℝ) {σ : ℝ → ℝ} (hσ : PB σ) (x : Fin (n 0) → ℝ) (m : ℕ) :
    MemLp (fun θ : Params n L => Sv Cb CW σ θ x m) 2 (stdGaussianParams n L) := by
  have hS := PT_Sv (L := L) Cb CW hσ x m
  rw [memLp_two_iff_integrable_sq hS.1.aestronglyMeasurable]
  exact PT.integrable (PT.comp (PB.id'.pow 2) hS)

end condLaw

end FW
end LesHouchesWidth

open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution (Cb CW : ℝ) (hCb : 0 ≤ Cb) (hCW : 0 < CW)
    (σ : ℝ → ℝ) (hσ : Measurable σ) (hσ_poly : PolyBounded σ)
    (n : ℕ → ℕ) (L : ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ) (x : Fin (n 0) → ℝ)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    (∀ᵐ y ∂((stdGaussianParams n L).map (fun θ => mlpZ Cb CW σ θ x ℓ)),
      condDistrib (fun θ => (WithLp.equiv 2 (Fin (n (ℓ + 1)) → ℝ)).symm (mlpZ Cb CW σ θ x (ℓ + 1)))
          (fun θ => mlpZ Cb CW σ θ x ℓ) (stdGaussianParams n L) y =
        multivariateGaussian 0 (collectiveSigma Cb CW σ n ℓ y • (1 : Matrix _ _ ℝ))) ∧
    (∀ i : Fin (n (ℓ + 1)),
      kappa4 Cb CW σ n L x (ℓ + 1) i =
        variance (fun θ => collectiveSigma Cb CW σ n ℓ (mlpZ Cb CW σ θ x ℓ))
          (stdGaussianParams n L)) := by
  have _unused : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ := hn
  have hPB := FW.PB.of_polyBounded hσ hσ_poly
  constructor
  · have hY : AEMeasurable (fun θ : Params n L =>
        (WithLp.equiv 2 (Fin (n (ℓ + 1)) → ℝ)).symm (mlpZ Cb CW σ θ x (ℓ + 1)))
        (stdGaussianParams n L) :=
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (measurable_pi_lambda _ fun j => FW.measurable_mlpZ Cb CW hσ x (ℓ + 1) j)).aemeasurable
    have h := condDistrib_ae_eq_of_measure_eq_compProd (fun θ => mlpZ Cb CW σ θ x ℓ) hY
      (FW.cond_main Cb CW hCb hCW.le hσ x ℓ hℓ hℓL)
    filter_upwards [h] with y hy
    rw [hy, FW.nextKernel_apply, FW.mvG_scalar]
    unfold collectiveSigma
    positivity
  · intro i
    have hS : (fun θ : Params n L => collectiveSigma Cb CW σ n ℓ (mlpZ Cb CW σ θ x ℓ)) =
        fun θ : Params n L => FW.Sv Cb CW σ θ x ℓ := by
      funext θ
      obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
      simp only [collectiveSigma, FW.Sv, FW.act_succ]
    rw [hS, variance_eq_sub (FW.memLp_two_Sv Cb CW hPB x ℓ),
      FW.kappa4_succ hCb hCW.le hPB x ℓ (by omega) i]
    simp only [Pi.pow_apply]
