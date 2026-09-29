-- Prove2me | solution 1 for LesHouchesWidth.nngp_limit_one_hidden_layer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T11:11:25.405073+00:00
-- url     : https://prove2.me/submissions/b3d0687d-800e-4dac-8e48-304d309397fb

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

/-! c38c8303 LesHouchesWidth.nngp_limit_one_hidden_layer (Neal 1996 NNGP limit, one hidden layer).
Route: reindex the iid parameters into (output biases) x (N iid hidden-unit blocks), factor the
characteristic function, apply a variance-v version of Mathlib's 1-D CLT Taylor step per direction,
identify the limit with `charFun_multivariateGaussian`, conclude by Levy continuity. -/

set_option autoImplicit false

namespace LesHouchesWidth
open MeasureTheory ProbabilityTheory Complex Filter Matrix
open scoped RealInnerProductSpace Topology

/-- characteristic integral of a linear form of iid standard Gaussians -/
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
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) := by
    fun_prop
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
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) := by fun_prop
  rw [show (fun u => (A *ᵥ u) i) =
      (fun v : EuclideanSpace ℝ ι => v i) ∘ (fun u => WithLp.toLp 2 (A *ᵥ u)) from rfl,
    ← Measure.map_map (by fun_prop) hmeas, map_pi_gaussian_linear,
    (measurePreserving_eval_multivariateGaussian hPSD).map_eq]
  simp

lemma integral_eval_mul_eval {κ : Type*} [Fintype κ] [DecidableEq κ] (i j : κ) :
    ∫ w, w i * w j ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = if i = j then 1 else 0 := by
  classical
  split_ifs with hij
  · subst hij
    have hc := integral_comp_eval (μ := fun _ : κ => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => x * x) (by fun_prop)
    rw [hc]
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id (by simp)] at hv
    simpa [sq] using hv
  · have hind := (iIndepFun_pi (X := fun _ : κ => fun x : ℝ => x)
      (μ := fun _ => gaussianReal 0 1) (fun _ => aemeasurable_id)).indepFun hij
    rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable]
    simp [integral_eval, integral_id_gaussianReal]

section clt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

lemma taylor_charFun_two_var {X : Ω → ℝ} (hX : AEMeasurable X P) (hX2 : MemLp X 2 P)
    (h0 : P[X] = 0) {v : ℝ} (hv : P[X ^ 2] = v) :
    (fun t : ℝ ↦ charFun (P.map X) t - (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2)) =o[𝓝 0]
      fun t ↦ t ^ 2 := by
  have hint : MemLp id 2 (P.map X) := (memLp_map_measure_iff aestronglyMeasurable_id hX).2 hX2
  have ht : ∀ t : ℝ, (1 - (v : ℂ) * (t : ℂ) ^ 2 / 2) =
      taylorWithinEval (charFun (P.map X)) 2 Set.univ 0 t := by
    intro t
    rw [taylorWithinEval_charFun_two_zero hX hint, h0, hv]
    simp
  simp_rw [ht]
  convert! taylor_isLittleO_univ (contDiff_charFun hint)
  simp

lemma tendsto_charFun_pow_var {X : Ω → ℝ} (hX : AEMeasurable X P) (hX2 : MemLp X 2 P)
    (h0 : P[X] = 0) {v : ℝ} (hv : P[X ^ 2] = v) (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (charFun (P.map X) ((√n)⁻¹ * t)) ^ n) atTop
      (𝓝 (cexp (-((v : ℂ) * (t : ℂ) ^ 2) / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  have hs : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  have h1 := (taylor_charFun_two_var hX hX2 h0 hv).comp_tendsto hs
  have h2 : ((fun s : ℝ => s ^ 2) ∘ fun n : ℕ => (√n)⁻¹ * t) =O[atTop]
      fun n : ℕ => (1 / n : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (t ^ 2) (Filter.Eventually.of_forall fun n => ?_)
    simp only [Function.comp, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n),
      Real.norm_eq_abs, one_div]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    ring_nf
    exact le_refl _
  have h3 := h1.trans_isBigO h2
  rw [← Asymptotics.isLittleO_norm_right]
  have aux : (fun n : ℕ => ‖(1 / n : ℂ)‖) = fun n : ℕ => ‖(1 / n : ℝ)‖ := by simp
  rw [aux, Asymptotics.isLittleO_norm_right]
  refine h3.congr_left (fun n => ?_)
  simp only [Function.comp]
  congr 1
  push_cast
  rw [mul_pow, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast
  ring

end clt

/-- index map from the reorganized index type into the parameter index. -/
def idx (n0 n2 N : ℕ) :
    Fin n2 ⊕ (Fin N × (Option (Fin n0) ⊕ Fin n2)) → ParamIndex (uniformWidths n0 n2 1 N) 1
  | .inl i => .inl ⟨1, i⟩
  | .inr (j, .inl none) => .inl ⟨0, j⟩
  | .inr (j, .inl (some k)) => .inr ⟨0, (j, k)⟩
  | .inr (j, .inr i) => .inr ⟨1, (i, j)⟩

lemma idx_injective (n0 n2 N : ℕ) : Function.Injective (idx n0 n2 N) := by
  rintro (i | ⟨j, (_ | k) | i⟩) (i' | ⟨j', (_ | k') | i'⟩) h <;>
    simp only [idx, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h <;>
    injection h with h1 h2 <;> (try injection h2 with h3 h4) <;> simp_all [Fin.ext_iff]

lemma idx_surjective (n0 n2 N : ℕ) : Function.Surjective (idx n0 n2 N) := by
  rintro (⟨ℓ, i⟩ | ⟨ℓ, i, k⟩) <;> fin_cases ℓ
  · exact ⟨.inr (i, .inl none), rfl⟩
  · exact ⟨.inl i, rfl⟩
  · exact ⟨.inr (i, .inl (some k)), rfl⟩
  · exact ⟨.inr (k, .inr i), rfl⟩

/-- `idx` as an equivalence. -/
noncomputable def idxEquiv (n0 n2 N : ℕ) :
    Fin n2 ⊕ (Fin N × (Option (Fin n0) ⊕ Fin n2)) ≃ ParamIndex (uniformWidths n0 n2 1 N) 1 :=
  Equiv.ofBijective _ ⟨idx_injective n0 n2 N, idx_surjective n0 n2 N⟩

/-- reindexing a product of identical measures along an equivalence. -/
lemma mp_comp_equiv {P P' : Type*} [Fintype P] [Fintype P'] (e : P' ≃ P) (g : Measure ℝ)
    [SigmaFinite g] :
    MeasurePreserving (fun θ : P → ℝ => θ ∘ e) (Measure.pi fun _ : P => g)
      (Measure.pi fun _ : P' => g) := by
  have := measurePreserving_piCongrLeft (α := fun _ : P' => ℝ) (fun _ : P' => g) e.symm
  convert this using 1
  ext θ p
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- currying a product of identical probability measures over a product index. -/
lemma mp_curry {A B : Type*} [Fintype A] [Fintype B] (g : Measure ℝ) [IsProbabilityMeasure g] :
    MeasurePreserving (MeasurableEquiv.curry A B ℝ) (Measure.pi fun _ : A × B => g)
      (Measure.pi fun _ : A => Measure.pi fun _ : B => g) := by
  refine ⟨(MeasurableEquiv.curry A B ℝ).measurable, ?_⟩
  have := Measure.infinitePi_map_curry (ι := A) (κ := B) (X := ℝ) (fun _ _ => g)
  simp only [Measure.infinitePi_eq_pi] at this
  exact this

/-- the parameters, split into output biases and hidden-unit blocks. -/
def split (n0 n2 N : ℕ) (θ : Params (uniformWidths n0 n2 1 N) 1) :
    (Fin n2 → ℝ) × (Fin N → Option (Fin n0) ⊕ Fin n2 → ℝ) :=
  (fun i => θ (idx n0 n2 N (.inl i)), fun j q => θ (idx n0 n2 N (.inr (j, q))))

lemma measurePreserving_split (n0 n2 N : ℕ) :
    MeasurePreserving (split n0 n2 N) (stdGaussianParams (uniformWidths n0 n2 1 N) 1)
      ((Measure.pi fun _ : Fin n2 => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => Measure.pi fun _ : Option (Fin n0) ⊕ Fin n2 =>
          gaussianReal 0 1)) := by
  have h1 := mp_comp_equiv (idxEquiv n0 n2 N) (gaussianReal 0 1)
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Fin n2 ⊕ (Fin N × (Option (Fin n0) ⊕ Fin n2)) => ℝ) (fun _ => gaussianReal 0 1)
  have h3 := (MeasurePreserving.id (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)).prod
    (mp_curry (A := Fin N) (B := Option (Fin n0) ⊕ Fin n2) (gaussianReal 0 1))
  exact h3.comp (h2.comp h1)

variable (σb σw : ℝ) (φ : ℝ → ℝ) {n0 n2 m : ℕ} (xs : Fin m → Fin n0 → ℝ)

/-- first-layer coefficients of the unit's parameters `(bias, weights)` at input `a`. -/
noncomputable def coef (a : Fin m) (q : Option (Fin n0)) : ℝ :=
  q.elim (√(σb ^ 2)) fun k => √(σw ^ 2 / n0) * xs a k

/-- first-layer preactivation of one hidden unit at input `a`. -/
noncomputable def pre (a : Fin m) (u : Option (Fin n0) → ℝ) : ℝ :=
  ∑ q, coef σb σw xs a q * u q

lemma pre_eq (a : Fin m) (u : Option (Fin n0) → ℝ) :
    pre σb σw xs a u = √(σb ^ 2) * u none + ∑ k, √(σw ^ 2 / n0) * u (some k) * xs a k := by
  simp only [pre, coef, Fintype.sum_option, Option.elim]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma coef_sum (a b : Fin m) :
    ∑ q, coef σb σw xs a q * coef σb σw xs b q =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b) := by
  simp only [coef, Fintype.sum_option, Option.elim, nngpKernel]
  rw [Real.mul_self_sqrt (sq_nonneg σb)]
  have h : √(σw ^ 2 / n0) * √(σw ^ 2 / n0) = σw ^ 2 / n0 :=
    Real.mul_self_sqrt (by positivity)
  have : ∑ k, √(σw ^ 2 / n0) * xs a k * (√(σw ^ 2 / n0) * xs b k) =
      σw ^ 2 / n0 * ∑ k, xs a k * xs b k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by linear_combination (xs a k * xs b k) * h
  rw [this]
  ring

lemma nngpKernel_one_comm (x y : Fin n0 → ℝ) :
    nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x y = nngpKernel (σb ^ 2) (σw ^ 2) φ 1 y x := by
  simp only [nngpKernel, mul_comm (x _)]

/-- the `2 × (1 + n0)` coefficient matrix of the preactivations at inputs `a, b`. -/
noncomputable def pairMat (a b : Fin m) : Matrix (Fin 2) (Option (Fin n0)) ℝ :=
  Matrix.of fun r q => coef σb σw xs (![a, b] r) q

lemma pair_eq (a b : Fin m) :
    (fun u => WithLp.toLp 2 ![pre σb σw xs a u, pre σb σw xs b u]) =
      fun u => WithLp.toLp 2 (pairMat σb σw xs a b *ᵥ u) := by
  funext u
  congr 1
  ext r
  fin_cases r <;> rfl

lemma pairLaw (a b : Fin m) :
    (Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).map
        (fun u => WithLp.toLp 2 ![pre σb σw xs a u, pre σb σw xs b u]) =
      multivariateGaussian 0
        !![nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a),
            nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b);
          nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b),
            nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs b) (xs b)] := by
  have h2 : pairMat σb σw xs a b * (pairMat σb σw xs a b).transpose =
      !![nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a),
            nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b);
          nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b),
            nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs b) (xs b)] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [pairMat, Matrix.mul_apply, coef_sum σb σw φ,
        nngpKernel_one_comm σb σw φ (xs b) (xs a)]
  rw [pair_eq, map_pi_gaussian_linear, h2]

@[fun_prop] lemma measurable_pre (a : Fin m) : Measurable (pre σb σw xs a) := by
  unfold pre; fun_prop

lemma preLaw (a : Fin m) :
    (Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).map (pre σb σw xs a) =
      gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal := by
  have := map_pi_gaussian_linear_eval (Matrix.of fun (_ : Fin 1) q => coef σb σw xs a q) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
    coef_sum σb σw φ] at this
  exact this

lemma pairAvg_eq (hφ : Measurable φ) (a b : Fin m) :
    ∫ u, φ (pre σb σw xs a u) * φ (pre σb σw xs b u)
        ∂(Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1) =
      gaussPairAvg φ (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a))
        (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs b))
        (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs b) (xs b)) := by
  have hm : Measurable (fun u => WithLp.toLp 2 (pairMat σb σw xs a b *ᵥ u)) := by fun_prop
  rw [gaussPairAvg, ← pairLaw σb σw φ xs a b, pair_eq,
    integral_map hm.aemeasurable (by fun_prop)]
  simp [pairMat, Matrix.mulVec, dotProduct, pre]


/-- one hidden unit's output contribution (before the `1/√N` factor). -/
noncomputable def unitVec (h : Option (Fin n0) ⊕ Fin n2 → ℝ) :
    EuclideanSpace ℝ (Fin n2 × Fin m) :=
  WithLp.toLp 2 fun ia => √(σw ^ 2) * h (.inr ia.1) * φ (pre σb σw xs ia.2 fun q => h (.inl q))

/-- the output-bias contribution. -/
noncomputable def biasVec (b : Fin n2 → ℝ) : EuclideanSpace ℝ (Fin n2 × Fin m) :=
  WithLp.toLp 2 fun ia => √(σb ^ 2) * b ia.1

/-- the output vector as a function of the split parameters. -/
noncomputable def Zhat (N : ℕ) (p : (Fin n2 → ℝ) × (Fin N → Option (Fin n0) ⊕ Fin n2 → ℝ)) :
    EuclideanSpace ℝ (Fin n2 × Fin m) :=
  biasVec σb (m := m) p.1 + (√(N : ℝ))⁻¹ • ∑ j, unitVec σb σw φ xs (p.2 j)

lemma outputVector_eq (N : ℕ) (θ : Params (uniformWidths n0 n2 1 N) 1) :
    outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs θ =
      Zhat σb σw φ xs N (split n0 n2 N θ) := by
  have hpt : ∀ (i : Fin n2) (a : Fin m),
      outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs θ (i, a) =
        √(σb ^ 2) * θ (idx n0 n2 N (.inl i)) +
          ∑ j : Fin N, √(σw ^ 2 / N) * θ (idx n0 n2 N (.inr (j, .inr i))) *
            φ (√(σb ^ 2) * θ (idx n0 n2 N (.inr (j, .inl none))) +
              ∑ k : Fin n0, √(σw ^ 2 / n0) * θ (idx n0 n2 N (.inr (j, .inl (some k)))) *
                xs a k) := by
    intro i a
    simp [outputVector, mlpZ, mlpBias, mlpWeight, idx]
    rfl
  ext ⟨i, a⟩
  rw [hpt]
  simp only [Zhat, biasVec, unitVec, pre_eq, split, PiLp.add_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum,
    Real.sqrt_div' _ (Nat.cast_nonneg N)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_eq_mul_inv]
  ring

lemma memLp_phi_pre (hφ : Measurable φ)
    (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal)) (a : Fin m) :
    MemLp (fun u => φ (pre σb σw xs a u)) 2
      (Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1) := by
  have hm := measurable_pre σb σw xs a
  refine (memLp_two_iff_integrable_sq (hφ.comp hm).aestronglyMeasurable).2 ?_
  have h := hφ2 a
  rw [← preLaw σb σw φ xs a, integrable_map_measure (by fun_prop) hm.aemeasurable] at h
  exact h

lemma memLp_eval {κ : Type*} [Fintype κ] (i : κ) :
    MemLp (fun w : κ → ℝ => w i) 2 (Measure.pi fun _ : κ => gaussianReal 0 1) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ i)

/-- the directional projection `⟪unitVec, c⟫` of one hidden unit, on the split space. -/
noncomputable def unitX (c : Fin n2 × Fin m → ℝ)
    (p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ)) : ℝ :=
  ∑ ia, c ia * (√(σw ^ 2) * p.2 ia.1 * φ (pre σb σw xs ia.2 p.1))

/-- the first-layer second-moment kernel `E[φ(z_a) φ(z_b)]`. -/
noncomputable def Fker (a b : Fin m) : ℝ :=
  ∫ u, φ (pre σb σw xs a u) * φ (pre σb σw xs b u)
    ∂(Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1)

section moments

variable (hφ : Measurable φ)
    (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal))
include hφ hφ2

lemma integrable_term (a b : Fin m) (i j : Fin n2) :
    Integrable (fun p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ) =>
      (φ (pre σb σw xs a p.1) * φ (pre σb σw xs b p.1)) * (p.2 i * p.2 j))
      ((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) :=
  Integrable.mul_prod
    ((memLp_phi_pre σb σw φ xs hφ hφ2 a).integrable_mul (memLp_phi_pre σb σw φ xs hφ hφ2 b))
    ((memLp_eval i).integrable_mul (memLp_eval j))

lemma memLp_unit_term (c : Fin n2 × Fin m → ℝ) (ia : Fin n2 × Fin m) :
    MemLp (fun p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ) =>
      c ia * (√(σw ^ 2) * p.2 ia.1 * φ (pre σb σw xs ia.2 p.1))) 2
      ((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) := by
  have hmeas : AEStronglyMeasurable (fun p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ) =>
      c ia * (√(σw ^ 2) * p.2 ia.1 * φ (pre σb σw xs ia.2 p.1)))
      ((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) := by fun_prop
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have hs : √(σw ^ 2) ^ 2 = σw ^ 2 := Real.sq_sqrt (sq_nonneg σw)
  refine ((integrable_term σb σw φ xs hφ hφ2 ia.2 ia.2 ia.1 ia.1).const_mul
    (c ia ^ 2 * σw ^ 2)).congr (ae_of_all _ fun p => ?_)
  simp only
  linear_combination (-(c ia ^ 2 * φ (pre σb σw xs ia.2 p.1) ^ 2 * p.2 ia.1 ^ 2)) * hs

lemma memLp_unitX (c : Fin n2 × Fin m → ℝ) :
    MemLp (unitX σb σw φ xs c) 2
      ((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) :=
  memLp_finsetSum _ fun ia _ => memLp_unit_term σb σw φ xs hφ hφ2 c ia

lemma integral_unitX (c : Fin n2 × Fin m → ℝ) :
    ∫ p, unitX σb σw φ xs c p
      ∂((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) = 0 := by
  unfold unitX
  rw [integral_finsetSum _ fun ia _ =>
    (memLp_unit_term σb σw φ xs hφ hφ2 c ia).integrable one_le_two]
  refine Finset.sum_eq_zero fun ia _ => ?_
  have h := integral_prod_mul (μ := Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin n2 => gaussianReal 0 1)
    (fun u => φ (pre σb σw xs ia.2 u)) (fun w => w ia.1)
  simp only [integral_eval, integral_id_gaussianReal, mul_zero] at h
  have h2 : ∀ p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ),
      c ia * (√(σw ^ 2) * p.2 ia.1 * φ (pre σb σw xs ia.2 p.1)) =
        (c ia * √(σw ^ 2)) * (φ (pre σb σw xs ia.2 p.1) * p.2 ia.1) := fun p => by ring
  simp_rw [h2]
  rw [integral_const_mul, h, mul_zero]

lemma integral_unitX_sq (c : Fin n2 × Fin m → ℝ) :
    ∫ p, unitX σb σw φ xs c p ^ 2
      ∂((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)) =
      ∑ ia, ∑ jb, c ia * c jb *
        (if ia.1 = jb.1 then σw ^ 2 * Fker σb σw φ xs ia.2 jb.2 else 0) := by
  have hs : √(σw ^ 2) * √(σw ^ 2) = σw ^ 2 := Real.mul_self_sqrt (sq_nonneg σw)
  have hexp : ∀ p : (Option (Fin n0) → ℝ) × (Fin n2 → ℝ), unitX σb σw φ xs c p ^ 2 =
      ∑ ia, ∑ jb, (c ia * c jb * σw ^ 2) *
        ((φ (pre σb σw xs ia.2 p.1) * φ (pre σb σw xs jb.2 p.1)) * (p.2 ia.1 * p.2 jb.1)) := by
    intro p
    unfold unitX
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ia _ => Finset.sum_congr rfl fun jb _ => ?_
    linear_combination (c ia * c jb * (φ (pre σb σw xs ia.2 p.1) * φ (pre σb σw xs jb.2 p.1)) *
      (p.2 ia.1 * p.2 jb.1)) * hs
  simp_rw [hexp]
  rw [integral_finsetSum _ fun ia _ => integrable_finsetSum _ fun jb _ =>
    (integrable_term σb σw φ xs hφ hφ2 ia.2 jb.2 ia.1 jb.1).const_mul _]
  refine Finset.sum_congr rfl fun ia _ => ?_
  rw [integral_finsetSum _ fun jb _ =>
    (integrable_term σb σw φ xs hφ hφ2 ia.2 jb.2 ia.1 jb.1).const_mul _]
  refine Finset.sum_congr rfl fun jb _ => ?_
  have h := integral_prod_mul (μ := Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin n2 => gaussianReal 0 1)
    (fun u => φ (pre σb σw xs ia.2 u) * φ (pre σb σw xs jb.2 u)) (fun w => w ia.1 * w jb.1)
  rw [integral_const_mul, h, integral_eval_mul_eval]
  split_ifs <;> simp [Fker]; ring

end moments


section charfun

variable (hφ : Measurable φ)
include hφ

@[fun_prop] lemma measurable_unitVec :
    Measurable (fun h : Option (Fin n0) ⊕ Fin n2 → ℝ => unitVec σb σw φ xs h) := by
  unfold unitVec; fun_prop

omit hφ in
@[fun_prop] lemma measurable_biasVec :
    Measurable (fun b : Fin n2 → ℝ => biasVec σb (m := m) b) := by
  unfold biasVec; fun_prop

lemma measurable_Zhat (N : ℕ) : Measurable (Zhat σb σw φ xs (n2 := n2) N) := by
  unfold Zhat; fun_prop

@[fun_prop] lemma measurable_unitX (c : Fin n2 × Fin m → ℝ) :
    Measurable (unitX σb σw φ xs c) := by
  unfold unitX; fun_prop

lemma measurable_outputVector (N : ℕ) :
    Measurable (outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs) := by
  rw [show outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs =
      Zhat σb σw φ xs N ∘ split n0 n2 N from funext (outputVector_eq σb σw φ xs N)]
  exact (measurable_Zhat σb σw φ xs hφ N).comp (measurePreserving_split n0 n2 N).measurable

lemma unit_factor (t : EuclideanSpace ℝ (Fin n2 × Fin m)) (s : ℝ) :
    ∫ h, cexp (((s * ⟪unitVec σb σw φ xs h, t⟫ : ℝ) : ℂ) * I)
        ∂(Measure.pi fun _ : Option (Fin n0) ⊕ Fin n2 => gaussianReal 0 1) =
      charFun (((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)).map (unitX σb σw φ xs t.ofLp)) s := by
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Option (Fin n0) ⊕ Fin n2 => ℝ) (fun _ => gaussianReal 0 1)
  rw [charFun_apply_real, integral_map (measurable_unitX σb σw φ xs hφ _).aemeasurable
    (by fun_prop), ← hmp.integral_comp']
  congr 1 with p
  rw [← Complex.ofReal_mul]
  congr 3

omit hφ in
lemma charFun_bias (t : EuclideanSpace ℝ (Fin n2 × Fin m)) :
    charFun ((Measure.pi fun _ : Fin n2 => gaussianReal 0 1).map (biasVec σb (m := m))) t =
      cexp (-(∑ i, (√(σb ^ 2) * ∑ a, t (i, a)) ^ 2 : ℝ) / 2) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have h : ∀ b : Fin n2 → ℝ,
      ⟪biasVec σb (m := m) b, t⟫ = ∑ i, (√(σb ^ 2) * ∑ a, t (i, a)) * b i := by
    intro b
    simp only [biasVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  simp_rw [h]
  exact integral_cexp_linear _

lemma charFun_law (N : ℕ) (t : EuclideanSpace ℝ (Fin n2 × Fin m)) :
    charFun ((stdGaussianParams (uniformWidths n0 n2 1 N) 1).map
        (outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs)) t =
      charFun ((Measure.pi fun _ : Fin n2 => gaussianReal 0 1).map (biasVec σb (m := m))) t *
        charFun (((Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin n2 => gaussianReal 0 1)).map (unitX σb σw φ xs t.ofLp))
          ((√(N : ℝ))⁻¹ * 1) ^ N := by
  have hOV : outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs =
      Zhat σb σw φ xs N ∘ split n0 n2 N := funext (outputVector_eq σb σw φ xs N)
  have hmp := measurePreserving_split n0 n2 N
  have hZ := measurable_Zhat σb σw φ xs hφ (n2 := n2) N
  rw [hOV, ← Measure.map_map hZ hmp.measurable, hmp.map_eq, charFun_apply,
    integral_map hZ.aemeasurable (by fun_prop)]
  have hsplit : ∀ p : (Fin n2 → ℝ) × (Fin N → Option (Fin n0) ⊕ Fin n2 → ℝ),
      cexp (((⟪Zhat σb σw φ xs N p, t⟫ : ℝ) : ℂ) * I) =
        cexp (((⟪biasVec σb (m := m) p.1, t⟫ : ℝ) : ℂ) * I) *
          ∏ j, cexp ((((√(N : ℝ))⁻¹ * 1 * ⟪unitVec σb σw φ xs (p.2 j), t⟫ : ℝ) : ℂ) * I) := by
    intro p
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    simp only [Zhat, inner_add_left, real_inner_smul_left, sum_inner, Finset.mul_sum, mul_one]
    push_cast
    rw [add_mul, Finset.sum_mul]
  simp_rw [hsplit]
  have h1 := integral_prod_mul (μ := Measure.pi fun _ : Fin n2 => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N =>
      Measure.pi fun _ : Option (Fin n0) ⊕ Fin n2 => gaussianReal 0 1)
    (fun b => cexp (((⟪biasVec σb (m := m) b, t⟫ : ℝ) : ℂ) * I))
    (fun h => ∏ j, cexp ((((√(N : ℝ))⁻¹ * 1 * ⟪unitVec σb σw φ xs (h j), t⟫ : ℝ) : ℂ) * I))
  rw [h1, integral_fintype_prod_eq_prod (fun _ h =>
      cexp ((((√(N : ℝ))⁻¹ * 1 * ⟪unitVec σb σw φ xs h, t⟫ : ℝ) : ℂ) * I)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, unit_factor σb σw φ xs hφ]
  congr 1
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]

end charfun

section quad

variable (hφ : Measurable φ)
include hφ

lemma K2_eq (a b : Fin m) :
    nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b) = σb ^ 2 + σw ^ 2 * Fker σb σw φ xs a b := by
  rw [Fker, pairAvg_eq σb σw φ xs hφ a b]
  rfl

lemma quad_S (x : Fin n2 × Fin m → ℝ) :
    x ⬝ᵥ (blockDiagCov (k := n2) fun a b => nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b)) *ᵥ x =
      ∑ ia, ∑ jb, x ia * x jb * (if ia.1 = jb.1 then σb ^ 2 else 0) +
      ∑ ia, ∑ jb, x ia * x jb *
        (if ia.1 = jb.1 then σw ^ 2 * Fker σb σw φ xs ia.2 jb.2 else 0) := by
  simp only [dotProduct, Matrix.mulVec, blockDiagCov, Matrix.of_apply, K2_eq σb σw φ xs hφ,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ia _ => Finset.sum_congr rfl fun jb _ => ?_
  split_ifs <;> ring

omit hφ in
lemma bias_quad (x : Fin n2 × Fin m → ℝ) :
    ∑ i, (√(σb ^ 2) * ∑ a, x (i, a)) ^ 2 =
      ∑ ia, ∑ jb, x ia * x jb * (if ia.1 = jb.1 then σb ^ 2 else 0) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, Real.sq_sqrt (sq_nonneg σb), pow_two (∑ a, x (i, a)), Finset.sum_mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
    (by simp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [if_true]
  ring

lemma S_psd (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal)) :
    (blockDiagCov (k := n2) fun a b =>
      nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext ia jb
    simp only [Matrix.conjTranspose_apply, star_trivial, blockDiagCov, Matrix.of_apply,
      K2_eq σb σw φ xs hφ]
    by_cases h : ia.1 = jb.1
    · rw [if_pos h.symm, if_pos h, Fker, Fker]
      congr 2
      exact integral_congr_ae (ae_of_all _ fun u => mul_comm _ _)
    · rw [if_neg (Ne.symm h), if_neg h]
  · simp only [star_trivial]
    rw [quad_S σb σw φ xs hφ, ← bias_quad, ← integral_unitX_sq σb σw φ xs hφ hφ2 x]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (integral_nonneg fun _ => sq_nonneg _)

end quad

theorem nngp_main (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (n0 n2 m : ℕ) (xs : Fin m → Fin n0 → ℝ)
    (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n2 × Fin m)) ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ, g (outputVector (σb ^ 2) (σw ^ 2) φ
          (uniformWidths_last n0 n2 1 N) xs θ)
        ∂(stdGaussianParams (uniformWidths n0 n2 1 N) 1))
      Filter.atTop
      (nhds (∫ v, g v ∂(multivariateGaussian 0
        (blockDiagCov (k := n2) fun a b => nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b))))) := by
  have hS := S_psd σb σw φ xs hφ hφ2 (n2 := n2)
  let μN : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n2 × Fin m)) := fun N =>
    ⟨(stdGaussianParams (uniformWidths n0 n2 1 N) 1).map
      (outputVector (σb ^ 2) (σw ^ 2) φ (uniformWidths_last n0 n2 1 N) xs),
      Measure.isProbabilityMeasure_map (measurable_outputVector σb σw φ xs hφ N).aemeasurable⟩
  let μ0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin n2 × Fin m)) :=
    ⟨multivariateGaussian 0 (blockDiagCov (k := n2) fun a b =>
      nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b)), inferInstance⟩
  have hconv : Tendsto μN atTop (𝓝 μ0) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simp only [μN, μ0, ProbabilityMeasure.coe_mk]
    simp_rw [charFun_law σb σw φ xs hφ _ t]
    rw [charFun_multivariateGaussian hS, charFun_bias]
    have h1 := tendsto_charFun_pow_var
      (P := (Measure.pi fun _ : Option (Fin n0) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n2 => gaussianReal 0 1))
      (measurable_unitX σb σw φ xs hφ t.ofLp).aemeasurable
      (memLp_unitX σb σw φ xs hφ hφ2 t.ofLp) (integral_unitX σb σw φ xs hφ hφ2 t.ofLp)
      (integral_unitX_sq σb σw φ xs hφ hφ2 t.ofLp) 1
    convert tendsto_const_nhds.mul h1 using 2
    rw [← Complex.exp_add]
    congr 1
    rw [quad_S σb σw φ xs hφ, ← bias_quad]
    simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub]
    push_cast
    ring
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv g
  simp only [μN, μ0, ProbabilityMeasure.coe_mk] at this
  refine this.congr fun N => ?_
  rw [integral_map (measurable_outputVector σb σw φ xs hφ N).aemeasurable
    g.continuous.aestronglyMeasurable]

end LesHouchesWidth

open LesHouchesWidth MeasureTheory ProbabilityTheory in
theorem solution (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (n0 n2 m : ℕ) (xs : Fin m → Fin n0 → ℝ)
    (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n2 × Fin m)) ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ, g (outputVector (σb ^ 2) (σw ^ 2) φ
          (uniformWidths_last n0 n2 1 N) xs θ)
        ∂(stdGaussianParams (uniformWidths n0 n2 1 N) 1))
      Filter.atTop
      (nhds (∫ v, g v ∂(multivariateGaussian 0
        (blockDiagCov (k := n2) fun a b => nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b))))) := by
  exact nngp_main σb σw φ hφ n0 n2 m xs hφ2 g
