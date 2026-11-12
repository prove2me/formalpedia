-- Prove2me | solution 1 for HindsightGain.Uniform.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:33:29.347908+00:00
-- url     : https://prove2.me/submissions/6ce86cf7-7a3a-4a62-9af6-280f9edd672c

import Mathlib
import Definitions.Def_HindsightGain_Uniform_fluctuations
import Definitions.Def_HindsightGain_Uniform_rademacher
import Theorems.Thm_HindsightGain_Uniform_theorem_7
import Theorems.Thm_variance_le_half_sum_resample_sq

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

/-- Frobenius norm of the row block. -/
def cF (M : Model n D r) (i : Fin n) : ℝ := Real.sqrt (rowFrobeniusSq M i)

lemma cF_nonneg (M : Model n D r) (i : Fin n) : 0 ≤ cF M i := Real.sqrt_nonneg _

lemma rowFrobeniusSq_nonneg (M : Model n D r) (i : Fin n) : 0 ≤ rowFrobeniusSq M i := by
  unfold rowFrobeniusSq
  positivity

lemma cF_sq (M : Model n D r) (i : Fin n) : cF M i ^ 2 = rowFrobeniusSq M i :=
  Real.sq_sqrt (rowFrobeniusSq_nonneg M i)

lemma rowBlock_apply (M : Model n D r) (i : Fin n) (w : Tensor (Fin n × Fin D) (r - 1))
    (a : Fin D) :
    rowBlock M i w a = ∑ b : Fin (r - 1) → Fin n × Fin D,
      symmetrized M (prepend (i, a) b) * w b := rfl

lemma rowBlock_sub (M : Model n D r) (i : Fin n) (w w' : Tensor (Fin n × Fin D) (r - 1)) :
    rowBlock M i (w - w') = rowBlock M i w - rowBlock M i w' := by
  ext a
  simp only [rowBlock_apply, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rowBlock_zero (M : Model n D r) (i : Fin n) :
    rowBlock M i 0 = 0 := by
  ext a
  simp [rowBlock_apply]

lemma rowBlock_norm_le (M : Model n D r) (i : Fin n) (w : Tensor (Fin n × Fin D) (r - 1)) :
    ‖rowBlock M i w‖ ≤ cF M i * ‖w‖ := by
  have h1 : ‖rowBlock M i w‖ ^ 2 ≤ (cF M i * ‖w‖) ^ 2 := by
    rw [mul_pow, cF_sq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, rowBlock_apply, rowFrobeniusSq]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (cF_nonneg _ _) (norm_nonneg _))
    two_ne_zero).1 h1

section support
variable {d : ℕ}

lemma support_bdd (K : Set (Vec d)) (hK : K ⊆ Metric.closedBall 0 1) (v : Vec d) :
    BddAbove ((fun u => inner ℝ u v) '' K) := by
  refine ⟨‖v‖, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have : ‖u‖ ≤ 1 := by simpa using hK hu
  calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
    _ ≤ 1 * ‖v‖ := by gcongr
    _ = ‖v‖ := one_mul _

lemma support_le_norm (K : Set (Vec d)) (hne : K.Nonempty) (hK : K ⊆ Metric.closedBall 0 1)
    (v : Vec d) : support K v ≤ ‖v‖ := by
  unfold support
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  have : ‖u‖ ≤ 1 := by simpa using hK hu
  calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
    _ ≤ 1 * ‖v‖ := by gcongr
    _ = ‖v‖ := one_mul _

lemma support_sub_le (K : Set (Vec d)) (hne : K.Nonempty) (hK : K ⊆ Metric.closedBall 0 1)
    (v v' : Vec d) : support K v - support K v' ≤ ‖v - v'‖ := by
  unfold support
  rw [sub_le_iff_le_add]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨u, hu, rfl⟩
  have h1 : inner ℝ u v' ≤ sSup ((fun u => inner ℝ u v') '' K) :=
    le_csSup (support_bdd K hK v') ⟨u, hu, rfl⟩
  have : ‖u‖ ≤ 1 := by simpa using hK hu
  have h2 : inner ℝ u (v - v') ≤ ‖v - v'‖ := by
    calc inner ℝ u (v - v') ≤ ‖u‖ * ‖v - v'‖ := real_inner_le_norm u _
      _ ≤ 1 * ‖v - v'‖ := by gcongr
      _ = ‖v - v'‖ := one_mul _
  have : inner ℝ u v = inner ℝ u v' + inner ℝ u (v - v') := by
    rw [← inner_add_right]; simp
  linarith

lemma support_zero (K : Set (Vec d)) (hne : K.Nonempty) (hK : K ⊆ Metric.closedBall 0 1) :
    support K 0 = 0 := by
  unfold support
  simp [hne]

lemma support_abs_le (K : Set (Vec d)) (hne : K.Nonempty) (hK : K ⊆ Metric.closedBall 0 1)
    (v : Vec d) : |support K v| ≤ ‖v‖ := by
  rw [abs_le]
  constructor
  · have := support_sub_le K hne hK 0 v
    rw [support_zero K hne hK] at this
    have h2 : ‖(0 : Vec d) - v‖ = ‖v‖ := by simp
    linarith
  · exact support_le_norm K hne hK v
end support

/-- the support function of the i-th body composed with the row block -/
def X (M : Model n D r) (i : Fin n) (w : Tensor (Fin n × Fin D) (r - 1)) : ℝ :=
  support (M.K i) (rowBlock M i w)

lemma X_abs_le (M : Model n D r) (i : Fin n) (w : Tensor (Fin n × Fin D) (r - 1)) :
    |X M i w| ≤ cF M i * ‖w‖ :=
  (support_abs_le _ (M.nonempty i) (M.unitBall i) _).trans (rowBlock_norm_le M i w)

lemma X_sub_le (M : Model n D r) (i : Fin n) (w w' : Tensor (Fin n × Fin D) (r - 1)) :
    X M i w - X M i w' ≤ cF M i * ‖w - w'‖ := by
  have := support_sub_le (M.K i) (M.nonempty i) (M.unitBall i) (rowBlock M i w) (rowBlock M i w')
  rw [← rowBlock_sub] at this
  exact this.trans (rowBlock_norm_le M i _)

lemma X_zero (M : Model n D r) (i : Fin n) : X M i 0 = 0 := by
  unfold X
  rw [rowBlock_zero]
  exact support_zero _ (M.nonempty i) (M.unitBall i)

/-- continuity of `X` -/
lemma X_continuous (M : Model n D r) (i : Fin n) : Continuous (X M i) := by
  have : LipschitzWith (Real.toNNReal (cF M i)) (X M i) := by
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (cF_nonneg _ _), abs_le]
    constructor
    · have := X_sub_le M i w' w
      rw [norm_sub_rev] at this
      linarith
    · exact X_sub_le M i w w'
  exact this.continuous

/-- the bilinear-ish functional -/
def G (M : Model n D r) (a : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1)) : ℝ :=
  ∑ i, a i * X M i w

/-- the maximum over the unit ball with centered weights `a` -/
def F0 (M : Model n D r) (a : Fin n → ℝ) : ℝ :=
  sSup (G M a '' Metric.closedBall 0 1)

def bnd (M : Model n D r) (a : Fin n → ℝ) : ℝ := ∑ i, |a i| * cF M i

lemma G_abs_le (M : Model n D r) (a : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1))
    (hw : ‖w‖ ≤ 1) : |G M a w| ≤ bnd M a := by
  unfold G bnd
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  gcongr
  exact (X_abs_le M i w).trans (by nlinarith [cF_nonneg M i])

lemma G_zero (M : Model n D r) (a : Fin n → ℝ) : G M a 0 = 0 := by
  simp [G, X_zero]

lemma G_bdd (M : Model n D r) (a : Fin n → ℝ) :
    BddAbove (G M a '' Metric.closedBall 0 1) := by
  refine ⟨bnd M a, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (le_abs_self _).trans (G_abs_le M a w (by simpa using hw))

lemma G_le_F0 (M : Model n D r) (a : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1))
    (hw : ‖w‖ ≤ 1) : G M a w ≤ F0 M a :=
  le_csSup (G_bdd M a) ⟨w, by simpa using hw, rfl⟩

lemma F0_le_of (M : Model n D r) (a : Fin n → ℝ) (t : ℝ)
    (h : ∀ w : Tensor (Fin n × Fin D) (r - 1), ‖w‖ ≤ 1 → G M a w ≤ t) : F0 M a ≤ t := by
  refine csSup_le ⟨G M a 0, 0, by simp, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  exact h w (by simpa using hw)

lemma F0_nonneg (M : Model n D r) (a : Fin n → ℝ) : 0 ≤ F0 M a := by
  have := G_le_F0 M a 0 (by simp)
  rwa [G_zero] at this

lemma F0_le_bnd (M : Model n D r) (a : Fin n → ℝ) : F0 M a ≤ bnd M a :=
  F0_le_of M a _ fun w hw => (le_abs_self _).trans (G_abs_le M a w hw)

lemma F0_abs_le (M : Model n D r) (a : Fin n → ℝ) : |F0 M a| ≤ bnd M a := by
  rw [abs_of_nonneg (F0_nonneg M a)]; exact F0_le_bnd M a

lemma G_sub (M : Model n D r) (a b : Fin n → ℝ) (w : Tensor (Fin n × Fin D) (r - 1)) :
    G M a w = G M b w + ∑ i, (a i - b i) * X M i w := by
  simp only [G, sub_mul, Finset.sum_sub_distrib]; ring

lemma F0_sub_le (M : Model n D r) (a b : Fin n → ℝ) :
    F0 M a - F0 M b ≤ bnd M (a - b) := by
  rw [sub_le_iff_le_add]
  refine F0_le_of M a _ fun w hw => ?_
  rw [G_sub M a b w]
  have h1 := G_le_F0 M b w hw
  have h2 : ∑ i, (a i - b i) * X M i w ≤ bnd M (a - b) := by
    have := G_abs_le M (a - b) w hw
    exact (le_abs_self _).trans (by simpa [G] using this)
  linarith

lemma F0_lipschitz (M : Model n D r) :
    LipschitzWith (Real.toNNReal (∑ i, cF M i)) (F0 M) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => cF_nonneg _ _),
    abs_le]
  have key : ∀ a b : Fin n → ℝ, bnd M (a - b) ≤ (∑ i, cF M i) * ‖a - b‖ := by
    intro a b
    unfold bnd
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm]
    gcongr
    · exact cF_nonneg _ _
    · simpa using norm_le_pi_norm (a - b) i
  constructor
  · have := F0_sub_le M b a
    have h2 := key b a
    rw [norm_sub_rev] at h2
    have : bnd M (b - a) = bnd M (b - a) := rfl
    linarith
  · exact (F0_sub_le M a b).trans (key a b)

lemma F0_continuous (M : Model n D r) : Continuous (F0 M) := (F0_lipschitz M).continuous

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

lemma extendedMean_coe {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f μ) :
    extendedMean μ (fun ω => (f ω : EReal)) = ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold extendedMean
  have e1 : ∀ ω, ((f ω : ℝ) : EReal).toENNReal = ENNReal.ofReal (f ω) :=
    fun ω => EReal.real_coe_toENNReal _
  have e2 : ∀ ω, (-((f ω : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-f ω) := by
    intro ω
    rw [← EReal.coe_neg]; exact EReal.real_coe_toENNReal _
  simp only [e1, e2]
  have hA : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≠ ⊤ := ((lintegral_mono fun ω => Real.ofReal_le_enorm (f ω)).trans_lt hf.2).ne
  have hB : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ ≠ ⊤ := ((lintegral_mono fun ω => Real.ofReal_le_enorm (-f ω)).trans_lt hf.neg.2).ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    EReal.coe_ennreal_toReal hA, EReal.coe_ennreal_toReal hB]


lemma extendedMean_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → EReal)
    (Bd : Ω → ℝ) (hB : Integrable Bd μ) (h0 : ∀ ω, 0 ≤ Bd ω)
    (hY : ∀ ω, Y ω ≤ (Bd ω : EReal)) :
    extendedMean μ Y ≤ ((∫ ω, Bd ω ∂μ : ℝ) : EReal) := by
  unfold extendedMean
  have hA : ∫⁻ ω, (Y ω).toENNReal ∂μ ≤ ENNReal.ofReal (∫ ω, Bd ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hB (Filter.Eventually.of_forall h0)]
    refine lintegral_mono fun ω => ?_
    rw [← EReal.real_coe_toENNReal]
    exact EReal.toENNReal_le_toENNReal (hY ω)
  have h1 : (((∫⁻ ω, (Y ω).toENNReal ∂μ : ℝ≥0∞)) : EReal) ≤
      ((ENNReal.ofReal (∫ ω, Bd ω ∂μ) : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 hA
  have h2 : ((ENNReal.ofReal (∫ ω, Bd ω ∂μ) : ℝ≥0∞) : EReal) = ((∫ ω, Bd ω ∂μ : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left]
    exact integral_nonneg h0
  calc _ ≤ (((∫⁻ ω, (Y ω).toENNReal ∂μ : ℝ≥0∞)) : EReal) - 0 :=
        EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
    _ ≤ _ := by rw [sub_zero]; exact h1.trans_eq h2

/-- Finitely supported coefficient sequences: the sign series is the finite sum. -/
lemma signSeries_eq_sum (a : SequenceL2) (N : ℕ) (ha : ∀ k, N ≤ k → a k = 0) (ε : ℕ → Bool) :
    signSeries a ε = ∑ k ∈ Finset.range N, sign (ε k) * a k := by
  have ht : Tendsto (fun N' : ℕ => ∑ k ∈ Finset.range N', sign (ε k) * a k) atTop
      (𝓝 (∑ k ∈ Finset.range N, sign (ε k) * a k)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun N' hN' => ?_
    refine (Finset.sum_subset (Finset.range_subset_range.2 hN') fun k _ hk => ?_).symm
    simp only [Finset.mem_range, not_lt] at hk
    rw [ha k hk, mul_zero]
  have h : ∃ l : ℝ, Tendsto (fun N' : ℕ => ∑ k ∈ Finset.range N', sign (ε k) * a k) atTop (𝓝 l) :=
    ⟨_, ht⟩
  unfold signSeries
  rw [dif_pos h]
  exact tendsto_nhds_unique (Classical.choose_spec h) ht

variable {D : ℕ}

def embFun (v : EuclideanSpace ℝ (Fin D)) : ℕ → ℝ := fun k => if h : k < D then v ⟨k, h⟩ else 0

lemma embFun_mem (v : EuclideanSpace ℝ (Fin D)) : Memℓp (fun k => embFun v k) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_of_ne_finset_zero (s := Finset.range D) fun k hk => ?_
  simp only [Finset.mem_range, not_lt] at hk
  simp [embFun, not_lt.2 hk]

def emb (v : EuclideanSpace ℝ (Fin D)) : SequenceL2 := ⟨embFun v, embFun_mem v⟩

lemma emb_apply (v : EuclideanSpace ℝ (Fin D)) (k : ℕ) : emb v k = embFun v k := rfl

lemma emb_zero_of_le (v : EuclideanSpace ℝ (Fin D)) (k : ℕ) (hk : D ≤ k) : emb v k = 0 := by
  simp [emb_apply, embFun, not_lt.2 hk]

lemma emb_sub (v v' : EuclideanSpace ℝ (Fin D)) : emb (v - v') = emb v - emb v' := by
  ext k
  simp only [emb_apply, embFun, lp.coeFn_sub, Pi.sub_apply, PiLp.sub_apply]
  split_ifs <;> simp

lemma emb_norm (v : EuclideanSpace ℝ (Fin D)) : ‖emb v‖ = ‖v‖ := by
  have h1 : ‖emb v‖ ^ (2:ℝ) = ∑' k, ‖emb v k‖ ^ (2:ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (emb v)
  rw [tsum_eq_sum (s := Finset.range D) (fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    simp [emb_zero_of_le v k hk])] at h1
  have h2 : ‖v‖ ^ (2:ℝ) = ∑ k ∈ Finset.range D, ‖emb v k‖ ^ (2:ℝ) := by
    rw [Real.rpow_two, EuclideanSpace.norm_sq_eq, ← Fin.sum_univ_eq_sum_range
      (fun k => ‖emb v k‖ ^ (2:ℝ))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [emb_apply, embFun, Real.rpow_two]
  have h3 : ‖emb v‖ ^ (2:ℝ) = ‖v‖ ^ (2:ℝ) := h1.trans h2.symm
  rw [Real.rpow_two, Real.rpow_two] at h3
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

open Classical

variable {J : Type} [Countable J]

instance signLaw_prob : IsProbabilityMeasure (signLaw J) := by
  unfold signLaw; infer_instance

lemma sign_sq (b : Bool) : sign b * sign b = 1 := by
  cases b <;> simp [sign]

lemma measurable_sign : Measurable sign := measurable_from_top

lemma integral_sign_eval (j : J) : ∫ ε, sign (ε j) ∂(signLaw J) = 0 := by
  have h := Measure.infinitePi_map_eval (fun _ : J => (PMF.uniformOfFintype Bool).toMeasure) j
  have : ∫ ε, sign (ε j) ∂(signLaw J) = ∫ b, sign b ∂((signLaw J).map (fun x => x j)) := by
    rw [integral_map (measurable_pi_apply j).aemeasurable measurable_sign.aestronglyMeasurable]
  rw [this]
  unfold signLaw
  rw [h, integral_fintype Integrable.of_finite]
  simp [Measure.real, sign]


lemma abs_sign_le (b : Bool) : |sign b| ≤ 1 := by cases b <;> simp [sign]

lemma measurable_sign_eval (j : J) : Measurable (fun ε : J → Bool => sign (ε j)) :=
  measurable_sign.comp (measurable_pi_apply j)

lemma integrable_sign_eval_mul (j k : J) :
    Integrable (fun ε : J → Bool => sign (ε j) * sign (ε k)) (signLaw J) := by
  refine Integrable.of_bound ((measurable_sign_eval j).mul (measurable_sign_eval k)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |sign (ε j)| * |sign (ε k)| ≤ 1 * 1 := by
        gcongr <;> first | exact abs_sign_le _ | positivity
    _ = 1 := one_mul 1

lemma integral_sign_mul (j k : J) :
    ∫ ε, sign (ε j) * sign (ε k) ∂(signLaw J) = if j = k then 1 else 0 := by
  split_ifs with h
  · subst h
    simp only [sign_sq, integral_const, probReal_univ, smul_eq_mul, mul_one]
  · have hind : IndepFun (fun ε : J → Bool => sign (ε j)) (fun ε : J → Bool => sign (ε k))
        (signLaw J) :=
      (iIndepFun_infinitePi (P := fun _ : J => (PMF.uniformOfFintype Bool).toMeasure)
        (X := fun _ b => sign b) (fun _ => measurable_sign)).indepFun h
    have := hind.integral_mul_eq_mul_integral (measurable_sign_eval j).aestronglyMeasurable
      (measurable_sign_eval k).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, integral_sign_eval j, zero_mul]

/-- second moment of a Rademacher sum over distinct coordinates -/
lemma integral_sign_sum_sq {K : Type} [Fintype K] (e : K → J) (he : Function.Injective e)
    (c : K → ℝ) :
    ∫ ε, (∑ x, sign (ε (e x)) * c x) ^ 2 ∂(signLaw J) = ∑ x, c x ^ 2 := by
  have h1 : ∀ ε : J → Bool, (∑ x, sign (ε (e x)) * c x) ^ 2 =
      ∑ x, ∑ y, (sign (ε (e x)) * sign (ε (e y))) * (c x * c y) := by
    intro ε
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  simp_rw [h1]
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_sign_eval_mul (e x) (e y)).mul_const _]
  simp_rw [integral_finsetSum _ fun y _ => (integrable_sign_eval_mul (e _) (e y)).mul_const _,
    integral_mul_const, integral_sign_mul, he.eq_iff]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [sq]


lemma integral_sqrt_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Q : Ω → ℝ) (hQm : Measurable Q) (hQi : Integrable Q μ) (h0 : ∀ ω, 0 ≤ Q ω) :
    ∫ ω, Real.sqrt (Q ω) ∂μ ≤ Real.sqrt (∫ ω, Q ω ∂μ) := by
  have hYm : Measurable fun ω => Real.sqrt (Q ω) := hQm.sqrt
  have hY : MemLp (fun ω => Real.sqrt (Q ω)) 2 μ := by
    refine (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 ?_
    refine hQi.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Real.sq_sqrt (h0 ω)]
  have h1 := variance_nonneg (fun ω => Real.sqrt (Q ω)) μ
  rw [variance_eq_sub hY] at h1
  have h2 : μ[(fun ω => Real.sqrt (Q ω)) ^ 2] = ∫ ω, Q ω ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [Real.sq_sqrt (h0 ω)]
  rw [h2] at h1
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

abbrev TT (n D r : ℕ) := Tensor (Fin n × Fin D) (r - 1)

/-- coefficient of the sign `ε (i,k)` in the `b`-th coordinate. -/
def coef (M : Model n D r) (a : Fin n → ℝ) (x : Fin n × Fin D) (b : Fin (r - 1) → Fin n × Fin D) : ℝ :=
  a x.1 * symmetrized M (prepend (x.1, x.2) b)

def gsum (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool)
    (b : Fin (r - 1) → Fin n × Fin D) : ℝ :=
  ∑ x : Fin n × Fin D, sign (ε (x.1, (x.2 : ℕ))) * coef M a x b

def QQ (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) : ℝ :=
  ∑ b, gsum M a ε b ^ 2

lemma QQ_nonneg (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) : 0 ≤ QQ M a ε :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gsum_measurable (M : Model n D r) (a : Fin n → ℝ) (b : Fin (r - 1) → Fin n × Fin D) :
    Measurable fun ε : Fin n × ℕ → Bool => gsum M a ε b := by
  unfold gsum
  refine Finset.measurable_sum _ fun x _ => ?_
  exact (measurable_sign_eval (x.1, (x.2 : ℕ))).mul_const _

lemma QQ_measurable (M : Model n D r) (a : Fin n → ℝ) : Measurable (QQ M a) := by
  unfold QQ
  exact Finset.measurable_sum _ fun b _ => (gsum_measurable M a b).pow_const 2

lemma gsum_abs_le (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool)
    (b : Fin (r - 1) → Fin n × Fin D) :
    |gsum M a ε b| ≤ ∑ x : Fin n × Fin D, |coef M a x b| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  calc |sign (ε (x.1, (x.2 : ℕ)))| * |coef M a x b| ≤ 1 * |coef M a x b| := by
        gcongr; exact abs_sign_le _
    _ = _ := one_mul _

lemma QQ_le (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) :
    QQ M a ε ≤ ∑ b, (∑ x : Fin n × Fin D, |coef M a x b|) ^ 2 := by
  unfold QQ
  refine Finset.sum_le_sum fun b _ => ?_
  calc gsum M a ε b ^ 2 = |gsum M a ε b| ^ 2 := (sq_abs _).symm
    _ ≤ _ := by gcongr; exact gsum_abs_le M a ε b

lemma QQ_integral (M : Model n D r) (a : Fin n → ℝ) :
    ∫ ε, QQ M a ε ∂(signLaw (Fin n × ℕ)) = ∑ i, a i ^ 2 * rowFrobeniusSq M i := by
  unfold QQ
  rw [integral_finsetSum]
  · have e : Function.Injective (fun x : Fin n × Fin D => (x.1, (x.2 : ℕ))) := by
      intro x y h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Fin.ext h.2)
    have : ∀ b, ∫ ε, gsum M a ε b ^ 2 ∂(signLaw (Fin n × ℕ)) = ∑ x : Fin n × Fin D, coef M a x b ^ 2 :=
      fun b => integral_sign_sum_sq (fun x : Fin n × Fin D => (x.1, (x.2 : ℕ))) e (fun x => coef M a x b)
    simp_rw [this]
    rw [Finset.sum_comm]
    simp only [coef, mul_pow, ← Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [rowFrobeniusSq, ← Finset.mul_sum]
  · intro b _
    refine Integrable.of_bound (C := (∑ x : Fin n × Fin D, |coef M a x b|) ^ 2)
      ((gsum_measurable M a b).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ε => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc gsum M a ε b ^ 2 = |gsum M a ε b| ^ 2 := (sq_abs _).symm
      _ ≤ _ := by gcongr; exact gsum_abs_le M a ε b


def Bd (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) : ℝ := Real.sqrt (QQ M a ε)

lemma Bd_nonneg (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) : 0 ≤ Bd M a ε :=
  Real.sqrt_nonneg _

lemma Bd_integrable (M : Model n D r) (a : Fin n → ℝ) :
    Integrable (Bd M a) (signLaw (Fin n × ℕ)) := by
  refine Integrable.of_bound (QQ_measurable M a).sqrt.aestronglyMeasurable
    (Real.sqrt (∑ b, (∑ x : Fin n × Fin D, |coef M a x b|) ^ 2))
    (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Bd_nonneg M a ε)]
  exact Real.sqrt_le_sqrt (QQ_le M a ε)

lemma Bd_integral_le (M : Model n D r) (a : Fin n → ℝ) :
    ∫ ε, Bd M a ε ∂(signLaw (Fin n × ℕ)) ≤ Real.sqrt (∑ i, a i ^ 2 * rowFrobeniusSq M i) := by
  have hi : Integrable (QQ M a) (signLaw (Fin n × ℕ)) :=
    Integrable.of_bound (QQ_measurable M a).aestronglyMeasurable
      (∑ b, (∑ x : Fin n × Fin D, |coef M a x b|) ^ 2)
      (Filter.Eventually.of_forall fun ε => by
        rw [Real.norm_eq_abs, abs_of_nonneg (QQ_nonneg M a ε)]; exact QQ_le M a ε)
  have := integral_sqrt_le (signLaw (Fin n × ℕ)) (QQ M a) (QQ_measurable M a) hi
    (QQ_nonneg M a)
  rwa [QQ_integral] at this

lemma phi_value (M : Model n D r) (a : Fin n → ℝ) (ε : Fin n × ℕ → Bool) (w : TT n D r) :
    ∑ i, signSeries (a i • emb (rowBlock M i w)) (fun k => ε (i, k)) =
      ∑ b, w b * gsum M a ε b := by
  have h1 : ∀ i, signSeries (a i • emb (rowBlock M i w)) (fun k => ε (i, k)) =
      ∑ j : Fin D, sign (ε (i, (j : ℕ))) * (a i * ∑ b, symmetrized M (prepend (i, j) b) * w b) := by
    intro i
    rw [signSeries_eq_sum _ D (fun k hk => by simp [emb_zero_of_le _ k hk]),
      Finset.sum_range (fun k => sign (ε (i, k)) * (a i • emb (rowBlock M i w)) k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [emb_apply, embFun, rowBlock_apply]
  simp_rw [h1]
  unfold gsum coef
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring


lemma cs_ball (w : TT n D r) (hw : ‖w‖ ≤ 1) (g : (Fin (r - 1) → Fin n × Fin D) → ℝ) :
    ∑ b, w b * g b ≤ Real.sqrt (∑ b, g b ^ 2) := by
  have h1 : (∑ b, w b * g b) ^ 2 ≤ (∑ b, w b ^ 2) * ∑ b, g b ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 : ∑ b, w b ^ 2 ≤ 1 := by
    have := EuclideanSpace.norm_sq_eq w
    simp only [Real.norm_eq_abs, sq_abs] at this
    rw [← this]
    nlinarith [norm_nonneg w]
  have h3 : 0 ≤ ∑ b, g b ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact (le_abs_self _).trans (Real.abs_le_sqrt (h1.trans (by nlinarith)))

lemma vector_le (M : Model n D r) (a : Fin n → ℝ) (S : ℕ → TT n D r) (hS : ∀ k, ‖S k‖ ≤ 1) :
    vectorComplexity n (fun i k => a i • emb (rowBlock M i (S k))) ≤
      ((∫ ε, Bd M a ε ∂(signLaw (Fin n × ℕ)) : ℝ) : EReal) := by
  unfold vectorComplexity
  refine extendedMean_le _ _ (Bd M a) (Bd_integrable M a) (Bd_nonneg M a) fun ε => ?_
  refine iSup_le fun k => ?_
  rw [EReal.coe_le_coe_iff, phi_value]
  exact cs_ball (S k) (hS k) _

lemma G_continuous (M : Model n D r) (a : Fin n → ℝ) : Continuous (G M a) := by
  unfold G
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (X_continuous M i)

lemma sup_dense (M : Model n D r) (a' : Fin n → ℝ)
    (S : ℕ → Metric.closedBall (0 : TT n D r) 1) (hd : DenseRange S) :
    ⨆ k, ((G M a' (S k).1 : ℝ) : EReal) = ((F0 M a' : ℝ) : EReal) := by
  have hle : ⨆ k, ((G M a' (S k).1 : ℝ) : EReal) ≤ ((F0 M a' : ℝ) : EReal) :=
    iSup_le fun k => EReal.coe_le_coe_iff.2 (G_le_F0 M a' _ (mem_closedBall_zero_iff.1 (S k).2))
  refine le_antisymm hle ?_
  generalize hT : (⨆ k, ((G M a' (S k).1 : ℝ) : EReal)) = T at *
  have hall : ∀ w : Metric.closedBall (0 : TT n D r) 1, ((G M a' w.1 : ℝ) : EReal) ≤ T := by
    intro w
    refine hd.induction_on w (isClosed_le ?_ continuous_const) fun k => ?_
    · exact continuous_coe_real_ereal.comp ((G_continuous M a').comp continuous_subtype_val)
    · rw [← hT]; exact le_iSup (fun k => ((G M a' (S k).1 : ℝ) : EReal)) k
  have hbot : T ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hall (S 0))
  have htop : T ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  induction T using EReal.rec with
  | bot => exact absurd rfl hbot
  | top => exact absurd rfl htop
  | coe t =>
    refine EReal.coe_le_coe_iff.2 (F0_le_of M a' t fun w hw => ?_)
    exact EReal.coe_le_coe_iff.1 (hall ⟨w, by simpa using hw⟩)

lemma scalar_eq (M : Model n D r) (a : Fin n → ℝ)
    (S : ℕ → Metric.closedBall (0 : TT n D r) 1) (hd : DenseRange S) :
    scalarComplexity n (fun i k => a i * X M i (S k).1) =
      ((∫ ε, F0 M (fun i => sign (ε i) * a i) ∂(signLaw (Fin n)) : ℝ) : EReal) := by
  unfold scalarComplexity
  have h : (fun ε : Fin n → Bool => ⨆ k, ((∑ i, sign (ε i) * (a i * X M i (S k).1) : ℝ) : EReal)) =
      fun ε => ((F0 M (fun i => sign (ε i) * a i) : ℝ) : EReal) := by
    funext ε
    rw [← sup_dense M (fun i => sign (ε i) * a i) S hd]
    refine iSup_congr fun k => ?_
    have e : (∑ i, sign (ε i) * (a i * X M i (S k).1)) =
        G M (fun i => sign (ε i) * a i) (S k).1 :=
      Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    rw [e]
  rw [h]
  refine extendedMean_coe _ _ ?_
  have hm : Measurable fun ε : Fin n → Bool => F0 M (fun i => sign (ε i) * a i) :=
    (F0_continuous M).measurable.comp
      (measurable_pi_iff.2 fun i => (measurable_sign_eval i).mul_const _)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ i, |a i| * cF M i)
    (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs]
  refine (F0_abs_le M _).trans (le_of_eq ?_)
  unfold bnd
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul]
  have : |sign (ε i)| = 1 := by cases ε i <;> simp [sign]
  rw [this, one_mul]

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

lemma rademacher_bound (M : Model n D r) (a : Fin n → ℝ) :
    ∫ ε, F0 M (fun i => sign (ε i) * a i) ∂(signLaw (Fin n)) ≤
      Real.sqrt 2 * Real.sqrt (∑ i, a i ^ 2 * rowFrobeniusSq M i) := by
  haveI : Nonempty (Metric.closedBall (0 : TT n D r) 1) := ⟨⟨0, by simp⟩⟩
  let S := TopologicalSpace.denseSeq (Metric.closedBall (0 : TT n D r) 1)
  have hd : DenseRange S := TopologicalSpace.denseRange_denseSeq _
  have hS : ∀ k, ‖(S k).1‖ ≤ 1 := fun k => mem_closedBall_zero_iff.1 (S k).2
  have h := theorem_7 (S := ℕ) n M.hn (fun i k => a i * X M i (S k).1)
    (fun i k => a i • emb (rowBlock M i (S k).1)) (by
      intro i k k'
      have h1 : a i • emb (rowBlock M i (S k).1) - a i • emb (rowBlock M i (S k').1) =
          a i • emb (rowBlock M i ((S k).1 - (S k').1)) := by
        rw [rowBlock_sub, emb_sub, smul_sub]
      rw [h1, norm_smul, emb_norm, Real.norm_eq_abs, ← mul_sub]
      have h2 : |X M i (S k).1 - X M i (S k').1| ≤ ‖rowBlock M i ((S k).1 - (S k').1)‖ := by
        rw [abs_le]
        have e1 := support_sub_le (M.K i) (M.nonempty i) (M.unitBall i)
          (rowBlock M i (S k).1) (rowBlock M i (S k').1)
        have e2 := support_sub_le (M.K i) (M.nonempty i) (M.unitBall i)
          (rowBlock M i (S k').1) (rowBlock M i (S k).1)
        rw [← rowBlock_sub] at e1
        rw [norm_sub_rev, ← rowBlock_sub] at e2
        unfold X
        constructor
        · linarith
        · exact e1
      calc a i * (X M i (S k).1 - X M i (S k').1) ≤ |a i * (X M i (S k).1 - X M i (S k').1)| :=
            le_abs_self _
        _ = |a i| * |X M i (S k).1 - X M i (S k').1| := abs_mul _ _
        _ ≤ |a i| * ‖rowBlock M i ((S k).1 - (S k').1)‖ := by gcongr)
  rw [scalar_eq M a S hd] at h
  have hv := (vector_le M a (fun k => (S k).1) hS).trans
    (EReal.coe_le_coe_iff.2 (Bd_integral_le M a))
  have h3 := h.trans (PosMulMono.mul_le_mul_of_nonneg_left
    (EReal.coe_nonneg.2 (Real.sqrt_nonneg 2)) hv)
  rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h3
  exact h3

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n : ℕ}

/-- coordinatewise swap along a sign pattern -/
def Theta (ε : Fin n → Bool) (p : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => if ε i then p.1 i else p.2 i, fun i => if ε i then p.2 i else p.1 i)

lemma Theta_measurePreserving (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (ε : Fin n → Bool) :
    MeasurePreserving (Theta ε) ((Measure.pi ν).prod (Measure.pi ν))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) ν ν
  have h2 : MeasurePreserving (fun (g : Fin n → ℝ × ℝ) i =>
      (fun (i : Fin n) (q : ℝ × ℝ) => if ε i then q else q.swap) i (g i))
      (Measure.pi fun i => (ν i).prod (ν i)) (Measure.pi fun i => (ν i).prod (ν i)) := by
    refine measurePreserving_pi (f := fun (i : Fin n) (q : ℝ × ℝ) => if ε i then q else q.swap)
      (fun i => (ν i).prod (ν i)) (fun i => (ν i).prod (ν i)) fun i => ?_
    by_cases h : ε i
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h, if_false]; exact Measure.measurePreserving_swap
  have h3 := h1.comp (h2.comp h1.symm)
  convert h3 using 1
  funext p
  simp only [Theta, MeasurableEquiv.arrowProdEquivProdArrow]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    by_cases h : ε i <;> simp [h, Equiv.arrowProdEquivProdArrow]

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

abbrev PP (ν : Fin n → Measure ℝ) : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi ν).prod (Measure.pi ν)

/-- the symmetrized expectation of `F0` over sign patterns -/
def RR (M : Model n D r) (a : Fin n → ℝ) : ℝ :=
  ∫ ε, F0 M (fun i => sign (ε i) * a i) ∂(signLaw (Fin n))

def HH (M : Model n D r) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ := F0 M (fun i => p.1 i - p.2 i)

section
variable (M : Model n D r) (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

lemma HH_measurable : Measurable (HH M) :=
  (F0_continuous M).measurable.comp
    (measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd))

lemma coord_memLp (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (i : Fin n) :
    MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) 2 (PP ν) :=
  (hL2 i).comp_measurePreserving ((measurePreserving_eval ν i).comp measurePreserving_fst)

lemma coord_memLp' (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (i : Fin n) :
    MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) 2 (PP ν) :=
  (hL2 i).comp_measurePreserving ((measurePreserving_eval ν i).comp measurePreserving_snd)

lemma bound_integrable (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ∑ i, |p.1 i - p.2 i| * cF M i) (PP ν) := by
  refine integrable_finsetSum _ fun i _ => ?_
  exact (((coord_memLp ν hL2 i).sub (coord_memLp' ν hL2 i)).integrable one_le_two).abs.mul_const _

lemma HH_integrable (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) : Integrable (HH M) (PP ν) := by
  refine (bound_integrable M ν hL2).mono' (HH_measurable M).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact F0_abs_le M _

lemma HH_Theta (ε : Fin n → Bool) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    HH M (Theta ε p) = F0 M (fun i => sign (ε i) * (p.1 i - p.2 i)) := by
  unfold HH Theta
  congr 1
  funext i
  by_cases h : ε i <;> simp [h, sign] <;> ring

lemma integral_Theta (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (ε : Fin n → Bool) :
    (∫ p, F0 M (fun i => sign (ε i) * (p.1 i - p.2 i)) ∂(PP ν)) = ∫ p, HH M p ∂(PP ν) := by
  have hΘ := Theta_measurePreserving ν ε
  simp_rw [← HH_Theta M ε]
  rw [← integral_map hΘ.measurable.aemeasurable, hΘ.map_eq]
  rw [hΘ.map_eq]
  exact (HH_measurable M).aestronglyMeasurable

lemma integrable_Theta (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (ε : Fin n → Bool) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      F0 M (fun i => sign (ε i) * (p.1 i - p.2 i))) (PP ν) := by
  have hΘ := Theta_measurePreserving ν ε
  simp_rw [← HH_Theta M ε]
  exact (hΘ.integrable_comp_of_integrable (HH_integrable M ν hL2))

lemma sym_eq (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) :
    ∫ p, RR M (fun i => p.1 i - p.2 i) ∂(PP ν) = ∫ p, HH M p ∂(PP ν) := by
  have hR : ∀ a : Fin n → ℝ, RR M a = ∑ ε : Fin n → Bool, (signLaw (Fin n)).real {ε} *
      F0 M (fun i => sign (ε i) * a i) := by
    intro a
    unfold RR
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
  simp_rw [hR]
  rw [integral_finsetSum _ fun ε _ => (integrable_Theta M ν hL2 ε).const_mul _]
  simp_rw [integral_const_mul, integral_Theta M ν hL2]
  rw [← Finset.sum_mul, sum_measureReal_singleton]
  simp

end

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

section
variable (M : Model n D r) (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

lemma coord_pi_memLp (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (i : Fin n) :
    MemLp (fun y : Fin n → ℝ => y i) 2 (Measure.pi ν) :=
  (hL2 i).comp_measurePreserving (measurePreserving_eval ν i)

lemma integral_coord (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (i : Fin n) :
    ∫ y, y i ∂(Measure.pi ν) = ∫ t, t ∂(ν i) := by
  rw [← (measurePreserving_eval ν i).map_eq, integral_map]
  · exact (measurable_pi_apply i).aemeasurable
  · rw [(measurePreserving_eval ν i).map_eq]; exact (hL2 i).aestronglyMeasurable

lemma F0_shift_integrable (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (x : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => F0 M (fun i => x i - y i)) (Measure.pi ν) := by
  have hb : Integrable (fun y : Fin n → ℝ => ∑ i, |x i - y i| * cF M i) (Measure.pi ν) := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact (((integrable_const (x i)).sub
      ((coord_pi_memLp ν hL2 i).integrable one_le_two)).abs).mul_const _
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((F0_continuous M).measurable.comp
      (measurable_pi_iff.2 fun i => measurable_const.sub (measurable_pi_apply i))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact F0_abs_le M _

lemma jensen_pointwise (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (x : Fin n → ℝ) :
    F0 M (fun i => x i - ∫ t, t ∂(ν i)) ≤ ∫ y, F0 M (fun i => x i - y i) ∂(Measure.pi ν) := by
  refine F0_le_of M _ _ fun w hw => ?_
  have hint : ∀ i, Integrable (fun y : Fin n → ℝ => (x i - y i) * X M i w) (Measure.pi ν) :=
    fun i => ((integrable_const (x i)).sub
      ((coord_pi_memLp ν hL2 i).integrable one_le_two)).mul_const _
  have h1 : ∫ y, G M (fun i => x i - y i) w ∂(Measure.pi ν) =
      G M (fun i => x i - ∫ t, t ∂(ν i)) w := by
    unfold G
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, integral_sub (integrable_const _)
      ((coord_pi_memLp ν hL2 i).integrable one_le_two), integral_coord ν hL2 i]
    simp
  rw [← h1]
  refine integral_mono (integrable_finsetSum _ fun i _ => hint i)
    (F0_shift_integrable M ν hL2 x) fun y => ?_
  exact G_le_F0 M _ w hw

end

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

lemma mp_integral {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {f : α → β} (h : MeasurePreserving f μ ν) {g : β → ℝ}
    (hg : AEStronglyMeasurable g ν) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  have := integral_map h.measurable.aemeasurable (f := g) (by rwa [h.map_eq])
  rw [h.map_eq] at this; exact this.symm

lemma int_diff_sq (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) (i : Fin n) :
    ∫ p, (p.1 i - p.2 i) ^ 2 ∂(PP ν) = 2 * variance (fun t : ℝ => t) (ν i) := by
  have hmp1 : MeasurePreserving (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) (PP ν) (ν i) :=
    (measurePreserving_eval ν i).comp measurePreserving_fst
  have hmp2 : MeasurePreserving (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) (PP ν) (ν i) :=
    (measurePreserving_eval ν i).comp measurePreserving_snd
  have hX := coord_memLp ν hL2 i
  have hY := coord_memLp' ν hL2 i
  have hv : ∀ f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      MeasurePreserving f (PP ν) (ν i) → variance f (PP ν) = variance (fun t : ℝ => t) (ν i) := by
    intro f hf
    rw [← hf.map_eq]
    exact (variance_map (μ := PP ν) (X := fun t : ℝ => t) (Y := f) (by rw [hf.map_eq]; exact (hL2 i).aemeasurable)
      hf.measurable.aemeasurable).symm
  have hm : ∀ f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ,
      MeasurePreserving f (PP ν) (ν i) → ∫ p, f p ∂(PP ν) = ∫ t, t ∂(ν i) := by
    intro f hf
    exact mp_integral hf (g := fun t : ℝ => t) (hL2 i).aestronglyMeasurable
  have hind : IndepFun (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i)
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.2 i) (PP ν) :=
    indepFun_prod (X := fun y : Fin n → ℝ => y i) (Y := fun y : Fin n → ℝ => y i)
      (measurable_pi_apply i) (measurable_pi_apply i)
  have hcov := hind.covariance_eq_zero hX hY
  have hZ : MemLp (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i - p.2 i) 2 (PP ν) := hX.sub hY
  have h1 := variance_eq_sub hZ
  have h2 : variance (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i - p.2 i) (PP ν) =
      2 * variance (fun t : ℝ => t) (ν i) := by
    have := variance_fun_sub hX hY
    rw [hcov, hv _ hmp1, hv _ hmp2] at this
    simpa [two_mul] using this
  have h3 : ∫ p, (p.1 i - p.2 i) ∂(PP ν) = 0 := by
    rw [integral_sub (hX.integrable one_le_two) (hY.integrable one_le_two), hm _ hmp1, hm _ hmp2,
      sub_self]
  rw [h3] at h1
  simp only [Pi.pow_apply] at h1
  linarith

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

def Rsq (M : Model n D r) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, (p.1 i - p.2 i) ^ 2 * rowFrobeniusSq M i

theorem mean_pi (M : Model n D r) (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) :
    ∫ x, F0 M (fun i => x i - ∫ t, t ∂(ν i)) ∂(Measure.pi ν) ≤
      2 * Real.sqrt (∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i) := by
  have hHH := HH_integrable M ν hL2
  -- step A
  have hA : ∫ x, F0 M (fun i => x i - ∫ t, t ∂(ν i)) ∂(Measure.pi ν) ≤ ∫ p, HH M p ∂(PP ν) := by
    rw [show (PP ν) = (Measure.pi ν).prod (Measure.pi ν) from rfl,
      integral_prod (HH M) hHH]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => F0_nonneg M _)
      hHH.integral_prod_left (Filter.Eventually.of_forall fun x => ?_)
    exact jensen_pointwise M ν hL2 x
  -- step B
  have hi : ∀ i, Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (p.1 i - p.2 i) ^ 2 * rowFrobeniusSq M i) (PP ν) := fun i =>
    (((coord_memLp ν hL2 i).sub (coord_memLp' ν hL2 i)).integrable_sq).mul_const _
  have hRsq_int : Integrable (Rsq M) (PP ν) := integrable_finsetSum _ fun i _ => hi i
  have hRsq_meas : Measurable (Rsq M) := by
    unfold Rsq
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd)).pow_const 2).mul_const _
  have hRsq_nonneg : ∀ p, 0 ≤ Rsq M p := fun p =>
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (rowFrobeniusSq_nonneg M i)
  have hsq_int : Integrable (fun p => Real.sqrt (Rsq M p)) (PP ν) := by
    refine MemLp.integrable one_le_two ((memLp_two_iff_integrable_sq
      hRsq_meas.sqrt.aestronglyMeasurable).2 ?_)
    refine hRsq_int.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Real.sq_sqrt (hRsq_nonneg p)]
  have hB : ∫ p, HH M p ∂(PP ν) ≤ ∫ p, Real.sqrt 2 * Real.sqrt (Rsq M p) ∂(PP ν) := by
    rw [← sym_eq M ν hL2]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ?_)
      (hsq_int.const_mul _) (Filter.Eventually.of_forall fun p => ?_)
    · exact integral_nonneg fun ε => F0_nonneg M _
    · exact rademacher_bound M (fun i => p.1 i - p.2 i)
  -- step C
  have hC1 : ∫ p, Real.sqrt (Rsq M p) ∂(PP ν) ≤ Real.sqrt (∫ p, Rsq M p ∂(PP ν)) :=
    integral_sqrt_le (PP ν) (Rsq M) hRsq_meas hRsq_int hRsq_nonneg
  have hC2 : ∫ p, Rsq M p ∂(PP ν) = 2 * ∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i := by
    unfold Rsq
    rw [integral_finsetSum _ fun i _ => hi i]
    simp_rw [integral_mul_const, int_diff_sq ν hL2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_const_mul] at hB
  have hS : 0 ≤ ∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (variance_nonneg _ _) (rowFrobeniusSq_nonneg M i)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc _ ≤ _ := hA.trans hB
    _ ≤ Real.sqrt 2 * Real.sqrt (2 * ∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i) := by
        rw [← hC2]; gcongr
    _ = 2 * Real.sqrt (∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i) := by
        rw [Real.sqrt_mul (by norm_num), ← mul_assoc, h2]

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

variable {n D r : ℕ}

lemma F0_update_le (M : Model n D r) (a : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    |F0 M a - F0 M (Function.update a i t)| ≤ |a i - t| * cF M i := by
  have key : ∀ b c : Fin n → ℝ, (∀ j, j ≠ i → b j = c j) →
      F0 M b - F0 M c ≤ |b i - c i| * cF M i := by
    intro b c h
    refine (F0_sub_le M b c).trans (le_of_eq ?_)
    unfold bnd
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [h j hj]
    · simp
  have h1 := key a (Function.update a i t) (fun j hj => by simp [Function.update_of_ne hj])
  have h2 := key (Function.update a i t) a (fun j hj => by simp [Function.update_of_ne hj])
  simp only [Function.update_self] at h1 h2
  rw [abs_le]
  constructor
  · rw [abs_sub_comm] at h2; linarith
  · exact h1

theorem var_pi (M : Model n D r) (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i)) :
    variance (fun x : Fin n → ℝ => F0 M (fun i => x i - ∫ t, t ∂(ν i))) (Measure.pi ν) ≤
      ∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i := by
  set m : Fin n → ℝ := fun i => ∫ t, t ∂(ν i) with hm
  set Z : (Fin n → ℝ) → ℝ := fun x => F0 M (fun i => x i - m i) with hZdef
  have hZm : Measurable Z :=
    (F0_continuous M).measurable.comp
      (measurable_pi_iff.2 fun i => (measurable_pi_apply i).sub measurable_const)
  have hZ : MemLp Z 2 (Measure.pi ν) := by
    have hb : MemLp (fun x : Fin n → ℝ => ∑ i, |x i - m i| * cF M i) 2 (Measure.pi ν) := by
      have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          MemLp (fun x : Fin n → ℝ => |x i - m i| * cF M i) 2 (Measure.pi ν) := fun i _ =>
        (((coord_pi_memLp ν hL2 i).sub (memLp_const (m i))).norm).mul_const _
      exact memLp_finsetSum _ hi
    refine hb.mono' hZm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact F0_abs_le M _
  have hES := variance_le_half_sum_resample_sq (fun i => ν i) hZ
  refine hES.trans ?_
  have hterm : ∀ i, ∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
      ∂((Measure.pi ν).prod (Measure.pi ν)) ≤
      2 * (variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i) := by
    intro i
    have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (p.1 i - p.2 i) ^ 2 * rowFrobeniusSq M i) (PP ν) :=
      (((coord_memLp ν hL2 i).sub (coord_memLp' ν hL2 i)).integrable_sq).mul_const _
    calc _ ≤ ∫ p, (p.1 i - p.2 i) ^ 2 * rowFrobeniusSq M i ∂(PP ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _) hint
            (Filter.Eventually.of_forall fun p => ?_)
          have h := F0_update_le M (fun j => p.1 j - m j) i (p.2 i - m i)
          have e : (Function.update (fun j => p.1 j - m j) i (p.2 i - m i)) =
              fun j => Function.update p.1 i (p.2 i) j - m j := by
            funext j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj]
          rw [e] at h
          have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          rw [sq_abs, mul_pow, sq_abs, cF_sq] at h2
          have e2 : p.1 i - m i - (p.2 i - m i) = p.1 i - p.2 i := by ring
          rw [e2] at h2
          exact h2
      _ = _ := by
          rw [integral_mul_const, int_diff_sq ν hL2]; ring
  have : ∑ i, ∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
      ∂((Measure.pi ν).prod (Measure.pi ν)) ≤
      ∑ i, 2 * (variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i) :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [← Finset.mul_sum] at this
  linarith

end HindsightGain.Uniform.Dev.Lem32
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace HindsightGain.Uniform.Dev.Lem32
open HindsightGain.Uniform

lemma main_aux {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Fin n → Ω → ℝ) (hindep : iIndepFun ζ μ)
    (hsecond : ∀ i, MemLp (ζ i) 2 μ) :
    MemLp (fluctuationRV M μ ζ) 2 μ ∧
      (∫ ω, fluctuationRV M μ ζ ω ∂μ) ≤ 2 * varianceScale M μ ζ ∧
      variance (fluctuationRV M μ ζ) μ ≤ varianceScale M μ ζ ^ 2 ∧
      (∫ ω, fluctuationRV M μ ζ ω ^ 2 ∂μ) ≤ 5 * varianceScale M μ ζ ^ 2 := by
  have hae : ∀ i, AEMeasurable (ζ i) μ := fun i => (hsecond i).aemeasurable
  set ν : Fin n → Measure ℝ := fun i => μ.map (ζ i) with hν
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i => Measure.isProbabilityMeasure_map (hae i)
  have hL2 : ∀ i, MemLp (fun t : ℝ => t) 2 (ν i) := fun i =>
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hae i)).2 (hsecond i)
  set T : Ω → (Fin n → ℝ) := fun ω i => ζ i ω with hT
  have hTae : AEMeasurable T μ := aemeasurable_pi_iff.2 hae
  have hmap : μ.map T = Measure.pi ν := by
    have := (iIndepFun_iff_map_fun_eq_pi_map hae).1 hindep
    exact this
  set Φ : (Fin n → ℝ) → ℝ := fun x => F0 M (fun i => x i - ∫ t, t ∂(ν i)) with hΦ
  have hΦm : Measurable Φ :=
    (F0_continuous M).measurable.comp
      (measurable_pi_iff.2 fun i => (measurable_pi_apply i).sub measurable_const)
  have hmean : ∀ i, weightMeans μ ζ i = ∫ t, t ∂(ν i) := by
    intro i
    show ∫ ω, ζ i ω ∂μ = _
    exact (integral_map (hae i) (f := fun t : ℝ => t) aestronglyMeasurable_id).symm
  have hΔ : fluctuationRV M μ ζ = Φ ∘ T := by
    funext ω
    show F0 M (fun i => ζ i ω - weightMeans μ ζ i) = _
    simp only [hmean]
    rfl
  have hΦL2 : MemLp Φ 2 (Measure.pi ν) := by
    have hb : MemLp (fun x : Fin n → ℝ => ∑ i, |x i - ∫ t, t ∂(ν i)| * cF M i) 2 (Measure.pi ν) := by
      have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          MemLp (fun x : Fin n → ℝ => |x i - ∫ t, t ∂(ν i)| * cF M i) 2 (Measure.pi ν) := fun i _ =>
        (((coord_pi_memLp ν hL2 i).sub (memLp_const _)).norm).mul_const _
      exact memLp_finsetSum _ hi
    refine hb.mono' hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact F0_abs_le M _
  have hΔL2 : MemLp (fluctuationRV M μ ζ) 2 μ := by
    rw [hΔ]
    exact (memLp_map_measure_iff (hmap ▸ hΦm.aestronglyMeasurable) hTae).1 (hmap ▸ hΦL2)
  have hint : ∫ ω, fluctuationRV M μ ζ ω ∂μ = ∫ x, Φ x ∂(Measure.pi ν) := by
    rw [← hmap, integral_map hTae hΦm.aestronglyMeasurable, hΔ]
    rfl
  have hvar : variance (fluctuationRV M μ ζ) μ = variance Φ (Measure.pi ν) := by
    rw [← hmap, variance_map (hmap ▸ hΦm.aemeasurable) hTae, hΔ]
  have hS : varianceScaleSq M μ ζ = ∑ i, variance (fun t : ℝ => t) (ν i) * rowFrobeniusSq M i := by
    unfold varianceScaleSq
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (variance_map (X := fun t : ℝ => t) (Y := ζ i) measurable_id.aemeasurable (hae i)).symm
  have hS0 : 0 ≤ varianceScaleSq M μ ζ := by
    unfold varianceScaleSq
    exact Finset.sum_nonneg fun i _ => mul_nonneg (variance_nonneg _ _) (rowFrobeniusSq_nonneg M i)
  have hV2 : varianceScale M μ ζ ^ 2 = varianceScaleSq M μ ζ := Real.sq_sqrt hS0
  have hmeanb : ∫ ω, fluctuationRV M μ ζ ω ∂μ ≤ 2 * varianceScale M μ ζ := by
    rw [hint, varianceScale, hS]
    exact mean_pi M ν hL2
  have hvarb : variance (fluctuationRV M μ ζ) μ ≤ varianceScale M μ ζ ^ 2 := by
    rw [hvar, hV2, hS]
    exact var_pi M ν hL2
  refine ⟨hΔL2, hmeanb, hvarb, ?_⟩
  have h1 := variance_eq_sub hΔL2
  simp only [Pi.pow_apply] at h1
  have h0 : 0 ≤ ∫ ω, fluctuationRV M μ ζ ω ∂μ := by
    refine integral_nonneg fun ω => ?_
    exact F0_nonneg M _
  have hV0 : 0 ≤ varianceScale M μ ζ := Real.sqrt_nonneg _
  nlinarith

end HindsightGain.Uniform.Dev.Lem32

namespace HindsightGain.Uniform
open MeasureTheory ProbabilityTheory
open HindsightGain.Uniform.Dev.Lem32 in
/-- Lemma 3.2, p.16, all three bounds for exactly (20).
Square integrability of Delta is asserted, rather than imposed on the weights. -/
theorem chk_lemma_3_2 {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Fin n → Ω → ℝ) (hindep : iIndepFun ζ μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ ζ i ω) (hsecond : ∀ i, MemLp (ζ i) 2 μ) :
    MemLp (fluctuationRV M μ ζ) 2 μ ∧
      (∫ ω, fluctuationRV M μ ζ ω ∂μ) ≤ 2 * varianceScale M μ ζ ∧
      variance (fluctuationRV M μ ζ) μ ≤ varianceScale M μ ζ ^ 2 ∧
      (∫ ω, fluctuationRV M μ ζ ω ^ 2 ∂μ) ≤ 5 * varianceScale M μ ζ ^ 2 :=
  main_aux M μ ζ hindep hsecond

end HindsightGain.Uniform
end

theorem solution : type_of% @HindsightGain.Uniform.chk_lemma_3_2 := @HindsightGain.Uniform.chk_lemma_3_2
