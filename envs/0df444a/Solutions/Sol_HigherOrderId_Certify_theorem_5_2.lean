-- Prove2me | solution 1 for HigherOrderId.Certify.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T21:21:58.754997+00:00
-- url     : https://prove2.me/submissions/602ce5bf-d8c3-4dfa-8174-3a2589edc53a

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_Release
import Definitions.Def_HigherOrderId_Certify_Fisher
import Definitions.Def_HigherOrderId_Certify_GaussTest
import Theorems.Thm_HigherOrderId_Certify_lemma_C_1
import Definitions.Def_HigherOrderId_Certify_TallCompletion
import Theorems.Thm_HigherOrderId_Certify_lemma_B_5
import Theorems.Thm_HigherOrderId_Certify_eq_101

section
open Matrix

namespace HigherOrderId.Certify.Dev.Nuc

variable {d : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

end HigherOrderId.Certify.Dev.Nuc
end

section
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B2
open HigherOrderId.Certify


lemma Gw_apply {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (r : FrameRows m) (c : Fin m) :
    Gw ι w (ι r) c = frameRow w r c := by
  unfold Gw
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'; simp [ι.injective.ne hr']
  · simp

lemma Sw_det {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    (Sw ι w).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hSx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hx
  have h1 : (Gw ι w *ᵥ x) ⬝ᵥ (Gw ι w *ᵥ x) = 0 := by
    have : x ⬝ᵥ ((Sw ι w) *ᵥ x) = 0 := by rw [hSx]; simp
    rw [Sw, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact this
  have h2 := dotProduct_self_eq_zero.mp h1
  funext i
  have := congrFun h2 (ι (Sum.inl i))
  simp only [Matrix.mulVec, dotProduct, Gw_apply, frameRow, Pi.zero_apply] at this
  simp [mul_comm] at this
  rcases this with h | h
  · exact h
  · exact absurd h (Real.sqrt_ne_zero'.mpr hw)

lemma sqrtS_props {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    ∃ Ri : Matrix (Fin m) (Fin m) ℝ, Riᵀ = Ri ∧ (CFC.sqrt (Sw ι w)) * Ri = 1 ∧
      Ri * (CFC.sqrt (Sw ι w)) = 1 ∧ (CFC.sqrt (Sw ι w))ᵀ = CFC.sqrt (Sw ι w) ∧
      Uw ι w = Gw ι w * Ri := by
  set R := CFC.sqrt (Sw ι w) with hR
  have hS : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sw ι w := by
    have := Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self (Gw ι w))
    simpa [Sw, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hRR : R * R = Sw ι w := CFC.sqrt_mul_sqrt_self _ hS
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg _
  have hRsym : Rᵀ = R := by
    have := (Matrix.nonneg_iff_posSemidef.mp hR0).isHermitian
    have h2 : Rᴴ = R := this
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hdet : R.det ≠ 0 := by
    have := Sw_det ι w hw
    rw [← hRR, Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨R⁻¹, ?_, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, hRsym, rfl⟩
  rw [Matrix.transpose_nonsing_inv, hRsym]

lemma fullColRank_Uw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    FullColRank (Uw ι w) := by
  obtain ⟨Ri, hRit, hRRi, hRiR, hRt, hU⟩ := sqrtS_props ι w hw
  set R := CFC.sqrt (Sw ι w)
  intro B hB hD
  set B' := Ri * B * Ri with hB'
  have hB's : B'ᵀ = B' := by
    rw [hB', Matrix.transpose_mul, Matrix.transpose_mul, hRit, hB.eq, Matrix.mul_assoc]
  have hdiag : ∀ a, (Gw ι w * B' * (Gw ι w)ᵀ) a a = 0 := by
    intro a
    have := congrFun hD a
    simp only [DU, Pi.zero_apply] at this
    rw [hU, Matrix.transpose_mul, hRit] at this
    rw [← this, hB']
    try simp only [Matrix.mul_assoc]
  have hq : ∀ r, (Gw ι w * B' * (Gw ι w)ᵀ) (ι r) (ι r) =
      ∑ c, ∑ c', frameRow w r c * B' c c' * frameRow w r c' := by
    intro r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Gw_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hii : ∀ i, B' i i = 0 := by
    intro i
    have := (hq (Sum.inl i)).symm.trans (hdiag _)
    simp [frameRow] at this
    have hsw : √w ≠ 0 := Real.sqrt_ne_zero'.mpr hw
    tauto
  have hij : ∀ i j (h : i < j), B' i j = 0 := by
    intro i j h
    have := (hq (Sum.inr ⟨(i, j), h⟩)).symm.trans (hdiag _)
    have hv : frameRow w (Sum.inr ⟨(i, j), h⟩) = Pi.single i 1 + Pi.single j 1 := by
      funext c
      simp only [frameRow, Pi.add_apply, Pi.single_apply]
      have hne : i ≠ j := ne_of_lt h
      by_cases h1 : c = i <;> by_cases h2 : c = j <;>
        first | simp [h1, h2, hne, hne.symm] | (exfalso; exact hne (h1.symm.trans h2))
    have hform : ∀ v : Fin m → ℝ, ∑ c, ∑ c', v c * B' c c' * v c' = v ⬝ᵥ (B' *ᵥ v) := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hform, hv] at this
    simp [add_dotProduct, dotProduct_add, Matrix.mulVec_add, Matrix.mulVec_single, hii] at this
    have hsym : B' j i = B' i j := by
      have := congrFun (congrFun hB's i) j
      simpa using this
    rw [hsym] at this
    linarith
  have hB'0 : B' = 0 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simpa using hij i j h
    · subst h; simpa using hii i
    · have := hij j i h
      have hsym := congrFun (congrFun hB's i) j
      simp at hsym
      simp [← hsym, this]
  calc B = R * B' * R := by
        rw [hB']
        calc B = (R * Ri) * B * (Ri * R) := by rw [hRRi, hRiR]; simp
          _ = _ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hB'0]; simp

end HigherOrderId.Certify.Dev.B2

namespace HigherOrderId.Certify

end HigherOrderId.Certify
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Complex

namespace HigherOrderId.Certify.Dev.T5.PartC
open HigherOrderId.Certify

/-! ## T1: the release law as the image of a standard Gaussian -/

/-- Flat index of the release coordinates: `(e, none)` is the value, `(e, some i)` the
`i`-th gradient coordinate of environment `e`. -/
abbrev Jx (d E : ℕ) := Fin E × Option (Fin d)

/-- The flat observation space. -/
abbrev Hs (d E : ℕ) := EuclideanSpace ℝ (Jx d E)

/-- Flat coordinates of an observation. -/
def obsCoord {d E : ℕ} (o : Obs d E) (j : Jx d E) : ℝ :=
  j.2.elim (o j.1).1 (o j.1).2

/-- Flatten an observation. -/
def fromObs {d E : ℕ} (o : Obs d E) : Hs d E := WithLp.toLp 2 (obsCoord o)

/-- Unflatten. -/
def toObs {d E : ℕ} (y : Hs d E) : Obs d E := fun e => (y (e, none), fun i => y (e, some i))

lemma toObs_fromObs {d E : ℕ} (o : Obs d E) : toObs (fromObs o) = o := by
  funext e
  simp [toObs, fromObs, obsCoord]

lemma measurable_toObs {d E : ℕ} : Measurable (toObs (d := d) (E := E)) := by
  unfold toObs
  fun_prop

lemma measurable_obsCoord {d E : ℕ} : Measurable (fun o : Obs d E => obsCoord o) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  rcases j with ⟨e, _ | i⟩
  · simp only [obsCoord, Option.elim]
    fun_prop
  · simp only [obsCoord, Option.elim]
    fun_prop

lemma measurable_fromObs {d E : ℕ} : Measurable (fromObs (d := d) (E := E)) :=
  (MeasurableEquiv.toLp 2 (Jx d E → ℝ)).measurable.comp measurable_obsCoord

/-- Flat mean vector of the release under `(b, Q)`. -/
noncomputable def meanFn {d E : ℕ} (D : Design d E) (b : Fin d → ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (j : Jx d E) : ℝ :=
  j.2.elim (mechValue b Q (D.x j.1)) (fun i => mechGrad b Q (D.x j.1) i)

/-- The common noise standard deviation `√(σ²/n)`. -/
noncomputable def sd (σ : ℝ) (n : ℕ) : ℝ := ((noiseVar σ n : NNReal) : ℝ).sqrt

lemma sd_sq (σ : ℝ) (n : ℕ) : sd σ n ^ 2 = (noiseVar σ n : ℝ) :=
  Real.sq_sqrt (NNReal.coe_nonneg _)

lemma inner_fromObs {d E : ℕ} (o : Obs d E) (ξ : Hs d E) :
    inner ℝ (fromObs o) ξ = ∑ e, ((o e).1 * ξ (e, none) + ∑ i, (o e).2 i * ξ (e, some i)) := by
  simp only [PiLp.inner_apply, fromObs, Fintype.sum_prod_type, Fintype.sum_option]
  simp [obsCoord, mul_comm]

lemma charFun_gauss (m : ℝ) (v : NNReal) (t : ℝ) :
    ∫ x, cexp (↑(x * t) * I) ∂(gaussianReal m v) = cexp (t * m * I - v * t ^ 2 / 2) := by
  rw [← charFun_gaussianReal, charFun_apply_real]
  congr 1; funext x; push_cast; ring_nf

lemma charFun_release {d E : ℕ} (D : Design d E) (σ : ℝ) (n : ℕ) (hn : ∀ e, D.n e = n)
    (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ξ : Hs d E) :
    charFun ((releaseLaw D σ b Q).map fromObs) ξ =
      cexp (∑ e, ((ξ (e, none) * mechValue b Q (D.x e) * I -
        (noiseVar σ n : ℝ) * ξ (e, none) ^ 2 / 2) +
        ∑ i, (ξ (e, some i) * mechGrad b Q (D.x e) i * I -
          (noiseVar σ n : ℝ) * ξ (e, some i) ^ 2 / 2))) := by
  rw [charFun_apply, integral_map measurable_fromObs.aemeasurable (by fun_prop)]
  have hint : ∀ o : Obs d E, cexp (↑(inner ℝ (fromObs o) ξ) * I) =
      ∏ e, (cexp (↑((o e).1 * ξ (e, none)) * I) *
        ∏ i, cexp (↑((o e).2 i * ξ (e, some i)) * I)) := by
    intro o
    rw [inner_fromObs]
    simp only [ofReal_sum, ofReal_add, Finset.sum_mul, add_mul, Complex.exp_sum,
      Complex.exp_add]
  simp_rw [hint]
  rw [releaseLaw, integral_fintype_prod_eq_prod
    (f := fun e (p : ℝ × (Fin d → ℝ)) => cexp (↑(p.1 * ξ (e, none)) * I) *
        ∏ i, cexp (↑(p.2 i * ξ (e, some i)) * I))]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [integral_prod_mul (f := fun x : ℝ => cexp (↑(x * ξ (e, none)) * I))
    (g := fun p : Fin d → ℝ => ∏ i, cexp (↑(p i * ξ (e, some i)) * I))]
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) => cexp (↑(x * ξ (e, some i)) * I))]
  simp_rw [charFun_gauss, hn e]
  rw [Complex.exp_add, Complex.exp_sum]

lemma charFun_std_shift {d E : ℕ} (c : Hs d E) (s : ℝ) (ξ : Hs d E) :
    charFun ((stdGaussian (Hs d E)).map (fun g => c + s • g)) ξ =
      cexp (↑(inner ℝ c ξ) * I - s ^ 2 * ‖ξ‖ ^ 2 / 2) := by
  rw [show (fun g : Hs d E => c + s • g) = (fun g => c + g) ∘ (fun g => s • g) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_const_add, charFun_map_smul,
    charFun_stdGaussian, ← Complex.exp_add, norm_smul]
  have h : ((‖s‖ * ‖ξ‖ : ℝ) : ℂ) ^ 2 = (s : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 := by
    rw [← ofReal_pow, mul_pow, Real.norm_eq_abs, sq_abs]; push_cast; ring
  rw [h]
  congr 1
  ring

/-- **T1.** The release law is the image of a standard Gaussian vector `g` under
`g ↦ μ(b, Q) + s g`, when all allocations equal `n`. -/
lemma releaseLaw_eq_map {d E : ℕ} (D : Design d E) (σ : ℝ) (n : ℕ) (hn : ∀ e, D.n e = n)
    (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    releaseLaw D σ b Q = (stdGaussian (Hs d E)).map
      (fun g => toObs (WithLp.toLp 2 (meanFn D b Q) + sd σ n • g)) := by
  have : IsProbabilityMeasure (releaseLaw D σ b Q) := by unfold releaseLaw; infer_instance
  have h1 : (releaseLaw D σ b Q).map fromObs =
      (stdGaussian (Hs d E)).map (fun g => WithLp.toLp 2 (meanFn D b Q) + sd σ n • g) := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [charFun_release D σ n hn, charFun_std_shift]
    congr 1
    have hn2 : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ∑ j, ((ξ j : ℝ) : ℂ) ^ 2 := by
      rw [← ofReal_pow, EuclideanSpace.real_norm_sq_eq]; push_cast; rfl
    have hs2 : ((sd σ n : ℝ) : ℂ) ^ 2 = ((noiseVar σ n : ℝ) : ℂ) := by rw [← ofReal_pow, sd_sq]
    rw [hn2, hs2, PiLp.inner_apply, ofReal_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Finset.mul_sum, Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [meanFn, Option.elim]
    simp only [RCLike.inner_apply, conj_trivial, ofReal_mul, Finset.sum_sub_distrib,
      Finset.sum_mul, add_mul]
    ring_nf
    simp only [Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    ring_nf
  have h2 : releaseLaw D σ b Q = ((releaseLaw D σ b Q).map fromObs).map toObs := by
    rw [Measure.map_map measurable_toObs measurable_fromObs]
    have : toObs ∘ fromObs = (id : Obs d E → Obs d E) := funext toObs_fromObs
    rw [this, Measure.map_id]
  rw [h2, h1, Measure.map_map measurable_toObs (by fun_prop)]
  rfl

end HigherOrderId.Certify.Dev.T5.PartC
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify.Dev.T5.PartC
open HigherOrderId.Certify

/-! ## The coordinates `ϑ` of (99) and the linear release mean -/

/-- `b` of the coordinate vector `ϑ`. -/
noncomputable def thB {d : ℕ} (ϑ : ThetaIdx d → ℝ) : Fin d → ℝ := ∑ s, ϑ s • thetaB s

/-- `Q` of the coordinate vector `ϑ`. -/
noncomputable def thQ {d : ℕ} (ϑ : ThetaIdx d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ s, ϑ s • thetaQ s

lemma thB_zero {d : ℕ} : thB (0 : ThetaIdx d → ℝ) = 0 := by simp [thB]

lemma thQ_zero {d : ℕ} : thQ (0 : ThetaIdx d → ℝ) = 0 := by simp [thQ]

lemma thB_apply {d : ℕ} (ϑ : ThetaIdx d → ℝ) (i : Fin d) : thB ϑ i = ϑ (Sum.inl i) := by
  simp [thB, Finset.sum_apply, Fintype.sum_sum_type, thetaB, Pi.single_apply]

lemma thQ_apply {d : ℕ} (ϑ : ThetaIdx d → ℝ) (i j : Fin d) :
    thQ ϑ i j = ∑ p : {p : Fin d × Fin d // p.1 < p.2}, ϑ (Sum.inr p) *
      ((if p.1.1 = i ∧ p.1.2 = j then 1 else 0) + (if p.1.2 = i ∧ p.1.1 = j then 1 else 0)) := by
  simp [thQ, Matrix.sum_apply, Fintype.sum_sum_type, thetaQ, Matrix.single_apply]

lemma thQ_symm {d : ℕ} (ϑ : ThetaIdx d → ℝ) (i j : Fin d) : thQ ϑ i j = thQ ϑ j i := by
  rw [thQ_apply, thQ_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e1 : (p.1.1 = i ∧ p.1.2 = j) ↔ (p.1.2 = j ∧ p.1.1 = i) := and_comm
  have e2 : (p.1.2 = i ∧ p.1.1 = j) ↔ (p.1.1 = j ∧ p.1.2 = i) := and_comm
  simp only [e1, e2]
  ring

lemma thQ_diag {d : ℕ} (ϑ : ThetaIdx d → ℝ) (i : Fin d) : thQ ϑ i i = 0 := by
  rw [thQ_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  have h := p.2
  have h1 : ¬ (p.1.1 = i ∧ p.1.2 = i) := by
    rintro ⟨h1, h2⟩; rw [h1, h2] at h; exact lt_irrefl _ h
  have h2 : ¬ (p.1.2 = i ∧ p.1.1 = i) := by
    rintro ⟨h1, h2⟩; rw [h1, h2] at h; exact lt_irrefl _ h
  simp [h1, h2]

lemma thQ_upper {d : ℕ} (ϑ : ThetaIdx d → ℝ) (p : {p : Fin d × Fin d // p.1 < p.2}) :
    thQ ϑ p.1.1 p.1.2 = ϑ (Sum.inr p) := by
  rw [thQ_apply, Finset.sum_eq_single p]
  · have : ¬ p.1.2 = p.1.1 := fun h => lt_irrefl _ (h ▸ p.2)
    simp [this]
  · intro q _ hq
    have h1 : ¬ (q.1.1 = p.1.1 ∧ q.1.2 = p.1.2) := by
      rintro ⟨h1, h2⟩; exact hq (Subtype.ext (Prod.ext h1 h2))
    have h2 : ¬ (q.1.2 = p.1.1 ∧ q.1.1 = p.1.2) := by
      rintro ⟨h1, h2⟩
      have := q.2; rw [h1, h2] at this; exact lt_asymm this p.2
    simp [h1, h2]
  · simp

lemma thQ_symZero {d : ℕ} (ϑ : ThetaIdx d → ℝ) : IsSymZeroDiag (thQ ϑ) :=
  ⟨by ext i j; exact thQ_symm ϑ j i, thQ_diag ϑ⟩

lemma frob_single {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    ∑ i, ∑ j, X i j * Matrix.single a b (1 : ℝ) i j = X a b := by
  simp [Matrix.single_apply, ite_and]

lemma frob_thetaQ {d : ℕ} (ϑ : ThetaIdx d → ℝ) (p : {p : Fin d × Fin d // p.1 < p.2}) :
    ∑ i, ∑ j, thQ ϑ i j * thetaQ (Sum.inr p) i j = 2 * ϑ (Sum.inr p) := by
  simp only [thetaQ, Matrix.add_apply, mul_add, Finset.sum_add_distrib, frob_single]
  rw [thQ_symm ϑ p.1.2 p.1.1, thQ_upper]; ring

lemma energy_th {d : ℕ} (ϑ : ThetaIdx d → ℝ) : energy (thB ϑ) (thQ ϑ) = ∑ s, ϑ s ^ 2 := by
  have hQ : ∑ i, ∑ j, thQ ϑ i j ^ 2 = 2 * ∑ p : {p : Fin d × Fin d // p.1 < p.2},
      ϑ (Sum.inr p) ^ 2 := by
    have h1 : ∀ i j, thQ ϑ i j ^ 2 = ∑ s, ϑ s * (thQ ϑ i j * thetaQ s i j) := by
      intro i j
      conv_lhs => rw [sq]; arg 2; rw [thQ]
      rw [Matrix.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp only [Matrix.smul_apply, smul_eq_mul]; ring
    simp_rw [h1]
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∑ s : ThetaIdx d, ϑ s * (thQ ϑ i j * thetaQ s i j)) =
        ∑ s : ThetaIdx d, ∑ i : Fin d, ∑ j : Fin d, ϑ s * (thQ ϑ i j * thetaQ s i j) by
      have hc : ∀ i : Fin d, ∑ j : Fin d, ∑ s : ThetaIdx d, ϑ s * (thQ ϑ i j * thetaQ s i j) =
          ∑ s : ThetaIdx d, ∑ j : Fin d, ϑ s * (thQ ϑ i j * thetaQ s i j) :=
        fun i => Finset.sum_comm
      rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_comm]]
    simp_rw [← Finset.mul_sum]
    rw [Fintype.sum_sum_type, Finset.mul_sum]
    simp only [frob_thetaQ]
    simp only [thetaQ, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [energy, hQ, Fintype.sum_sum_type]
  simp [thB_apply]

/-- The linear part of the release mean, flat coordinates × `ϑ`-coordinates. -/
noncomputable def Amat {d E : ℕ} (D : Design d E) : Matrix (Jx d E) (ThetaIdx d) ℝ :=
  fun j s => j.2.elim (thetaB s ⬝ᵥ D.x j.1 + (1 / 2) * (D.x j.1 ⬝ᵥ (thetaQ s *ᵥ D.x j.1)))
    (fun i => thetaB s i + (thetaQ s *ᵥ D.x j.1) i)

/-- The intercept of the release mean. -/
noncomputable def cvec {d E : ℕ} : Jx d E → ℝ := fun j => j.2.elim (1 / 2) (fun _ => 0)

lemma meanFn_th {d E : ℕ} (D : Design d E) (ϑ : ThetaIdx d → ℝ) :
    meanFn D (thB ϑ) (thQ ϑ) = cvec + Amat D *ᵥ ϑ := by
  funext j
  rcases j with ⟨e, _ | i⟩
  · simp only [meanFn, Option.elim, mechValue, cvec, Pi.add_apply]
    rw [show (Amat D *ᵥ ϑ) (e, none) = ∑ s, Amat D (e, none) s * ϑ s from rfl]
    simp only [Amat, Option.elim]
    rw [thB, thQ, Matrix.sum_mulVec, sum_dotProduct, dotProduct_sum,
      Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  · simp only [meanFn, Option.elim, mechGrad, cvec, Pi.add_apply]
    rw [show (Amat D *ᵥ ϑ) (e, some i) = ∑ s, Amat D (e, some i) s * ϑ s from rfl]
    simp only [Amat, Option.elim]
    rw [thB, thQ, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply, zero_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun x _ => by ring)

lemma meanFn_zero {d E : ℕ} (D : Design d E) : meanFn D 0 0 = cvec := by
  have := meanFn_th D 0
  rw [thB_zero, thQ_zero, Matrix.mulVec_zero, add_zero] at this
  exact this

/-- The Fisher matrix is `(n/σ²) AᵀA` when every allocation is `n`. -/
lemma fisher_eq {d E : ℕ} (D : Design d E) (σ : ℝ) (n : ℕ) (hn : ∀ e, D.n e = n) :
    fullFisherMat D σ = ((n : ℝ) / σ ^ 2) • ((Amat D)ᵀ * Amat D) := by
  ext s s'
  simp only [fullFisherMat, hn, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Fintype.sum_option, Amat, Option.elim,
    Finset.mul_sum, mul_add]

lemma sd_sq_eq (σ : ℝ) (n : ℕ) (hn : 0 < n) : sd σ n ^ 2 = σ ^ 2 / n := by
  rw [sd_sq, noiseVar, Real.coe_toNNReal _ (by positivity)]

lemma fisher_eq' {d E : ℕ} (D : Design d E) (σ : ℝ) (n : ℕ) (hn0 : 0 < n)
    (hn : ∀ e, D.n e = n) :
    fullFisherMat D σ = (sd σ n ^ 2)⁻¹ • ((Amat D)ᵀ * Amat D) := by
  rw [fisher_eq D σ n hn, sd_sq_eq σ n hn0, inv_div]

end HigherOrderId.Certify.Dev.T5.PartC
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Complex WithLp

namespace HigherOrderId.Certify.Dev.T5.PartC

/-! ## Sufficiency: a Gaussian linear model reduces to `N(θ, Σ)` -/

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

/-- The continuous linear map of a rectangular matrix between Euclidean spaces. -/
noncomputable def mat (A : Matrix J ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ J :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toLp 2 (A *ᵥ ofLp x)
      map_add' := fun x y => by simp [Matrix.mulVec_add]
      map_smul' := fun r x => by simp [Matrix.mulVec_smul] }

lemma ofLp_mat (A : Matrix J ι ℝ) (x : EuclideanSpace ℝ ι) : ofLp (mat A x) = A *ᵥ ofLp x := rfl

lemma inner_eq_dot {κ : Type*} [Fintype κ] (x y : EuclideanSpace ℝ κ) :
    inner ℝ x y = ofLp x ⬝ᵥ ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma inner_mat (A : Matrix J ι ℝ) (x : EuclideanSpace ℝ ι) (ξ : EuclideanSpace ℝ J) :
    inner ℝ (mat A x) ξ = inner ℝ x (mat Aᵀ ξ) := by
  rw [inner_eq_dot, inner_eq_dot, ofLp_mat, ofLp_mat, dotProduct_comm, dotProduct_mulVec,
    mulVec_transpose, dotProduct_comm]

lemma norm_sq_eq_dot {κ : Type*} [Fintype κ] (x : EuclideanSpace ℝ κ) :
    ‖x‖ ^ 2 = ofLp x ⬝ᵥ ofLp x := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dot]

lemma charFun_map_mat (μ : Measure (EuclideanSpace ℝ ι)) (A : Matrix J ι ℝ)
    (ξ : EuclideanSpace ℝ J) :
    charFun (μ.map (mat A)) ξ = charFun μ (mat Aᵀ ξ) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_mat]

lemma charFun_std_shift' (c : EuclideanSpace ℝ J) (s : ℝ) (ξ : EuclideanSpace ℝ J) :
    charFun ((stdGaussian (EuclideanSpace ℝ J)).map (fun g => c + s • g)) ξ =
      cexp (↑(inner ℝ c ξ) * I - s ^ 2 * ‖ξ‖ ^ 2 / 2) := by
  rw [show (fun g : EuclideanSpace ℝ J => c + s • g) = (fun g => c + g) ∘ (fun g => s • g) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_const_add, charFun_map_smul,
    charFun_stdGaussian, ← Complex.exp_add, norm_smul]
  have h : ((‖s‖ * ‖ξ‖ : ℝ) : ℂ) ^ 2 = (s : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 := by
    rw [← ofReal_pow, mul_pow, Real.norm_eq_abs, sq_abs]; push_cast; ring
  rw [h]
  congr 1
  ring

/-- The scaled Fisher matrix `s⁻² AᵀA`. -/
noncomputable def Fis (A : Matrix J ι ℝ) (s : ℝ) : Matrix ι ι ℝ := (s ^ 2)⁻¹ • (Aᵀ * A)

/-- Its inverse, the efficient covariance. -/
noncomputable def Sig (A : Matrix J ι ℝ) (s : ℝ) : Matrix ι ι ℝ := (Fis A s)⁻¹

/-- The projection `s⁻² A Σ Aᵀ` onto the range of `A`. -/
noncomputable def Prj (A : Matrix J ι ℝ) (s : ℝ) : Matrix J J ℝ := (s ^ 2)⁻¹ • (A * Sig A s * Aᵀ)

section facts
variable (A : Matrix J ι ℝ) (s : ℝ) (hs : 0 < s) (hF : (Fis A s).PosDef)
include hs hF

lemma AtA_Sig : (Aᵀ * A) * Sig A s = s ^ 2 • (1 : Matrix ι ι ℝ) := by
  have hu : IsUnit (Fis A s).det := (Matrix.isUnit_iff_isUnit_det _).mp hF.isUnit
  have h1 := Matrix.mul_nonsing_inv (Fis A s) hu
  have hs2 : s ^ 2 ≠ 0 := by positivity
  rw [Sig, ← h1, Fis, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hs2, one_smul]

lemma Sig_transpose : (Sig A s)ᵀ = Sig A s := by
  rw [Sig, Matrix.transpose_nonsing_inv, Fis, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

lemma Prj_transpose : (Prj A s)ᵀ = Prj A s := by
  rw [Prj, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Sig_transpose A s hs hF, Matrix.mul_assoc]

lemma Prj_idem : Prj A s * Prj A s = Prj A s := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have h := AtA_Sig A s hs hF
  have : A * Sig A s * Aᵀ * (A * Sig A s * Aᵀ) = s ^ 2 • (A * Sig A s * Aᵀ) := by
    calc A * Sig A s * Aᵀ * (A * Sig A s * Aᵀ) = A * Sig A s * ((Aᵀ * A) * Sig A s) * Aᵀ := by
          simp only [Matrix.mul_assoc]
      _ = s ^ 2 • (A * Sig A s * Aᵀ) := by
          rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [Prj, Matrix.smul_mul, Matrix.mul_smul, this, smul_smul, smul_smul]
  congr 1
  field_simp

lemma one_sub_Prj_sq : (1 - Prj A s)ᵀ * (1 - Prj A s) = 1 - Prj A s := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Prj_transpose A s hs hF, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_sub, Prj_idem A s hs hF]
  simp

/-- The exponent identity. -/
lemma expo (v : J → ℝ) :
    (Aᵀ *ᵥ v) ⬝ᵥ (Sig A s *ᵥ (Aᵀ *ᵥ v)) + s ^ 2 * (((1 - Prj A s) *ᵥ v) ⬝ᵥ ((1 - Prj A s) *ᵥ v))
      = s ^ 2 * (v ⬝ᵥ v) := by
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have h1 : s ^ 2 * (v ⬝ᵥ (Prj A s *ᵥ v)) = (Aᵀ *ᵥ v) ⬝ᵥ (Sig A s *ᵥ (Aᵀ *ᵥ v)) := by
    rw [Prj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs2,
      one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      ← mulVec_transpose]
  have h2 : ((1 - Prj A s) *ᵥ v) ⬝ᵥ ((1 - Prj A s) *ᵥ v) = v ⬝ᵥ v - v ⬝ᵥ (Prj A s *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec,
      one_sub_Prj_sq A s hs hF, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  rw [← h1, h2]; ring

end facts

/-- **Sufficiency (law form).** -/
lemma suff_measure (A : Matrix J ι ℝ) (s : ℝ) (hs : 0 < s) (hF : (Fis A s).PosDef)
    (c : EuclideanSpace ℝ J) (θ : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ J)).map (fun g => c + mat A θ + s • g) =
      ((multivariateGaussian θ (Sig A s)).prod (stdGaussian (EuclideanSpace ℝ J))).map
        (fun p => c + mat A p.1 + s • mat (1 - Prj A s) p.2) := by
  have hSp : (Sig A s).PosSemidef := hF.inv.posSemidef
  set μ' := (multivariateGaussian θ (Sig A s)).map (mat A) with hμ'
  set ν' := (stdGaussian (EuclideanSpace ℝ J)).map (fun h => s • mat (1 - Prj A s) h) with hν'
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map (by fun_prop)
  have : IsProbabilityMeasure ν' := Measure.isProbabilityMeasure_map (by fun_prop)
  have hR : ((multivariateGaussian θ (Sig A s)).prod (stdGaussian (EuclideanSpace ℝ J))).map
        (fun p => c + mat A p.1 + s • mat (1 - Prj A s) p.2) =
      ((μ'.prod ν').map (fun q => q.1 + q.2)).map (fun z => c + z) := by
    have hf : Measurable (mat A) := (mat A).continuous.measurable
    have hg : Measurable (fun h : EuclideanSpace ℝ J => s • mat (1 - Prj A s) h) :=
      ((mat (1 - Prj A s)).continuous.const_smul s).measurable
    rw [hμ', hν', Measure.map_prod_map _ _ hf hg,
      Measure.map_map (by fun_prop) (hf.prodMap hg), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    simp [add_assoc]
  rw [hR]
  apply Measure.ext_of_charFun
  funext ξ
  rw [show (fun g : EuclideanSpace ℝ J => c + mat A θ + s • g) =
      (fun g => (c + mat A θ) + s • g) from rfl, charFun_std_shift', charFun_map_const_add,
    charFun_map_add_prod_eq_mul, Pi.mul_apply, hμ', charFun_map_mat,
    charFun_multivariateGaussian hSp, hν',
    charFun_map_smul_comp (by fun_prop), charFun_map_mat, charFun_stdGaussian,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hE := expo A s hs hF (ofLp ξ)
  have hT : (1 - Prj A s)ᵀ = 1 - Prj A s := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Prj_transpose A s hs hF]
  rw [inner_add_left, inner_mat, real_inner_comm θ]
  simp only [← ofReal_pow, norm_sq_eq_dot]
  rw [ofLp_mat, ofLp_mat, hT, WithLp.ofLp_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hE
  push_cast at hC ⊢
  linear_combination (1 / 2 : ℂ) * hC

/-- The averaged rule on the sufficient statistic. -/
noncomputable def psi (A : Matrix J ι ℝ) (s : ℝ) (c : EuclideanSpace ℝ J)
    (Φ : EuclideanSpace ℝ J → ℝ) (t : EuclideanSpace ℝ ι) : ℝ :=
  ∫ h, Φ (c + mat A t + s • mat (1 - Prj A s) h) ∂(stdGaussian (EuclideanSpace ℝ J))

lemma measurable_F (A : Matrix J ι ℝ) (s : ℝ) (c : EuclideanSpace ℝ J) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ J =>
      c + mat A p.1 + s • mat (1 - Prj A s) p.2) := by
  have h1 : Continuous (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ J =>
      c + mat A p.1 + s • mat (1 - Prj A s) p.2) := by
    exact (continuous_const.add ((mat A).continuous.comp continuous_fst)).add
      (((mat (1 - Prj A s)).continuous.comp continuous_snd).const_smul s)
  exact h1.measurable

lemma psi_rule (A : Matrix J ι ℝ) (s : ℝ) (c : EuclideanSpace ℝ J)
    (Φ : EuclideanSpace ℝ J → ℝ) (hΦm : Measurable Φ) (hΦb : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1) :
    Measurable (psi A s c Φ) ∧ ∀ t, 0 ≤ psi A s c Φ t ∧ psi A s c Φ t ≤ 1 := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · exact ((hΦm.comp (measurable_F A s c)).stronglyMeasurable.integral_prod_right'
      (ν := stdGaussian (EuclideanSpace ℝ J))).measurable
  · exact integral_nonneg (fun h => (hΦb _).1)
  · have hint : Integrable (fun h => Φ (c + mat A t + s • mat (1 - Prj A s) h))
        (stdGaussian (EuclideanSpace ℝ J)) := by
      refine Integrable.of_bound ?_ 1 (ae_of_all _ (fun h => ?_))
      · exact (hΦm.comp ((measurable_F A s c).comp (measurable_prodMk_left (x := t)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hΦb (c + mat A t + s • mat (1 - Prj A s) h)]
    calc psi A s c Φ t ≤ ∫ _h, (1 : ℝ) ∂(stdGaussian (EuclideanSpace ℝ J)) :=
          integral_mono hint (integrable_const _) (fun h => (hΦb _).2)
      _ = 1 := by simp

/-- **Sufficiency (integral form).** -/
lemma suff_integral (A : Matrix J ι ℝ) (s : ℝ) (hs : 0 < s) (hF : (Fis A s).PosDef)
    (c : EuclideanSpace ℝ J) (θ : EuclideanSpace ℝ ι)
    (Φ : EuclideanSpace ℝ J → ℝ) (hΦm : Measurable Φ) (hΦb : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1) :
    ∫ g, Φ (c + mat A θ + s • g) ∂(stdGaussian (EuclideanSpace ℝ J)) =
      ∫ t, psi A s c Φ t ∂(multivariateGaussian θ (Sig A s)) := by
  have hg : Measurable (fun g : EuclideanSpace ℝ J => c + mat A θ + s • g) := by fun_prop
  have h1 := integral_map (μ := stdGaussian (EuclideanSpace ℝ J)) hg.aemeasurable
    hΦm.aestronglyMeasurable
  rw [← h1, suff_measure A s hs hF c θ,
    integral_map (measurable_F A s c).aemeasurable hΦm.aestronglyMeasurable]
  rw [integral_prod]
  · rfl
  · refine Integrable.of_bound (hΦm.comp (measurable_F A s c)).aestronglyMeasurable 1
      (ae_of_all _ (fun p => ?_))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hΦb (c + mat A p.1 + s • mat (1 - Prj A s) p.2)]

end HigherOrderId.Certify.Dev.T5.PartC
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory WithLp

namespace HigherOrderId.Certify.Dev.T5.PartC
open HigherOrderId.Certify

lemma sd_pos (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) : 0 < sd σ n := by
  have h := sd_sq_eq σ n hn
  have h2 : 0 < sd σ n ^ 2 := by rw [h]; positivity
  have h3 : 0 ≤ sd σ n := Real.sqrt_nonneg _
  rcases h3.eq_or_lt with h4 | h4
  · rw [← h4] at h2; simp at h2
  · exact h4

lemma frobNorm_submatrix {κ μ' : Type*} [Fintype κ] [Fintype μ'] (X : Matrix κ κ ℝ)
    (e : μ' ≃ κ) : frobNorm (X.submatrix e e) = frobNorm X := by
  unfold frobNorm frobInner
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [Equiv.sum_comp e (fun i => ∑ j, X i (e j) * X i (e j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Equiv.sum_comp e (fun j => X i j * X i j)

lemma dot_pos {κ : Type*} [Fintype κ] {v : κ → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
    (Ne.symm (mt dotProduct_self_eq_zero.mp hv))

/-- Reindexed design matrix. -/
noncomputable def Ar {d E D' : ℕ} (D : Design d E) (e : ThetaIdx d ≃ Fin D') :
    Matrix (Jx d E) (Fin D') ℝ :=
  (Amat D).submatrix id e.symm

lemma Fis_Ar {d E D' : ℕ} (D : Design d E) (e : ThetaIdx d ≃ Fin D') (s : ℝ) :
    Fis (Ar D e) s = (Fis (Amat D) s).submatrix e.symm e.symm := by
  ext k l
  simp [Fis, Ar, Matrix.mul_apply]

lemma Amat_mulVec_reindex {d E D' : ℕ} (D : Design d E) (e : ThetaIdx d ≃ Fin D')
    (θ : EuclideanSpace ℝ (Fin D')) :
    Amat D *ᵥ (fun t => θ (e t)) = Ar D e *ᵥ ofLp θ := by
  funext j
  simp only [mulVec, dotProduct, Ar, Matrix.submatrix_apply, id]
  exact (Equiv.sum_comp e.symm (fun t => Amat D j t * θ (e t))).symm.trans (by simp)

lemma norm_reindex {d D' : ℕ} (e : ThetaIdx d ≃ Fin D') (θ : EuclideanSpace ℝ (Fin D')) :
    ∑ t, (θ (e t)) ^ 2 = ‖θ‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Equiv.sum_comp e (fun k => θ k ^ 2)

/-- The converse, restated verbatim from the Blueprint. -/
theorem converse (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4)
    (c₀ : ℝ)
    (h101 : ∀ (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)), 10 ≤ d → m ≤ md d → 0 < α →
        α ≤ 1 / 2 → 0 < σ → InDesignClass d m N α D → (fullFisherMat D σ).PosDef →
        c₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤ frobNorm (SigmaEff D σ))
    (d m N : ℕ) (α σ R : ℝ) (hd : 10 ≤ d) (hm : m ≤ md d) (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hσ : 0 < σ) (D : Design d (d - m + 1)) (hD : InDesignClass d m N α D)
    (ε : ℝ) (hε0 : 0 < ε) (hεR : ε ≤ R ^ 2)
    (φ : Obs d (d - m + 1) → ℝ) (hφ : IsRandomizedRule φ) (hcert : Certifies D σ R ε δ β φ) :
    cLower δ β * c₀ * rate d m N α σ ≤ ε := by
  obtain ⟨_, _, _, _, hNpos, hn⟩ := hD
  set n := N / (d - m + 1) with hndef
  have hs : 0 < sd σ n := sd_pos σ hσ n hNpos
  have hFis : fullFisherMat D σ = Fis (Amat D) (sd σ n) := by
    rw [fisher_eq' D σ n hNpos hn, Fis]
  -- releases with equal means are equal
  have hlaw : ∀ (b b' : Fin d → ℝ) (Q Q' : Matrix (Fin d) (Fin d) ℝ),
      meanFn D b Q = meanFn D b' Q' → releaseLaw D σ b Q = releaseLaw D σ b' Q' := by
    intro b b' Q Q' h
    rw [releaseLaw_eq_map D σ n hn, releaseLaw_eq_map D σ n hn, h]
  by_cases hPD : (fullFisherMat D σ).PosDef
  · -- the full-rank case: sufficiency + Lemma C.1
    set D' := Fintype.card (ThetaIdx d)
    let e : ThetaIdx d ≃ Fin D' := Fintype.equivFin (ThetaIdx d)
    set A' := Ar D e with hA'
    set s := sd σ n with hsdef
    have hF' : (Fis A' s).PosDef := by
      rw [hA', Fis_Ar, ← hFis]
      exact hPD.submatrix e.symm.injective
    have hSig : Sig A' s = (SigmaEff D σ).submatrix e.symm e.symm := by
      rw [Sig, hA', Fis_Ar, Matrix.inv_submatrix_equiv, SigmaEff, hFis]
    have hfrob : frobNorm (Sig A' s) = frobNorm (SigmaEff D σ) := by
      rw [hSig, frobNorm_submatrix]
    set Φ : EuclideanSpace ℝ (Jx d (d - m + 1)) → ℝ := fun y => φ (toObs y) with hΦ
    have hΦm : Measurable Φ := hφ.1.comp measurable_toObs
    have hΦb : ∀ y, 0 ≤ Φ y ∧ Φ y ≤ 1 := fun y => hφ.2 _
    set c : EuclideanSpace ℝ (Jx d (d - m + 1)) := toLp 2 cvec
    set ψ := psi A' s c Φ with hψ
    have key : ∀ θ : EuclideanSpace ℝ (Fin D'),
        ∫ y, φ y ∂(releaseLaw D σ (thB (fun t => θ (e t))) (thQ (fun t => θ (e t)))) =
          ∫ t, ψ t ∂(multivariateGaussian θ (Sig A' s)) := by
      intro θ
      have hmeasG : ∀ v : Hs d (d - m + 1),
          Measurable (fun g : Hs d (d - m + 1) => toObs (v + sd σ n • g)) :=
        fun v => measurable_toObs.comp (by fun_prop)
      rw [releaseLaw_eq_map D σ n hn,
        integral_map (hmeasG _).aemeasurable hφ.1.aestronglyMeasurable,
        ← suff_integral A' s hs hF' c θ Φ hΦm hΦb]
      congr 1
      funext g
      rw [meanFn_th, Amat_mulVec_reindex]
      rfl
    have hrule := psi_rule A' s c Φ hΦm hΦb
    have hSPD : (Sig A' s).PosDef := hF'.inv
    have hC1 := (lemma_C_1 D' (Sig A' s) hSPD δ β R ε hδ0 hδ1 hβ0 hβ1 hε0 hεR).1 ψ hrule
      (by
        intro θ h1 h2
        rw [← key θ]
        refine hcert.1 _ _ ⟨thQ_symZero _, ?_⟩ ?_
        · rw [energy_th, norm_reindex]; exact h2
        · rw [energy_th, norm_reindex]; exact h1)
      (by
        rw [nullPower, ← key 0]
        have h0 : (fun t => (0 : EuclideanSpace ℝ (Fin D')) (e t)) = 0 := by funext t; simp
        rw [h0, thB_zero, thQ_zero]
        exact hcert.2)
    have h1 := h101 d m N α σ D hd hm hα0 hα1 hσ
      ⟨‹_›, ‹_›, ‹_›, ‹_›, hNpos, hn⟩ hPD
    have hcL : 0 ≤ cLower δ β := Real.sqrt_nonneg _
    rw [hfrob] at hC1
    calc cLower δ β * c₀ * rate d m N α σ
        = cLower δ β * (c₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6)) := by
          rw [rate]; ring
      _ ≤ cLower δ β * frobNorm (SigmaEff D σ) := mul_le_mul_of_nonneg_left h1 hcL
      _ ≤ ε := hC1
  · -- a null direction of the Fisher information makes certification impossible
    exfalso
    obtain ⟨x, hx0, hAx⟩ : ∃ x : ThetaIdx d → ℝ, x ≠ 0 ∧ Amat D *ᵥ x = 0 := by
      by_contra hcon'
      have hcon : ∀ x : ThetaIdx d → ℝ, x ≠ 0 → Amat D *ᵥ x ≠ 0 :=
        fun x hx h => hcon' ⟨x, hx, h⟩
      apply hPD
      rw [hFis, posDef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x hx => ?_⟩
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Fis,
          Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
      · rw [Fis, Matrix.smul_mulVec, dotProduct_smul, star_trivial, ← Matrix.mulVec_mulVec,
          dotProduct_mulVec, ← mulVec_transpose, Matrix.transpose_transpose, smul_eq_mul]
        have hpos : 0 < (Amat D *ᵥ x) ⬝ᵥ (Amat D *ᵥ x) := dot_pos (hcon x hx)
        have : 0 < (sd σ n ^ 2)⁻¹ := by positivity
        positivity
    have hr : 0 < x ⬝ᵥ x := dot_pos hx0
    set τ := Real.sqrt (ε / (x ⬝ᵥ x))
    have hτ : τ ^ 2 = ε / (x ⬝ᵥ x) := Real.sq_sqrt (by positivity)
    set ϑ : ThetaIdx d → ℝ := τ • x
    have hen : energy (thB ϑ) (thQ ϑ) = ε := by
      rw [energy_th]
      have : ∑ t, ϑ t ^ 2 = τ ^ 2 * (x ⬝ᵥ x) := by
        simp only [ϑ, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun t _ => by ring)
      rw [this, hτ]; field_simp
    have hmean : meanFn D (thB ϑ) (thQ ϑ) = meanFn D 0 0 := by
      rw [meanFn_th, meanFn_zero, Matrix.mulVec_smul, hAx, smul_zero, add_zero]
    have h1 := hcert.1 (thB ϑ) (thQ ϑ) ⟨thQ_symZero _, by rw [hen]; exact hεR⟩ (by rw [hen])
    rw [hlaw _ _ _ _ hmean] at h1
    linarith [hcert.2]

end HigherOrderId.Certify.Dev.T5.PartC
end

section
set_option autoImplicit false
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify

/-! ## T3(a): the frame `U`, the complement `V`, the simplex `H` and the design -/

/-- `m ≤ m_d` gives `m(m+1) ≤ 2d`, hence `m < d`. -/
lemma m_bound (d m : ℕ) (hd : 10 ≤ d) (hm : m ≤ md d) : m * (m + 1) ≤ 2 * d ∧ m < d := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt (8 * (d : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hx : 0 ≤ (Real.sqrt (8 * (d : ℝ) + 1) - 1) / 2 := by linarith
  have h1 : (m : ℝ) ≤ (Real.sqrt (8 * (d : ℝ) + 1) - 1) / 2 :=
    le_trans (Nat.cast_le.mpr hm) (Nat.floor_le hx)
  have h2 : 2 * (m : ℝ) + 1 ≤ Real.sqrt (8 * (d : ℝ) + 1) := by linarith
  have h3 : (2 * (m : ℝ) + 1) ^ 2 ≤ 8 * (d : ℝ) + 1 := by
    have := pow_le_pow_left₀ (by positivity) h2 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have h4 : ((m * (m + 1) : ℕ) : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by push_cast; nlinarith
  have h5 : m * (m + 1) ≤ 2 * d := by exact_mod_cast h4
  refine ⟨h5, ?_⟩
  by_contra hc
  nlinarith

lemma card_lt_pairs (m : ℕ) :
    2 * Fintype.card {p : Fin m × Fin m // p.1 < p.2} + m = m * m := by
  rw [Fintype.card_subtype]
  have h1 : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Fin m × Fin m => p.2 < p.1)).card :=
    Finset.card_nbij' Prod.swap Prod.swap (fun p hp => by simpa using hp)
      (fun p hp => by simpa using hp) (fun p _ => rfl) (fun p _ => rfl)
  have h2 : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 = p.2)).card = m := by
    have : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 = p.2)) =
        (Finset.univ : Finset (Fin m)).diag := by
      ext p; simp [Finset.mem_diag]
    rw [this, Finset.diag_card]; simp
  have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun p : Fin m × Fin m => p.1 < p.2)
  have h4 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin m × Fin m => ¬ p.1 < p.2))
    (fun p : Fin m × Fin m => p.2 < p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h4
  have e1 : Finset.univ.filter (fun p : Fin m × Fin m => ¬ p.1 < p.2 ∧ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin m × Fin m => p.2 < p.1) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨not_lt.mpr h.le, h⟩
  have e2 : Finset.univ.filter (fun p : Fin m × Fin m => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin m × Fin m => p.1 = p.2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    · intro h; rw [h]; exact ⟨lt_irrefl _, lt_irrefl _⟩
  rw [e1, e2, h2] at h4
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h3
  omega

lemma exists_frame_emb (d m : ℕ) (hd : 10 ≤ d) (hm : m ≤ md d) :
    Nonempty (FrameRows m ↪ Fin d) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h1 := card_lt_pairs m
  have h2 := (m_bound d m hd hm).1
  nlinarith

lemma Uw_orth {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) (hw : 0 < w) :
    (Uw ι w)ᵀ * Uw ι w = 1 := by
  obtain ⟨Ri, hRit, hRRi, hRiR, _, hU⟩ := Dev.B2.sqrtS_props ι w hw
  have hS : (0 : Matrix (Fin m) (Fin m) ℝ) ≤ Sw ι w := by
    have := Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self (Gw ι w))
    simpa [Sw, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hRR := CFC.sqrt_mul_sqrt_self _ hS
  rw [hU, Matrix.transpose_mul, hRit]
  calc Ri * (Gw ι w)ᵀ * (Gw ι w * Ri) = Ri * Sw ι w * Ri := by
        rw [Sw]; simp only [Matrix.mul_assoc]
    _ = (Ri * CFC.sqrt (Sw ι w)) * (CFC.sqrt (Sw ι w) * Ri) := by
        conv_lhs => rw [← hRR]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hRiR, hRRi, Matrix.one_mul]

/-- An orthonormal complement of the columns of `W`, with the completeness relation. -/
lemma exists_compl {n k m : ℕ} (hkm : k + m = n) (W : Matrix (Fin n) (Fin k) ℝ)
    (hW : Wᵀ * W = 1) : ∃ U : Matrix (Fin n) (Fin m) ℝ, Uᵀ * U = 1 ∧ Uᵀ * W = 0 ∧
      W * Wᵀ + U * Uᵀ = 1 := by
  let v : Fin k ⊕ Fin m → EuclideanSpace ℝ (Fin n) :=
    Sum.elim (fun l => WithLp.toLp 2 (fun a => W a l)) (fun _ => 0)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin k ⊕ Fin m) := by
    simp [hkm]
  have hv : Orthonormal ℝ ((Set.range (Sum.inl : Fin k → Fin k ⊕ Fin m)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨l, rfl⟩ := hi
    obtain ⟨l', rfl⟩ := hj
    show inner ℝ (v (Sum.inl l)) (v (Sum.inl l')) = _
    simp only [v, Sum.elim_inl, EuclideanSpace.inner_toLp_toLp, Subtype.mk.injEq, Sum.inl.injEq]
    have := congrFun (congrFun hW l) l'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    have key : ((fun a => W a l') ⬝ᵥ star fun a => W a l) = ∑ j, W j l * W j l' := by
      simp [dotProduct, mul_comm]
    rw [key, this]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (by subst h1; rfl) h2
    · have := congrArg Subtype.val h2; simp at this; exact absurd this h1
    · rfl
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  have hbo := orthonormal_iff_ite.mp b.orthonormal
  have hbl : ∀ l a, (b (Sum.inl l)).ofLp a = W a l := by
    intro l a; rw [hb (Sum.inl l) ⟨l, rfl⟩]; simp [v]
  refine ⟨Matrix.of fun a c => (b (Sum.inr c)).ofLp a, ?_, ?_, ?_⟩
  · ext c c'
    have := hbo (Sum.inr c) (Sum.inr c')
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Sum.inr.injEq,
      Matrix.of_apply] at this ⊢
    rw [← this]
    simp [dotProduct, mul_comm]
  · ext c l
    have := hbo (Sum.inr c) (Sum.inl l)
    rw [hb (Sum.inl l) ⟨l, rfl⟩, EuclideanSpace.inner_eq_star_dotProduct] at this
    simp only [v, Sum.elim_inl, reduceCtorEq, if_false] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Matrix.of_apply]
    rw [← this]
    simp [dotProduct, mul_comm]
  · ext a a'
    have h := b.sum_inner_mul_inner (EuclideanSpace.single a (1 : ℝ))
      (EuclideanSpace.single a' (1 : ℝ))
    simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
      one_mul, mul_one, Fintype.sum_sum_type] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply]
    simp only [hbl, starRingEnd_apply, star_trivial] at h
    convert h using 1
    simp [eq_comm]

end HigherOrderId.Certify.Dev.T5.PartA

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify

/-- The frame `U` (`U_w`, `w = m^{1/4}`, for `m ≥ 1`; empty for `m = 0`). -/
lemma exists_U (d m : ℕ) (hd : 10 ≤ d) (hm : m ≤ md d) :
    ∃ U : Matrix (Fin d) (Fin m) ℝ, Uᵀ * U = 1 ∧ FullColRank U ∧
      (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) := by
  obtain ⟨ι⟩ := exists_frame_emb d m hd hm
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    refine ⟨0, Subsingleton.elim _ _, fun B _ _ => Subsingleton.elim _ _, fun h => ?_⟩
    omega
  · have hw : 0 < (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast h0) _
    exact ⟨Uw ι _, Uw_orth ι _ hw, Dev.B2.fullColRank_Uw ι _ hw, fun _ => ⟨ι, rfl⟩⟩

/-- The centred simplex directions `H` (`(k+1) × k`). -/
lemma exists_H (k : ℕ) : ∃ H : Matrix (Fin (k + 1)) (Fin k) ℝ, Hᵀ * H = 1 ∧
    (∀ l, ∑ e, H e l = 0) ∧ (∀ e, ∑ l, H e l ^ 2 = 1 - 1 / ((k : ℝ) + 1)) := by
  set c : ℝ := 1 / Real.sqrt ((k : ℝ) + 1)
  have hc2 : c ^ 2 = 1 / ((k : ℝ) + 1) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; simp
  let u : Matrix (Fin (k + 1)) (Fin 1) ℝ := Matrix.of fun _ _ => c
  have hu : uᵀ * u = 1 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, u, Matrix.of_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← sq, hc2]
    push_cast; field_simp
  obtain ⟨H, hH, hHu, hrows⟩ := exists_compl (n := k + 1) (k := 1) (m := k) (by omega) u hu
  refine ⟨H, hH, fun l => ?_, fun e => ?_⟩
  · have := congrFun (congrFun hHu l) 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, u,
      Matrix.of_apply] at this
    rw [← Finset.sum_mul] at this
    have hc : c ≠ 0 := by positivity
    exact (mul_eq_zero.mp this).resolve_right hc
  · have := congrFun (congrFun hrows e) e
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
      u, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton] at this
    rw [← hc2]
    have h2 : ∑ l, H e l ^ 2 = ∑ l, H e l * H e l := by simp [sq]
    rw [h2]; linarith [show c * c = c ^ 2 by ring]

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify

lemma sum_vecMulVec_rows {E d : ℕ} (X : Matrix (Fin E) (Fin d) ℝ) :
    ∑ e, vecMulVec (X e) (X e) = Xᵀ * X := by
  ext a b
  simp [Matrix.sum_apply, vecMulVec_apply, Matrix.mul_apply]

/-- The regular-simplex design with `V ⟂ U`. -/
lemma exists_design (d m N : ℕ) (α : ℝ) (hd : 10 ≤ d) (hm : m ≤ md d) (hα : 0 < α)
    (hdvd : (d - m + 1) ∣ N) (hN : 0 < N / (d - m + 1)) :
    ∃ (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin (d - m)) ℝ)
      (D : Design d (d - m + 1)),
      Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ Uᵀ * V = 0 ∧ FullColRank U ∧
      (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) ∧
      InDesignClass d m N α D ∧ ∑ e, D.x e = 0 ∧
      ∑ e, vecMulVec (D.x e) (D.x e) =
        ((((d - m + 1 : ℕ) : ℝ) * α ^ 2 / ((d - m : ℕ) : ℝ)) • (V * Vᵀ)) := by
  have hmd := (m_bound d m hd hm).2
  obtain ⟨U, hU, hfull, hUw⟩ := exists_U d m hd hm
  obtain ⟨V, hV, hVU, -⟩ := exists_compl (n := d) (k := m) (m := d - m) (by omega) U hU
  obtain ⟨H, hH, hHs, hHr⟩ := exists_H (d - m)
  set kR : ℝ := ((d - m : ℕ) : ℝ) with hkR
  have hk : 0 < kR := by rw [hkR]; exact_mod_cast (by omega : 0 < d - m)
  have hE : ((d - m + 1 : ℕ) : ℝ) = kR + 1 := by rw [hkR]; push_cast; ring
  set γ : ℝ := α * Real.sqrt ((kR + 1) / kR) with hγ
  have hγ2 : γ ^ 2 = α ^ 2 * ((kR + 1) / kR) := by
    rw [hγ, mul_pow, Real.sq_sqrt (by positivity)]
  set X : Matrix (Fin (d - m + 1)) (Fin d) ℝ := γ • (H * Vᵀ) with hX
  let D : Design d (d - m + 1) := ⟨fun e => X e, fun _ => N / (d - m + 1)⟩
  have hXX : Xᵀ * X = γ ^ 2 • (V * Vᵀ) := by
    rw [hX, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← sq]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ, hH, Matrix.one_mul]
  have hcov : ∑ e, vecMulVec (D.x e) (D.x e) = γ ^ 2 • (V * Vᵀ) := by
    rw [← hXX, ← sum_vecMulVec_rows]
  have hXe : ∀ e a, X e a = γ * ∑ l, H e l * V a l := by
    intro e a; simp [hX, Matrix.mul_apply, Matrix.transpose_apply]
  have hsum : ∑ e, D.x e = 0 := by
    funext a
    rw [Finset.sum_apply]
    simp only [D, hXe, Pi.zero_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hHs, zero_mul, Finset.sum_const_zero, mul_zero]
  have hnorm : ∀ e, ∑ i, D.x e i ^ 2 = α ^ 2 := by
    intro e
    have h1 : ∑ i, D.x e i ^ 2 = (X * Xᵀ) e e := by
      simp only [D, Matrix.mul_apply, Matrix.transpose_apply, sq]
    have h2 : X * Xᵀ = γ ^ 2 • (H * Hᵀ) := by
      rw [hX, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← sq]
      congr 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]
    rw [h1, h2, Matrix.smul_apply, smul_eq_mul]
    have h3 : (H * Hᵀ) e e = ∑ l, H e l ^ 2 := by simp [Matrix.mul_apply, sq]
    rw [h3, hHr e, hγ2]
    have hk0 := hk.ne'
    field_simp
    ring
  refine ⟨U, V, D, hU, hV, ?_, hfull, hUw, ⟨hnorm, hsum, ⟨V, hV, ?_⟩, hdvd, hN, fun _ => rfl⟩,
    hsum, ?_⟩
  · rw [← Matrix.transpose_transpose (Uᵀ * V), Matrix.transpose_mul, Matrix.transpose_transpose,
      hVU, Matrix.transpose_zero]
  · rw [hcov, smul_smul, hγ2, hE, ← hkR]
    congr 1
    have hk0 := hk.ne'
    field_simp
  · rw [hcov, hγ2, hE]
    congr 1
    field_simp

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify

/-! ## T3(b): linearity of the completion estimator `Q̂` -/

section lin
variable {d m k : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)

lemma rhat_add (M M' : Matrix (Fin d) (Fin k) ℝ) :
    rhat U V (M + M') = rhat U V M + rhat U V M' := by
  simp only [rhat, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, smul_add]
  abel

lemma rhat_smul (r : ℝ) (M : Matrix (Fin d) (Fin k) ℝ) :
    rhat U V (r • M) = r • rhat U V M := by
  simp only [rhat, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, smul_add]
  congr 1
  rw [smul_comm (1 / 2 : ℝ) r (Vᵀ * M), smul_comm (1 / 2 : ℝ) r (Vᵀ * M)ᵀ, ← smul_add,
    Matrix.mul_smul, Matrix.smul_mul]

lemma Mc_add (X Y : Matrix (Fin d) (Fin d) ℝ) : Mc U (X + Y) = Mc U X + Mc U Y := by
  have : diagVec (X + Y) = diagVec X + diagVec Y := by funext a; simp [diagVec]
  simp only [Mc, this, Matrix.mulVec_add]

lemma Mc_smul (r : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) : Mc U (r • X) = r • Mc U X := by
  have : diagVec (r • X) = r • diagVec X := by funext a; simp [diagVec]
  simp only [Mc, this, Matrix.mulVec_smul]

lemma Lmap_add (X Y : Matrix (Fin d) (Fin d) ℝ) : Lmap U (X + Y) = Lmap U X + Lmap U Y := by
  have : Mmap U (X + Y) = Mmap U X + Mmap U Y := by
    simp only [Mmap, Mc_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  simp only [Lmap, this, Matrix.mul_add, Matrix.add_mul]
  abel

lemma Lmap_smul (r : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) : Lmap U (r • X) = r • Lmap U X := by
  have : Mmap U (r • X) = r • Mmap U X := by
    simp only [Mmap, Mc_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  simp only [Lmap, this, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

lemma P0_add (X Y : Matrix (Fin d) (Fin d) ℝ) : P0 (X + Y) = P0 X + P0 Y := by
  ext i j; simp only [P0, Matrix.add_apply]; split_ifs <;> ring

lemma P0_smul (r : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) : P0 (r • X) = r • P0 X := by
  ext i j; simp only [P0, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring

/-- `Q̂` as a linear map. -/
noncomputable def QhatL : Matrix (Fin d) (Fin k) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := Qhat U V
  map_add' M M' := by simp only [Qhat, rhat_add, Lmap_add, P0_add]
  map_smul' r M := by simp only [Qhat, rhat_smul, Lmap_smul, P0_smul, RingHom.id_apply]

lemma Qhat_expand (M : Matrix (Fin d) (Fin k) ℝ) (i j : Fin d) :
    Qhat U V M i j = ∑ c : Fin d × Fin k, noiseMap U V (i, j) c * M c.1 c.2 := by
  have hM : M = ∑ a, ∑ l, M a l • Matrix.single a l (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp_rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have h : Qhat U V M = ∑ a, ∑ l, M a l • Qhat U V (Matrix.single a l (1 : ℝ)) := by
    change QhatL U V M = _
    conv_lhs => rw [hM]
    simp only [map_sum, map_smul]
    rfl
  rw [h, Matrix.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [Matrix.smul_apply, smul_eq_mul, noiseMap]
  ring

end lin

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify HigherOrderId.Certify.Dev.T5.PartC

/-! ## T3(b,c): the explicit estimator `ϑ̂ = (b̂, Q̂)` as a matrix on the flat release -/

variable {d E k m : ℕ}

/-- `Y_{e,l} = x_eᵀ v_l`. -/
def Ymat (D : Design d E) (V : Matrix (Fin d) (Fin k) ℝ) : Matrix (Fin E) (Fin k) ℝ :=
  Matrix.of fun e l => D.x e ⬝ᵥ (fun b => V b l)

/-- The estimator matrix: `b̂ = E⁻¹ Σ_e ĝ_e`, `Q̂ = Q̂(κ Σ_e ĝ_e x_eᵀ V)`; value releases unused. -/
noncomputable def Tm (D : Design d E) (U : Matrix (Fin d) (Fin m) ℝ)
    (V : Matrix (Fin d) (Fin k) ℝ) (κ : ℝ) : Matrix (ThetaIdx d) (Jx d E) ℝ :=
  fun t j => Option.elim j.2 0 (fun a' => Sum.elim (fun a => if a' = a then ((E : ℝ))⁻¹ else 0)
    (fun p => κ * ∑ l, noiseMap U V p.1 (a', l) * Ymat D V j.1 l) t)

/-- The (scaled) estimator covariance pattern. -/
noncomputable def Gm (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ) (Einv κ : ℝ) :
    Matrix (ThetaIdx d) (ThetaIdx d) ℝ
  | .inl a, .inl a' => if a = a' then Einv else 0
  | .inr p, .inr q => κ * ∑ c : Fin d × Fin k, noiseMap U V p.1 c * noiseMap U V q.1 c
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0

section est
variable (D : Design d E) (U : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin k) ℝ)
  (κ c : ℝ)

lemma Tm_mulVec (y : Jx d E → ℝ) (t : ThetaIdx d) :
    (Tm D U V κ *ᵥ y) t = ∑ e, ∑ a, Tm D U V κ t (e, some a) * y (e, some a) := by
  simp [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_option, Tm]

lemma Tm_mul (t t' : ThetaIdx d) :
    (Tm D U V κ * (Tm D U V κ)ᵀ) t t' =
      ∑ e, ∑ a, Tm D U V κ t (e, some a) * Tm D U V κ t' (e, some a) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_option, Tm]

lemma Tm_inl (a : Fin d) (e : Fin E) (a' : Fin d) :
    Tm D U V κ (Sum.inl a) (e, some a') = if a' = a then ((E : ℝ))⁻¹ else 0 := rfl

lemma Tm_inr (p : {p : Fin d × Fin d // p.1 < p.2}) (e : Fin E) (a' : Fin d) :
    Tm D U V κ (Sum.inr p) (e, some a') = κ * ∑ l, noiseMap U V p.1 (a', l) * Ymat D V e l :=
  rfl

section hyp
variable (hsum : ∑ e, D.x e = 0)
  (hcov : ∑ e, vecMulVec (D.x e) (D.x e) = c • (V * Vᵀ)) (hV : Vᵀ * V = 1)
include hsum

lemma Y_colsum (l : Fin k) : ∑ e, Ymat D V e l = 0 := by
  simp only [Ymat, Matrix.of_apply]
  rw [← sum_dotProduct, hsum, zero_dotProduct]

lemma Qx_sum (Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d) : ∑ e, (Q *ᵥ D.x e) a = 0 := by
  rw [← Finset.sum_apply, ← Matrix.mulVec_sum, hsum, Matrix.mulVec_zero, Pi.zero_apply]

include hcov hV

lemma Xm_gram : (Matrix.of fun e a => D.x e a)ᵀ * (Matrix.of fun e a => D.x e a) = c • (V * Vᵀ) := by
  rw [← hcov, ← sum_vecMulVec_rows]
  rfl

lemma Y_eq : Ymat D V = (Matrix.of fun e a => D.x e a) * V := by
  ext e l; simp [Ymat, Matrix.mul_apply, dotProduct]

lemma Y_gram : (Ymat D V)ᵀ * Ymat D V = c • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [Y_eq D V c hsum hcov hV, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ V,
    Xm_gram D V c hsum hcov hV, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Vᵀ, hV, Matrix.one_mul]

lemma Mg_mean (hκ : κ * c = 1) (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d)
    (l : Fin k) : κ * ∑ e, mechGrad b Q (D.x e) a * Ymat D V e l = (Q * V) a l := by
  have h1 : ∑ e, mechGrad b Q (D.x e) a * Ymat D V e l =
      b a * ∑ e, Ymat D V e l + ((Q * (Matrix.of fun e a => D.x e a)ᵀ) * Ymat D V) a l := by
    simp only [mechGrad, Pi.add_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
  rw [h1, Y_colsum D V hsum, mul_zero, zero_add, Y_eq D V c hsum hcov hV,
    show Q * (Matrix.of fun e a => D.x e a)ᵀ * ((Matrix.of fun e a => D.x e a) * V) =
      Q * ((Matrix.of fun e a => D.x e a)ᵀ * (Matrix.of fun e a => D.x e a)) * V by
        simp only [Matrix.mul_assoc],
    Xm_gram D V c hsum hcov hV, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, hV, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hκ,
    one_mul]

/-- The estimator reproduces `(b, Q)` from the noiseless release. -/
lemma Tm_mean (hκ : κ * c = 1) (hE : (E : ℝ) ≠ 0)
    (hrep : ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsSymZeroDiag Q → Qhat U V (Q * V) = Q)
    (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsSymZeroDiag Q) :
    (∀ a, (Tm D U V κ *ᵥ meanFn D b Q) (Sum.inl a) = b a) ∧
    (∀ p, (Tm D U V κ *ᵥ meanFn D b Q) (Sum.inr p) = Q p.1.1 p.1.2) := by
  constructor
  · intro a
    rw [Tm_mulVec]
    simp only [Tm_inl, meanFn, Option.elim, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    simp only [mechGrad, Pi.add_apply, Finset.sum_add_distrib, Qx_sum D hsum, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro p
    rw [Tm_mulVec]
    simp only [Tm_inr, meanFn, Option.elim]
    have h : ∀ e a', κ * (∑ l, noiseMap U V p.1 (a', l) * Ymat D V e l) *
        mechGrad b Q (D.x e) a' =
        ∑ l, noiseMap U V p.1 (a', l) * (κ * (mechGrad b Q (D.x e) a' * Ymat D V e l)) := by
      intro e a'
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    simp_rw [h]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin E)))]
    simp_rw [← Finset.mul_sum, Mg_mean D V κ c hsum hcov hV hκ b Q]
    rw [show Q p.1.1 p.1.2 = Qhat U V (Q * V) p.1.1 p.1.2 by rw [hrep Q hQ], Qhat_expand,
      Fintype.sum_prod_type]

lemma Y_quad (A B : Fin k → ℝ) :
    ∑ e, (∑ l, A l * Ymat D V e l) * (∑ l, B l * Ymat D V e l) = c * ∑ l, A l * B l := by
  have hA : ∀ e, ∑ l, A l * Ymat D V e l = (Ymat D V *ᵥ A) e := by
    intro e; simp only [mulVec, dotProduct]; exact Finset.sum_congr rfl (fun l _ => by ring)
  have hB : ∀ e, ∑ l, B l * Ymat D V e l = (Ymat D V *ᵥ B) e := by
    intro e; simp only [mulVec, dotProduct]; exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [hA, hB]
  change (Ymat D V *ᵥ A) ⬝ᵥ (Ymat D V *ᵥ B) = _
  rw [dotProduct_mulVec, ← mulVec_transpose, Matrix.mulVec_mulVec, Y_gram D V c hsum hcov hV,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul]
  rfl

lemma Tm_gram (hκ : κ * c = 1) (hE : (E : ℝ) ≠ 0) :
    Tm D U V κ * (Tm D U V κ)ᵀ = Gm U V ((E : ℝ))⁻¹ κ := by
  ext t t'
  rw [Tm_mul]
  rcases t with a | p <;> rcases t' with a' | q
  · simp only [Tm_inl, Gm, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs with h
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp
  · simp only [Tm_inl, Tm_inr, Gm, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have : ∀ e, (E : ℝ)⁻¹ * (κ * (noiseMap U V q.1 (a, l) * Ymat D V e l)) =
        ((E : ℝ)⁻¹ * κ * noiseMap U V q.1 (a, l)) * Ymat D V e l := fun e => by ring
    simp_rw [this, ← Finset.mul_sum, Y_colsum D V hsum, mul_zero]
  · simp only [Tm_inl, Tm_inr, Gm, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    have : ∀ e, (κ * ∑ l, noiseMap U V p.1 (a', l) * Ymat D V e l) * (E : ℝ)⁻¹ =
        ∑ l, (κ * noiseMap U V p.1 (a', l) * (E : ℝ)⁻¹) * Ymat D V e l := by
      intro e; rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, Y_colsum D V hsum, mul_zero, Finset.sum_const_zero]
  · simp only [Tm_inr, Gm]
    rw [Finset.sum_comm]
    have : ∀ b : Fin d, ∑ e, (κ * ∑ l, noiseMap U V p.1 (b, l) * Ymat D V e l) *
        (κ * ∑ l, noiseMap U V q.1 (b, l) * Ymat D V e l) =
        κ * ((κ * c) * ∑ l, noiseMap U V p.1 (b, l) * noiseMap U V q.1 (b, l)) := by
      intro b
      have h := Y_quad D V c hsum hcov hV (fun l => noiseMap U V p.1 (b, l))
        (fun l => noiseMap U V q.1 (b, l))
      rw [show (κ * c) * ∑ l, noiseMap U V p.1 (b, l) * noiseMap U V q.1 (b, l) =
          κ * (c * ∑ l, noiseMap U V p.1 (b, l) * noiseMap U V q.1 (b, l)) by ring, ← h,
        Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    simp_rw [this, hκ, one_mul, ← Finset.mul_sum, Fintype.sum_prod_type]

end hyp

end est

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Complex WithLp

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify.Dev.T5.PartC

/-! ## T3(c,d): the law of a linear estimator, and positive definiteness of its covariance -/

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

lemma posSemidef_LLt (L : Matrix ι J ℝ) (s : ℝ) : (s ^ 2 • (L * Lᵀ)).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose L
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul (sq_nonneg s)

/-- `a + s L g` with `g` standard Gaussian is `N(a, s² L Lᵀ)`. -/
lemma std_map_affine (L : Matrix ι J ℝ) (s : ℝ) (a : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ J)).map (fun g => a + s • mat L g) =
      multivariateGaussian a (s ^ 2 • (L * Lᵀ)) := by
  apply Measure.ext_of_charFun
  funext ξ
  rw [show (fun g : EuclideanSpace ℝ J => a + s • mat L g) =
      (fun z => a + z) ∘ (fun g => s • mat L g) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_const_add,
    charFun_map_smul_comp (mat L).continuous.measurable.aemeasurable, charFun_map_mat,
    charFun_stdGaussian, charFun_multivariateGaussian (posSemidef_LLt L s), ← Complex.exp_add]
  congr 1
  rw [real_inner_comm, ← ofReal_pow, norm_sq_eq_dot, ofLp_mat, WithLp.ofLp_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
    Matrix.transpose_transpose, dotProduct_comm (L *ᵥ _)]
  push_cast
  ring

/-- `s² L Lᵀ` is positive definite when `L` is onto. -/
lemma posDef_LLt (L : Matrix ι J ℝ) (s : ℝ) (hs : s ≠ 0)
    (hsurj : ∀ x : ι → ℝ, ∃ y, L *ᵥ y = x) : (s ^ 2 • (L * Lᵀ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [Matrix.smul_mulVec, dotProduct_smul, star_trivial, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec, ← mulVec_transpose, smul_eq_mul]
    have hne : Lᵀ *ᵥ x ≠ 0 := by
      intro h0
      obtain ⟨y, hy⟩ := hsurj x
      apply hx
      have : x ⬝ᵥ x = 0 := by
        calc x ⬝ᵥ x = x ⬝ᵥ (L *ᵥ y) := by rw [hy]
          _ = (Lᵀ *ᵥ x) ⬝ᵥ y := by rw [dotProduct_mulVec, ← mulVec_transpose]
          _ = 0 := by rw [h0, zero_dotProduct]
      exact dotProduct_self_eq_zero.mp this
    have hpos : 0 < (Lᵀ *ᵥ x) ⬝ᵥ (Lᵀ *ᵥ x) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm (mt dotProduct_self_eq_zero.mp hne))
    have : 0 < s ^ 2 := by positivity
    positivity

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory WithLp

namespace HigherOrderId.Certify.Dev.T5.PartA
open HigherOrderId.Certify HigherOrderId.Certify.Dev.T5.PartC

/-! ## T3(e): assembly of the achievability part -/

lemma fromObs_toObs {d E : ℕ} (y : Hs d E) : fromObs (toObs y) = y := by
  ext j
  rcases j with ⟨e, _ | i⟩ <;> simp [fromObs, toObs, obsCoord]

/-- The coordinates `ϑ = (b, (Q_ij)_{i<j})`. -/
def coords {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ThetaIdx d → ℝ :=
  Sum.elim b (fun p => Q p.1.1 p.1.2)

lemma thB_coords {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    thB (coords b Q) = b := by
  funext i; rw [thB_apply]; rfl

lemma thQ_coords {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsSymZeroDiag Q) : thQ (coords b Q) = Q := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · exact thQ_upper (coords b Q) ⟨(i, j), h⟩
  · subst h; rw [thQ_diag, hQ.2]
  · rw [thQ_symm, thQ_upper (coords b Q) ⟨(j, i), h⟩]
    show Q j i = Q i j
    exact (hQ.1.apply j i).symm

lemma energy_coords {d : ℕ} (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsSymZeroDiag Q) : energy b Q = ∑ t, coords b Q t ^ 2 := by
  have := energy_th (coords b Q)
  rwa [thB_coords, thQ_coords b Q hQ] at this

lemma coords_th {d : ℕ} (ϑ : ThetaIdx d → ℝ) : coords (thB ϑ) (thQ ϑ) = ϑ := by
  funext t
  rcases t with i | p
  · exact thB_apply ϑ i
  · exact thQ_upper ϑ p

lemma symZero_zero {d : ℕ} : IsSymZeroDiag (0 : Matrix (Fin d) (Fin d) ℝ) :=
  ⟨by simp [Matrix.IsSymm], fun _ => rfl⟩

lemma frobNorm_pos_of_posDef {D' : ℕ} (S : Matrix (Fin D') (Fin D') ℝ) (hS : S.PosDef)
    (i : Fin D') : 0 < frobNorm S := by
  unfold frobNorm frobInner
  apply Real.sqrt_pos.mpr
  have h1 : 0 < S i i * S i i := mul_pos (hS.diag_pos) (hS.diag_pos)
  calc (0 : ℝ) < S i i * S i i := h1
    _ ≤ ∑ j, S i j * S i j :=
        Finset.single_le_sum (f := fun j => S i j * S i j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
    _ ≤ ∑ i', ∑ j, S i' j * S i' j :=
        Finset.single_le_sum (f := fun i' => ∑ j, S i' j * S i' j)
          (fun i' _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg _)) (Finset.mem_univ i)

/-- Achievability, restated verbatim from the Blueprint. -/
theorem achieve (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (h101 : ∀ (d m N : ℕ) (α σ : ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
          (V : Matrix (Fin d) (Fin (d - m)) ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 →
        0 < σ → (d - m + 1) ∣ N → 0 < N / (d - m + 1) →
        Uᵀ * U = 1 → Vᵀ * V = 1 → Uᵀ * V = 0 →
        (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) →
        frobNorm (GammaTheta U V σ N (vN d m N α σ)) ≤
          C₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6))
    (d m N : ℕ) (α σ R : ℝ) (hd : 10 ≤ d) (hm : m ≤ md d) (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hσ : 0 < σ) (hdvd : (d - m + 1) ∣ N) (hN : 0 < N / (d - m + 1)) (hR : 0 < R)
    (hrate : CUpper δ β * C₀ * rate d m N α σ ≤ R ^ 2) :
    ∃ D : Design d (d - m + 1), InDesignClass d m N α D ∧
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ^ 2 ∧ ε ≤ CUpper δ β * C₀ * rate d m N α σ ∧
        ∃ A : Set (Obs d (d - m + 1)), MeasurableSet A ∧
          Certifies D σ R ε δ β (A.indicator (fun _ => (1 : ℝ))) := by
  obtain ⟨U, V, D, hU, hV, hUV, hfull, hUw, hD, hsum, hcov⟩ :=
    exists_design d m N α hd hm hα0 hdvd hN
  have hmd := (m_bound d m hd hm).2
  have hrep := (lemma_B_5 d m (d - m) hd (by omega) U V hU hV hUV hfull 1 one_pos).2.2.1
  set n := N / (d - m + 1) with hndef
  have hn : ∀ e, D.n e = n := hD.2.2.2.2.2
  set kR : ℝ := ((d - m : ℕ) : ℝ) with hkR
  have hk : 0 < kR := by rw [hkR]; exact_mod_cast (by omega : 0 < d - m)
  set ER : ℝ := ((d - m + 1 : ℕ) : ℝ) with hERdef
  have hER : ER = kR + 1 := by rw [hERdef, hkR]; push_cast; ring
  have hE0 : ER ≠ 0 := by rw [hER]; positivity
  set c : ℝ := ER * α ^ 2 / kR with hc
  set κ : ℝ := kR / (ER * α ^ 2) with hκdef
  have hκ : κ * c = 1 := by rw [hc, hκdef]; field_simp
  set s := sd σ n with hsdef
  have hs : 0 < s := sd_pos σ hσ n hN
  have hs2 : s ^ 2 = σ ^ 2 / n := sd_sq_eq σ n hN
  have hNE : (N : ℝ) = n * ER := by
    rw [hERdef, hndef]; exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hN
  have hkd : kR = (d : ℝ) - m := by rw [hkR]; push_cast [hmd.le]; ring
  -- the covariance of the estimator
  set T := Tm D U V κ with hT
  have hgram : T * Tᵀ = Gm U V ER⁻¹ κ := Tm_gram D U V κ c hsum hcov hV hκ hE0
  set Γ := GammaTheta U V σ N (vN d m N α σ) with hΓdef
  have hΓ : s ^ 2 • (T * Tᵀ) = Γ := by
    rw [hgram]
    ext t t'
    rcases t with a | p <;> rcases t' with a' | q
    · simp only [Matrix.smul_apply, Gm, GammaTheta, smul_eq_mul, hΓdef]
      split_ifs
      · rw [hs2, hNE]; field_simp
      · simp
    · simp [Gm, GammaTheta, hΓdef]
    · simp [Gm, GammaTheta, hΓdef]
    · simp only [Matrix.smul_apply, Gm, GammaTheta, GammaEntry, smul_eq_mul, Matrix.mul_apply,
        Matrix.transpose_apply, hΓdef]
      rw [← mul_assoc]
      congr 1
      rw [hs2, hκdef, vN, hNE, ← hkd]
      field_simp
  -- reindexing to `Fin D'`
  set D' := Fintype.card (ThetaIdx d)
  let e : ThetaIdx d ≃ Fin D' := Fintype.equivFin (ThetaIdx d)
  set T' : Matrix (Fin D') (Jx d (d - m + 1)) ℝ := T.submatrix e.symm id with hT'
  set Γ' := Γ.submatrix e.symm e.symm with hΓ'def
  have hΓ' : s ^ 2 • (T' * T'ᵀ) = Γ' := by
    rw [hΓ'def, ← hΓ]
    ext k l
    simp [hT', Matrix.mul_apply]
  have hmean : ∀ (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ), IsSymZeroDiag Q →
      T' *ᵥ meanFn D b Q = fun k => coords b Q (e.symm k) := by
    intro b Q hQ
    obtain ⟨h1, h2⟩ := Tm_mean D U V κ c hsum hcov hV hκ hE0 hrep b Q hQ
    funext k
    change (T *ᵥ meanFn D b Q) (e.symm k) = _
    rcases e.symm k with a | p
    · exact h1 a
    · exact h2 p
  have hsurj : ∀ x : Fin D' → ℝ, ∃ y, T' *ᵥ y = x := by
    intro x
    refine ⟨meanFn D (thB (fun t => x (e t))) (thQ (fun t => x (e t))), ?_⟩
    rw [hmean _ _ (thQ_symZero _), coords_th]
    funext k; simp
  have hΓPD : Γ'.PosDef := by rw [← hΓ']; exact posDef_LLt T' s hs.ne' hsurj
  -- the law of the estimator
  set Tob : Obs d (d - m + 1) → EuclideanSpace ℝ (Fin D') := fun o => mat T' (fromObs o)
    with hTob
  have hTobm : Measurable Tob := (mat T').continuous.measurable.comp measurable_fromObs
  have hlaw : ∀ (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ), IsSymZeroDiag Q →
      (releaseLaw D σ b Q).map Tob =
        multivariateGaussian (toLp 2 (fun k => coords b Q (e.symm k))) Γ' := by
    intro b Q hQ
    have hg : Measurable (fun g : Hs d (d - m + 1) =>
        toObs (toLp 2 (meanFn D b Q) + sd σ n • g)) := measurable_toObs.comp (by fun_prop)
    rw [releaseLaw_eq_map D σ n hn, Measure.map_map hTobm hg]
    have : Tob ∘ (fun g => toObs (toLp 2 (meanFn D b Q) + sd σ n • g)) =
        fun g => toLp 2 (fun k => coords b Q (e.symm k)) + s • mat T' g := by
      funext g
      simp only [Function.comp, hTob, fromObs_toObs, map_add, map_smul]
      congr 1
      ext k
      rw [ofLp_mat, hmean b Q hQ]
    rw [this, std_map_affine, hΓ']
  -- the tolerance
  have : Nonempty (ThetaIdx d) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hD'pos : 0 < D' := Fintype.card_pos
  have hfrobpos : 0 < frobNorm Γ' := frobNorm_pos_of_posDef Γ' hΓPD ⟨0, hD'pos⟩
  have hfrobeq : frobNorm Γ' = frobNorm Γ := frobNorm_submatrix Γ e.symm
  set ε := CUpper δ β * frobNorm Γ' with hεdef
  have hCU : 0 < CUpper δ β := lt_of_lt_of_le (div_pos (by norm_num) hδ0) (le_max_right _ _)
  have hε0 : 0 < ε := mul_pos hCU hfrobpos
  have h1 := h101 d m N α σ U V hd hm hα0 hα1 hσ hdvd hN hU hV hUV hUw
  have hεC : ε ≤ CUpper δ β * C₀ * rate d m N α σ := by
    rw [hεdef, hfrobeq, rate, mul_assoc (CUpper δ β), ← mul_assoc C₀]
    exact mul_le_mul_of_nonneg_left h1 hCU.le
  have hεR : ε ≤ R ^ 2 := hεC.trans hrate
  obtain ⟨hsafe, hnull⟩ :=
    (lemma_C_1 D' Γ' hΓPD δ β R ε hδ0 hδ1 hβ0 hβ1 hε0 hεR).2 le_rfl
  -- the rule
  set S := {x : EuclideanSpace ℝ (Fin D') | ‖x‖ ^ 2 - Γ'.trace ≤ ε / 2} with hSdef
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hind : (Tob ⁻¹' S).indicator (fun _ => (1 : ℝ)) = energyRule Γ' ε ∘ Tob := by
    funext o
    simp only [Set.indicator, Set.mem_preimage, Function.comp, energyRule, hSdef,
      Set.mem_ofPred_eq]
  have hERm : Measurable (energyRule Γ' ε) := measurable_const.indicator hSm
  have hint : ∀ (b : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ), IsSymZeroDiag Q →
      ∫ y, (Tob ⁻¹' S).indicator (fun _ => (1 : ℝ)) y ∂(releaseLaw D σ b Q) =
        ∫ x, energyRule Γ' ε x ∂(multivariateGaussian
          (toLp 2 (fun k => coords b Q (e.symm k))) Γ') := by
    intro b Q hQ
    rw [hind, ← hlaw b Q hQ, integral_map hTobm.aemeasurable hERm.aestronglyMeasurable]
    rfl
  refine ⟨D, hD, ε, hε0, hεR, hεC, Tob ⁻¹' S, hTobm hSm, ?_, ?_⟩
  · intro b Q hθ hεE
    rw [hint b Q hθ.1]
    have hnorm : ‖(toLp 2 (fun k => coords b Q (e.symm k)) : EuclideanSpace ℝ (Fin D'))‖ ^ 2 =
        energy b Q := by
      rw [EuclideanSpace.real_norm_sq_eq, energy_coords b Q hθ.1]
      exact Equiv.sum_comp e.symm (fun t => coords b Q t ^ 2)
    exact hsafe _ (by rw [hnorm]; exact hεE) (by rw [hnorm]; exact hθ.2)
  · rw [hint 0 0 symZero_zero]
    have h0 : (toLp 2 (fun k => coords (0 : Fin d → ℝ) 0 (e.symm k)) :
        EuclideanSpace ℝ (Fin D')) = 0 := by
      ext k
      simp only [PiLp.zero_apply]
      rcases e.symm k with a | p <;> rfl
    rw [h0]
    exact hnull

end HigherOrderId.Certify.Dev.T5.PartA
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify.Dev.T5.Final
open HigherOrderId.Certify

lemma CUpper_pos (δ β : ℝ) (hδ0 : 0 < δ) : 0 < CUpper δ β :=
  lt_of_lt_of_le (div_pos (by norm_num) hδ0) (le_max_right _ _)

lemma cLower_pos (δ β : ℝ) (hδ1 : δ < 1 / 4) (hβ1 : β < 1 / 4) : 0 < cLower δ β := by
  unfold cLower
  apply Real.sqrt_pos.mpr
  have h : 0 < 1 - δ - β := by linarith
  have : 0 < Real.log (1 + 4 * (1 - δ - β) ^ 2) := Real.log_pos (by nlinarith)
  linarith

end HigherOrderId.Certify.Dev.T5.Final

namespace HigherOrderId.Certify
open HigherOrderId.Certify.Dev.T5.Final in
theorem chk_theorem_5_2 (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4) :
    ∃ cbar c C : ℝ, 0 < cbar ∧ 0 < c ∧ 0 < C ∧
      ∀ (d m N : ℕ) (α σ R : ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 → 0 < σ →
        (d - m + 1) ∣ N → 0 < N / (d - m + 1) → 0 < R →
        rate d m N α σ ≤ cbar * R ^ 2 →
        (∃ D : Design d (d - m + 1), InDesignClass d m N α D ∧
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ^ 2 ∧ ε ≤ C * rate d m N α σ ∧
            ∃ A : Set (Obs d (d - m + 1)), MeasurableSet A ∧
              Certifies D σ R ε δ β (A.indicator (fun _ => (1 : ℝ)))) ∧
        (∀ D : Design d (d - m + 1), InDesignClass d m N α D →
          ∀ ε : ℝ, 0 < ε → ε ≤ R ^ 2 →
            ∀ φ : Obs d (d - m + 1) → ℝ, IsRandomizedRule φ →
              Certifies D σ R ε δ β φ → c * rate d m N α σ ≤ ε) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, h1, h2⟩ := eq_101
  have hCU := CUpper_pos δ β hδ0
  have hcL := cLower_pos δ β hδ1 hβ1
  have hK : 0 < CUpper δ β * C₀ := mul_pos hCU hC₀
  refine ⟨1 / (CUpper δ β * C₀), cLower δ β * c₀, CUpper δ β * C₀, by positivity,
    mul_pos hcL hc₀, hK, ?_⟩
  intro d m N α σ R hd hm hα0 hα1 hσ hdvd hN hR hrate
  refine ⟨?_, ?_⟩
  · have hrate' : CUpper δ β * C₀ * rate d m N α σ ≤ R ^ 2 := by
      have := mul_le_mul_of_nonneg_left hrate hK.le
      rwa [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] at this
    exact Dev.T5.PartA.achieve δ β hδ0 hδ1 hβ0 hβ1 C₀ hC₀ h2 d m N α σ R hd hm hα0 hα1 hσ hdvd
      hN hR hrate'
  · intro D hD ε hε0 hεR φ hφ hcert
    exact Dev.T5.PartC.converse δ β hδ0 hδ1 hβ0 hβ1 c₀ h1 d m N α σ R hd hm hα0 hα1 hσ D hD ε hε0
      hεR φ hφ hcert

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_theorem_5_2 := @HigherOrderId.Certify.chk_theorem_5_2
