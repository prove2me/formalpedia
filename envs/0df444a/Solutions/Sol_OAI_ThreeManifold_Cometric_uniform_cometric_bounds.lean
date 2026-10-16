-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.uniform_cometric_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:33:29.877557+00:00
-- url     : https://prove2.me/submissions/db324935-0597-4ba0-8ade-c61566ccacd3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L1451-L1483
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.uniform_cometric_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Theorems.Thm_OAI_ThreeManifold_Cometric_P_elliptic
import Theorems.Thm_OAI_ThreeManifold_Cometric_P_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_Cometric_Q_elliptic
import Theorems.Thm_OAI_ThreeManifold_Cometric_a_sq_le_neg_deriv
import Theorems.Thm_OAI_ThreeManifold_Cometric_first_derivative_bound
import Theorems.Thm_OAI_ThreeManifold_Cometric_sqnorm_mulVec_le

-- ---- from OAI.Geometry.ConjugatePoints.Cometric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Radial profiles, cometrics, and collar estimates.
-/

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.RadialProfile

end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

lemma a_hasDerivAt (u : ℝ) :
    HasDerivAt a (-a u / (2 / 3 - u) ^ 2) u := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (2 / 3 - u)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  have hcomp := h.comp u ((hasDerivAt_const u (2 / 3)).sub (hasDerivAt_id u))
  convert! hcomp using 1
  simp [a, div_eq_mul_inv, inv_pow, mul_comm]

lemma a_deriv (u : ℝ) : deriv a u = -a u / (2 / 3 - u) ^ 2 :=
  (a_hasDerivAt u).deriv

lemma a_deriv_nonpos (u : ℝ) : deriv a u ≤ 0 := by
  rw [a_deriv]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (a_nonneg u)) (sq_nonneg _)

lemma neg_a_deriv_hasDerivAt {u : ℝ} (hu : u < 2 / 3) :
    HasDerivAt (fun x => -deriv a x)
      (a u * (2 * (2 / 3 - u) - 1) / (2 / 3 - u) ^ 4) u := by
  have hx : 2 / 3 - u ≠ 0 := by linarith
  have hs := ((hasDerivAt_const u ((2 : ℝ) / 3)).sub (hasDerivAt_id u)).pow 2
  have h := (a_hasDerivAt u).div hs (pow_ne_zero 2 hx)
  convert! h using 1
  · funext x
    simp only [a_deriv, Pi.div_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    ring
  · dsimp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero, zero_sub]
    field_simp [hx]
    ring

lemma neg_a_deriv_antitone_mid :
    AntitoneOn (fun u => -deriv a u) (Icc (5 / 12) (7 / 12)) := by
  have hc : ContDiff ℝ ∞ (fun u => -deriv a u) :=
    (contDiff_infty_iff_deriv.mp a_smooth).2.neg
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuous.continuousOn
    (hc.differentiable (by simp)).differentiableOn ?_
  intro u hu
  rw [interior_Icc] at hu
  have hcut : u < 2 / 3 := by linarith [hu.2]
  rw [(neg_a_deriv_hasDerivAt hcut).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (a_nonneg u) (by linarith [hu.1]))
    (by positivity)

lemma a_slope_lower {u : ℝ} (hu : u ∈ Icc (5 / 12) (7 / 12)) :
    144 * Real.exp (-12) ≤ -deriv a u := by
  have h := neg_a_deriv_antitone_mid hu (show (7 / 12 : ℝ) ∈ Icc (5 / 12) (7 / 12)
    by norm_num) hu.2
  have he : -deriv a (7 / 12) = 144 * Real.exp (-12) := by
    rw [a_deriv, a_formula]
    norm_num
    ring
  dsimp only at h
  rwa [he] at h

lemma χ_nonneg (t : ℝ) : 0 ≤ χ t := Real.smoothTransition.nonneg _
lemma χ_le_one (t : ℝ) : χ t ≤ 1 := Real.smoothTransition.le_one _

lemma χ_eventually_zero {t : ℝ} (ht : t < 5 / 12) :
    χ =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [gt_mem_nhds ht] with x hx
  exact χ_eq_zero hx.le

lemma χ_eventually_one {t : ℝ} (ht : 7 / 12 < t) :
    χ =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [lt_mem_nhds ht] with x hx
  exact χ_eq_one hx.le

lemma χ_deriv_left {t : ℝ} (ht : t < 5 / 12) : deriv χ t = 0 := by
  simpa using (χ_eventually_zero ht).deriv_eq

lemma χ_deriv_right {t : ℝ} (ht : 7 / 12 < t) : deriv χ t = 0 := by
  simpa using (χ_eventually_one ht).deriv_eq

lemma χ_deriv2_left {t : ℝ} (ht : t < 5 / 12) : deriv (deriv χ) t = 0 := by
  simpa using (χ_eventually_zero ht).deriv.deriv_eq

lemma χ_deriv2_right {t : ℝ} (ht : 7 / 12 < t) : deriv (deriv χ) t = 0 := by
  simpa using (χ_eventually_one ht).deriv.deriv_eq

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

end ThreeManifold.Collar

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma shear_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    0 ≤ shear δ t ∧ shear δ t ≤ 1 := by
  have hc := χ_nonneg t
  have hc' := χ_le_one t
  dsimp [shear]
  constructor
  · positivity
  · calc
      δ ^ 2 * χ t ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hc' (sq_nonneg δ)
      _ ≤ 1 := by nlinarith [hδ.1, hδ.2]

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

lemma sqnorm_eq_zero_iff (p : V2) : sqnorm p = 0 ↔ p = 0 := by
  rw [sqnorm, add_eq_zero_iff_of_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]
  simp only [sq_eq_zero_iff, funext_iff, Fin.forall_fin_two, Pi.zero_apply]

lemma sqnorm_pos {p : V2} (hp : p ≠ 0) : 0 < sqnorm p :=
  (sqnorm_nonneg p).lt_of_ne' (mt (sqnorm_eq_zero_iff p).mp hp)

lemma shear_norm_upper (x y c : ℝ) (hc : |c| ≤ 1) :
    x ^ 2 + (y + c * x) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) := by
  have hc' : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc
  have hcx := mul_nonneg (sub_nonneg.mpr hc') (sq_nonneg x)
  nlinarith [sq_nonneg (y - c * x), sq_nonneg y]

lemma shear_norm_lower (x y c : ℝ) (hc : |c| ≤ 1) :
    (x ^ 2 + y ^ 2) / 3 ≤ x ^ 2 + (y + c * x) ^ 2 := by
  have h := shear_norm_upper x (y + c * x) (-c) (by simpa using hc)
  have he : y + c * x + -c * x = y := by ring
  rw [he] at h
  linarith

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma P_posDef {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    (P δ t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (P_hermitian δ t)
  intro p hp
  have hl := (P_elliptic hδ ht p).1
  have hp' := sqnorm_pos hp
  change 0 < qform (P δ t) p
  linarith

lemma d₂_hasDerivAt (δ t : ℝ) : HasDerivAt (d₂ δ) (u₂ δ t) t := by
  have h := (A_hasDerivAt (1 - t)).comp t ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! (hasDerivAt_const t (1 : ℝ)).add (h.const_mul δ) using 1
  simp [u₂]

lemma shear_hasDerivAt (δ t : ℝ) : HasDerivAt (shear δ) (v δ t) t :=
  ((χ_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma u₁_hasDerivAt (δ t : ℝ) : HasDerivAt (u₁ δ) (w₁ δ t) t :=
  ((a_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma u₂_hasDerivAt (δ t : ℝ) : HasDerivAt (u₂ δ) (w₂ δ t) t := by
  have h := ((a_smooth.differentiable (by simp) (1 - t)).hasDerivAt).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  convert! h.const_mul (-δ) using 1
  simp [w₂]

lemma v_hasDerivAt (δ t : ℝ) : HasDerivAt (v δ) (z δ t) t :=
  ((χ_deriv_smooth.differentiable (by simp) t).hasDerivAt).const_mul _

lemma P_deriv (δ : ℝ) : deriv (P δ) = P₁ δ := funext fun t => (P_hasDerivAt δ t).deriv

lemma P₁_hasDerivAt (δ t : ℝ) : HasDerivAt (P₁ δ) (P₂ δ t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hu1 := u₁_hasDerivAt δ t
  have hu2 := u₂_hasDerivAt δ t
  have hd2 := d₂_hasDerivAt δ t
  have hs := shear_hasDerivAt δ t
  have hv := v_hasDerivAt δ t
  fin_cases i <;> fin_cases j <;> dsimp [P₁, P₂]
  · convert! (hu1.add (hu2.mul (hs.pow 2))).add
      (((hd2.const_mul 2).mul hs).mul hv) using 1
    dsimp only [Pi.pow_apply, Pi.mul_apply]
    ring
  · convert! (hu2.mul hs).add (hd2.mul hv) using 1
    ring
  · convert! (hu2.mul hs).add (hd2.mul hv) using 1
    ring
  · exact hu2

lemma P₂_deriv (δ : ℝ) : deriv (deriv (P δ)) = P₂ δ := by
  rw [P_deriv]
  exact funext fun t => (P₁_hasDerivAt δ t).deriv

lemma frame_inverse (δ : ℝ) : C₂ δ * T₂ δ = 1 ∧ T₂ δ * C₂ δ = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [T₂, C₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma P₂_split (δ t : ℝ) :
    P₂ δ t = diagonal ![w₁ δ t, w₂ δ t] + δ ^ 2 • N₂ δ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P₂, N₂, shear, w₁, w₂, u₂, v, z] <;> ring

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

lemma N₁_smooth : ContDiff ℝ ∞ (fun y : ℝ × ℝ => N₁ y.1 y.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [N₁, d₂] <;> fun_prop

lemma N₂_smooth : ContDiff ℝ ∞ (fun y : ℝ × ℝ => N₂ y.1 y.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [N₂, d₂] <;> fun_prop

lemma normalized_errors_bounded : ∃ B : ℝ, 1 ≤ B ∧
    ∀ δ ∈ Icc (0 : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j,
      |N₁ δ t i j| ≤ B ∧ |N₂ δ t i j| ≤ B := by
  obtain ⟨b1, hb1⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (1 / 2) ×ˢ Icc (0 : ℝ) 1) N₁_smooth.continuous.continuousOn
  obtain ⟨b2, hb2⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (1 / 2) ×ˢ Icc (0 : ℝ) 1) N₂_smooth.continuous.continuousOn
  refine ⟨max 1 (max b1 b2), le_max_left _ _, ?_⟩
  intro δ hδ t ht i j
  constructor
  · calc
      |N₁ δ t i j| ≤ ‖N₁ δ t i‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (N₁ δ t i) j
      _ ≤ ‖N₁ δ t‖ := norm_le_pi_norm _ i
      _ ≤ b1 := hb1 (δ, t) ⟨hδ, ht⟩
      _ ≤ max 1 (max b1 b2) := le_trans (le_max_left _ _) (le_max_right _ _)
  · calc
      |N₂ δ t i j| ≤ ‖N₂ δ t i‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (N₂ δ t i) j
      _ ≤ ‖N₂ δ t‖ := norm_le_pi_norm _ i
      _ ≤ b2 := hb2 (δ, t) ⟨hδ, ht⟩
      _ ≤ max 1 (max b1 b2) := le_trans (le_max_right _ _) (le_max_right _ _)

lemma qform_add (M N : Mat2) (p : V2) :
    qform (M + N) p = qform M p + qform N p := by
  simp only [qform, Matrix.add_mulVec, dotProduct_add]

lemma qform_smul (r : ℝ) (M : Mat2) (p : V2) :
    qform (r • M) p = r * qform M p := by
  simp only [qform, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma qform_neg (M : Mat2) (p : V2) : qform (-M) p = -qform M p := by
  simp only [qform, Matrix.neg_mulVec, dotProduct_neg]

lemma qform_diag (r s : ℝ) (p : V2) :
    qform (diagonal ![r, s]) p = r * p 0 ^ 2 + s * p 1 ^ 2 := by
  simp [qform, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

lemma dotProduct_sq_le (p q : V2) : (p ⬝ᵥ q) ^ 2 ≤ sqnorm p * sqnorm q := by
  simp only [dotProduct, Fin.sum_univ_two, sqnorm]
  nlinarith [sq_nonneg (p 0 * q 1 - p 1 * q 0)]

lemma abs_qform_le {M : Mat2} {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, |M i j| ≤ B) (p : V2) :
    |qform M p| ≤ 2 * B * sqnorm p := by
  have h := dotProduct_sq_le p (M *ᵥ p)
  have hm := mul_le_mul_of_nonneg_left (sqnorm_mulVec_le hB hM p) (sqnorm_nonneg p)
  change qform M p ^ 2 ≤ _ at h
  have ht : 0 ≤ 2 * B * sqnorm p := mul_nonneg (mul_nonneg (by norm_num) hB) (sqnorm_nonneg p)
  have ha := abs_nonneg (qform M p)
  have hs := sq_abs (qform M p)
  nlinarith

lemma cutoffMargin_pos : 0 < cutoffMargin := by
  unfold cutoffMargin
  positivity

lemma middle_concavity {δ t B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (ht : t ∈ Icc (5 / 12) (7 / 12))
    (hN : ∀ i j, |N₂ δ t i j| ≤ B) (hsmall : 4 * B * δ ≤ cutoffMargin)
    (p : V2) :
    cutoffMargin * δ / 2 * sqnorm p ≤ qform (-P₂ δ t) p := by
  have ha := a_slope_lower ht
  have hb := a_slope_lower (u := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  change cutoffMargin ≤ -deriv a t at ha
  change cutoffMargin ≤ -deriv a (1 - t) at hb
  have ha' := mul_le_mul_of_nonneg_right ha (mul_nonneg hδ (sq_nonneg (p 0)))
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg hδ (sq_nonneg (p 1)))
  have hn := (abs_le.mp (abs_qform_le hB hN p)).2
  have hn' := mul_le_mul_of_nonneg_left hn (sq_nonneg δ)
  have hs := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hδ (sqnorm_nonneg p))
  rw [qform_neg, P₂_split, qform_add, qform_diag, qform_smul]
  dsimp only [w₁, w₂, sqnorm] at ha' hb' hn' hs ⊢
  nlinarith

lemma middle_domination {δ t B : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hB : 0 ≤ B)
    (ht : t ∈ Icc (5 / 12) (7 / 12))
    (hN : ∀ i j, |N₁ δ t i j| ≤ B ∧ |N₂ δ t i j| ≤ B)
    (hsmall : 4 * B * δ ≤ cutoffMargin) (p : V2) :
    0 ≤ qform (-P₂ δ t) p ∧
    sqnorm (P₁ δ t *ᵥ p) ≤
      (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ * qform (-P₂ δ t) p := by
  have hc := middle_concavity hδ.1 hB ht (fun i j => (hN i j).2) hsmall p
  have hp := first_derivative_bound hδ hB (fun i j => (hN i j).1) p
  have hm := cutoffMargin_pos
  constructor
  · exact le_trans (mul_nonneg (div_nonneg (mul_nonneg hm.le hδ.1) (by norm_num))
      (sqnorm_nonneg p)) hc
  · have hmul := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ by positivity [hδ.1])
    calc
      sqnorm (P₁ δ t *ᵥ p) ≤ (2 + 8 * B ^ 2) * δ ^ 2 * sqnorm p := hp
      _ = (2 * (2 + 8 * B ^ 2) / cutoffMargin) * δ *
          (cutoffMargin * δ / 2 * sqnorm p) := by field_simp
      _ ≤ _ := hmul

lemma outside_cutoff_derivatives {t : ℝ} (ht : t ∉ Icc (5 / 12) (7 / 12)) :
    deriv χ t = 0 ∧ deriv (deriv χ) t = 0 := by
  have h : t < 5 / 12 ∨ 7 / 12 < t := by
    simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases h with hl | hr
  · exact ⟨χ_deriv_left hl, χ_deriv2_left hl⟩
  · exact ⟨χ_deriv_right hr, χ_deriv2_right hr⟩

lemma stationary_first_formula {δ t : ℝ} (hχ : deriv χ t = 0) (p : V2) :
    sqnorm (P₁ δ t *ᵥ p) =
      (δ * a t * p 0 + shear δ t * (-δ * a (1 - t) * (p 1 + shear δ t * p 0))) ^ 2 +
      (-δ * a (1 - t) * (p 1 + shear δ t * p 0)) ^ 2 := by
  simp [sqnorm, Matrix.mulVec, dotProduct, Fin.sum_univ_two, P₁, u₁, u₂, v, hχ]
  ring

lemma stationary_second_formula {δ t : ℝ}
    (hχ : deriv χ t = 0) (hχ' : deriv (deriv χ) t = 0) (p : V2) :
    qform (-P₂ δ t) p = δ *
      (-deriv a t * p 0 ^ 2 - deriv a (1 - t) * (p 1 + shear δ t * p 0) ^ 2) := by
  simp [qform, Matrix.mulVec, dotProduct, Fin.sum_univ_two, P₂, w₁, w₂, v, z, hχ, hχ']
  ring

lemma outside_domination {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1)
    (hout : t ∉ Icc (5 / 12) (7 / 12)) (p : V2) :
    0 ≤ qform (-P₂ δ t) p ∧
    sqnorm (P₁ δ t *ᵥ p) ≤ 3 * δ * qform (-P₂ δ t) p := by
  obtain ⟨hc, hc'⟩ := outside_cutoff_derivatives hout
  have hshear := shear_bounds (t := t) hδ
  have hsabs : |shear δ t| ≤ 1 := by rw [abs_of_nonneg hshear.1]; exact hshear.2
  have hn := shear_norm_upper (-δ * a (1 - t) * (p 1 + shear δ t * p 0))
    (δ * a t * p 0) (shear δ t) hsabs
  have ha := a_sq_le_neg_deriv ht
  have hb := a_sq_le_neg_deriv (u := 1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hm1 := mul_le_mul_of_nonneg_right ha (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 0)))
  have hm2 := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (sq_nonneg δ) (sq_nonneg (p 1 + shear δ t * p 0)))
  rw [stationary_second_formula hc hc', stationary_first_formula hc]
  constructor
  · apply mul_nonneg hδ.1
    have h1 : 0 ≤ -deriv a t * p 0 ^ 2 :=
      mul_nonneg (neg_nonneg.mpr (a_deriv_nonpos t)) (sq_nonneg (p 0))
    have h2 : 0 ≤ -deriv a (1 - t) * (p 1 + shear δ t * p 0) ^ 2 :=
      mul_nonneg (neg_nonneg.mpr (a_deriv_nonpos (1 - t)))
        (sq_nonneg (p 1 + shear δ t * p 0))
    linarith
  · nlinarith

theorem uniform_original_bounds : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : V2,
      (sqnorm p / 3 ≤ qform (P δ t) p ∧ qform (P δ t) p ≤ 6 * sqnorm p) ∧
      (sqnorm p / 6 ≤ qform (Q δ t) p ∧ qform (Q δ t) p ≤ 3 * sqnorm p) ∧
      sqnorm (deriv (P δ) t *ᵥ p) ≤ C ^ 2 * δ ^ 2 * sqnorm p ∧
      0 ≤ qform (-deriv (deriv (P δ)) t) p ∧
      sqnorm (deriv (P δ) t *ᵥ p) ≤ C * δ * qform (-deriv (deriv (P δ)) t) p := by
  obtain ⟨B, hB, hN⟩ := normalized_errors_bounded
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hm := cutoffMargin_pos
  let δ₀ := min (1 / 2 : ℝ) (cutoffMargin / (4 * B))
  let K := 2 + 8 * B ^ 2
  let C := max 3 (max K (2 * K / cutoffMargin))
  have hδ₀ : 0 < δ₀ := lt_min (by norm_num) (div_pos hm (by positivity))
  have hC3 : 3 ≤ C := le_max_left _ _
  have hCK : K ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCM : 2 * K / cutoffMargin ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hKC : K ≤ C ^ 2 := by nlinarith
  refine ⟨δ₀, C, hδ₀, min_le_left _ _, by linarith, ?_⟩
  intro δ hδ t ht p
  have hδ' : δ ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨hδ.1.le, le_trans hδ.2 (min_le_left _ _)⟩
  have hsmall : 4 * B * δ ≤ cutoffMargin := by
    have h := le_trans hδ.2 (min_le_right _ _)
    have hd : 0 < 4 * B := by positivity
    simpa only [mul_comm] using (le_div_iff₀ hd).mp h
  refine ⟨P_elliptic hδ' ht p, Q_elliptic hδ' ht p, ?_⟩
  rw [P₂_deriv, P_deriv]
  constructor
  · calc
      sqnorm (P₁ δ t *ᵥ p) ≤ K * δ ^ 2 * sqnorm p :=
        first_derivative_bound hδ' hB0.le (fun i j => (hN δ hδ' t ht i j).1) p
      _ ≤ C ^ 2 * δ ^ 2 * sqnorm p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC (sq_nonneg δ))
          (sqnorm_nonneg p)
  · by_cases hmid : t ∈ Icc (5 / 12) (7 / 12)
    · obtain ⟨hc, hd⟩ := middle_domination hδ' hB0.le hmid (hN δ hδ' t ht) hsmall p
      refine ⟨hc, hd.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hδ.1.le) hc
    · obtain ⟨hc, hd⟩ := outside_domination hδ' ht hmid p
      refine ⟨hc, hd.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hδ.1.le) hc

lemma qform_congruence (C M : Mat2) (p : V2) :
    qform (C * M * Cᵀ) p = qform M (Cᵀ *ᵥ p) := by
  simp [qform, dotProduct, Matrix.mulVec, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma C₂_transpose (δ : ℝ) : (C₂ δ)ᵀ = C₂ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma T₂_transpose (δ : ℝ) : (T₂ δ)ᵀ = T₂ δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma C₂_norm_bounds {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (p : V2) :
    sqnorm p / 3 ≤ sqnorm (C₂ δ *ᵥ p) ∧ sqnorm (C₂ δ *ᵥ p) ≤ 3 * sqnorm p := by
  have h : |-(δ ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg δ)]
    nlinarith [hδ.1, hδ.2]
  have hl := shear_norm_lower (p 1) (p 0) (-(δ ^ 2)) h
  have hu := shear_norm_upper (p 1) (p 0) (-(δ ^ 2)) h
  simp [sqnorm, C₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> nlinarith

lemma T₂_norm_bounds {δ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (p : V2) :
    sqnorm p / 3 ≤ sqnorm (T₂ δ *ᵥ p) ∧ sqnorm (T₂ δ *ᵥ p) ≤ 3 * sqnorm p := by
  have h : |δ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg δ)]
    nlinarith [hδ.1, hδ.2]
  have hl := shear_norm_lower (p 0) (p 1) (δ ^ 2) h
  have hu := shear_norm_upper (p 0) (p 1) (δ ^ 2) h
  simp [sqnorm, T₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> nlinarith

lemma PEnd_hasDerivAt (δ τ : ℝ) :
    HasDerivAt (PEnd δ) (-(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ)) τ := by
  have hd := (P_hasDerivAt δ (1 - τ)).scomp τ
    ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ))
  have hc := (congruenceCLM (C₂ δ)).hasFDerivAt.comp_hasDerivAt τ hd
  change HasDerivAt (fun x => C₂ δ * P δ (1 - x) * (C₂ δ)ᵀ)
    (C₂ δ * ((0 - 1 : ℝ) • P₁ δ (1 - τ)) * (C₂ δ)ᵀ) τ at hc
  convert! hc using 1
  simp

lemma PEnd_deriv (δ : ℝ) : deriv (PEnd δ) =
    fun τ => -(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ) :=
  funext fun τ => (PEnd_hasDerivAt δ τ).deriv

lemma PEnd_deriv₂ (δ : ℝ) : deriv (deriv (PEnd δ)) =
    fun τ => C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ := by
  rw [PEnd_deriv]
  funext τ
  have hd := (P₁_hasDerivAt δ (1 - τ)).scomp τ
    ((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ))
  have hc := ((congruenceCLM (C₂ δ)).hasFDerivAt.comp_hasDerivAt τ hd).neg
  change HasDerivAt (fun x => -(C₂ δ * P₁ δ (1 - x) * (C₂ δ)ᵀ))
    (-(C₂ δ * ((0 - 1 : ℝ) • P₂ δ (1 - τ)) * (C₂ δ)ᵀ)) τ at hc
  have he : HasDerivAt (fun τ => -(C₂ δ * P₁ δ (1 - τ) * (C₂ δ)ᵀ))
      (C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ) τ := by
    simpa only [zero_sub,
      neg_smul, one_smul, Matrix.mul_neg, Matrix.neg_mul, neg_neg] using hc
  exact he.deriv

lemma QEnd_formula {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) :
    (PEnd δ τ)⁻¹ = T₂ δ * Q δ (1 - τ) * (T₂ δ)ᵀ := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  apply Matrix.inv_eq_left_inv
  dsimp only [PEnd, Q]
  rw [T₂_transpose, C₂_transpose]
  calc
    (T₂ δ * (P δ (1 - τ))⁻¹ * T₂ δ) * (C₂ δ * P δ (1 - τ) * C₂ δ) =
        T₂ δ * ((P δ (1 - τ))⁻¹ * P δ (1 - τ)) * C₂ δ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (T₂ δ) (C₂ δ), (frame_inverse δ).2,
        Matrix.one_mul]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (P_posDef hδ ht).det_pos.ne'), Matrix.mul_one, (frame_inverse δ).2]

lemma PEnd_elliptic {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) (p : V2) :
    sqnorm p / 9 ≤ qform (PEnd δ τ) p ∧ qform (PEnd δ τ) p ≤ 18 * sqnorm p := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hp := P_elliptic hδ ht (C₂ δ *ᵥ p)
  have hc := C₂_norm_bounds hδ p
  rw [PEnd, qform_congruence, C₂_transpose]
  constructor <;> linarith [hp.1, hp.2, hc.1, hc.2]

lemma QEnd_elliptic {δ τ : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (hτ : τ ∈ Icc 0 1) (p : V2) :
    sqnorm p / 18 ≤ qform (PEnd δ τ)⁻¹ p ∧ qform (PEnd δ τ)⁻¹ p ≤ 9 * sqnorm p := by
  have ht : 1 - τ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hq := Q_elliptic hδ ht (T₂ δ *ᵥ p)
  have hc := T₂_norm_bounds hδ p
  rw [QEnd_formula hδ hτ, qform_congruence, T₂_transpose]
  constructor <;> linarith [hq.1, hq.2, hc.1, hc.2]

lemma sqnorm_neg (p : V2) : sqnorm (-p) = sqnorm p := by simp [sqnorm]

lemma PEnd_derivative_norm {δ τ : ℝ} (p : V2) :
    sqnorm (deriv (PEnd δ) τ *ᵥ p) =
      sqnorm (C₂ δ *ᵥ (P₁ δ (1 - τ) *ᵥ (C₂ δ *ᵥ p))) := by
  rw [PEnd_deriv, Matrix.neg_mulVec, sqnorm_neg, C₂_transpose]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma PEnd_derivative_qform (δ τ : ℝ) (p : V2) :
    qform (-deriv (deriv (PEnd δ)) τ) p = qform (-P₂ δ (1 - τ)) (C₂ δ *ᵥ p) := by
  rw [PEnd_deriv₂]
  change qform (-(C₂ δ * P₂ δ (1 - τ) * (C₂ δ)ᵀ)) p = _
  rw [qform_neg, qform_congruence, C₂_transpose, qform_neg]

lemma PEnd_derivative_bounds {δ τ C : ℝ} (hδ : δ ∈ Icc 0 (1 / 2))
    (hd : ∀ q, sqnorm (P₁ δ (1 - τ) *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q)
    (hc : ∀ q, 0 ≤ qform (-P₂ δ (1 - τ)) q)
    (hdom : ∀ q, sqnorm (P₁ δ (1 - τ) *ᵥ q) ≤ C * δ * qform (-P₂ δ (1 - τ)) q)
    (p : V2) :
    sqnorm (deriv (PEnd δ) τ *ᵥ p) ≤ (3 * C) ^ 2 * δ ^ 2 * sqnorm p ∧
    0 ≤ qform (-deriv (deriv (PEnd δ)) τ) p ∧
    sqnorm (deriv (PEnd δ) τ *ᵥ p) ≤
      (3 * C) * δ * qform (-deriv (deriv (PEnd δ)) τ) p := by
  rw [PEnd_derivative_norm, PEnd_derivative_qform]
  have h₁ := (C₂_norm_bounds hδ (P₁ δ (1 - τ) *ᵥ (C₂ δ *ᵥ p))).2
  have h₂ := (C₂_norm_bounds hδ p).2
  have h₃ := mul_le_mul_of_nonneg_left h₂ (mul_nonneg (sq_nonneg C) (sq_nonneg δ))
  refine ⟨?_, hc _, ?_⟩
  · nlinarith [hd (C₂ δ *ᵥ p)]
  · nlinarith [hdom (C₂ δ *ᵥ p)]

theorem uniform_cometric_bounds : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 0 < C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀, ∀ right : Bool, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p : V2,
      let R := coordinateCometric right δ
      (sqnorm p / 9 ≤ qform (R t) p ∧ qform (R t) p ≤ 18 * sqnorm p) ∧
      (sqnorm p / 18 ≤ qform (R t)⁻¹ p ∧ qform (R t)⁻¹ p ≤ 9 * sqnorm p) ∧
      sqnorm (deriv R t *ᵥ p) ≤ C ^ 2 * δ ^ 2 * sqnorm p ∧
      0 ≤ qform (-deriv (deriv R) t) p ∧
      sqnorm (deriv R t *ᵥ p) ≤ C * δ * qform (-deriv (deriv R) t) p := by
  obtain ⟨δ₀, C, hδ₀, hδ₀', hC, h⟩ := uniform_original_bounds
  refine ⟨δ₀, 3 * C, hδ₀, hδ₀', by positivity, ?_⟩
  intro δ hδ right t ht p
  have hδ' : δ ∈ Icc (0 : ℝ) (1 / 2) := ⟨hδ.1.le, le_trans hδ.2 hδ₀'⟩
  cases right with
  | false =>
    simp only [coordinateCometric, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hp, hq, hd, hc, hdom⟩ := h δ hδ t ht p
    have hn := sqnorm_nonneg p
    refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩,
      ⟨by change sqnorm p / 18 ≤ qform (Q δ t) p; linarith [hq.1],
        by change qform (Q δ t) p ≤ 9 * sqnorm p; linarith [hq.2]⟩, ?_, hc, ?_⟩
    · have he := mul_nonneg (sq_nonneg C) (mul_nonneg (sq_nonneg δ) hn)
      nlinarith
    · have he := mul_nonneg (mul_nonneg hC.le hδ.1.le) hc
      nlinarith
  | true =>
    simp only [coordinateCometric, ↓reduceIte]
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h' := fun q => (h δ hδ (1 - t) ht' q).2.2
    rw [P₂_deriv, P_deriv] at h'
    exact ⟨PEnd_elliptic hδ' ht p, QEnd_elliptic hδ' ht p,
      PEnd_derivative_bounds hδ' (fun q => (h' q).1) (fun q => (h' q).2.1)
        (fun q => (h' q).2.2) p⟩

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.uniform_cometric_bounds := @_root_.OAI.ThreeManifold.Cometric.uniform_cometric_bounds
