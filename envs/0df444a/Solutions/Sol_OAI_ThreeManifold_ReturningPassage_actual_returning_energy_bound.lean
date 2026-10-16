-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:49:40.531983+00:00
-- url     : https://prove2.me/submissions/d0035ce5-6658-400d-8db0-8ea06cd84941

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L1421-L1556
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Theorems.Thm_OAI_ThreeManifold_Cometric_coordinateCometric_end_deriv
import Theorems.Thm_OAI_ThreeManifold_Neck_pairing_hasDerivAt
import Theorems.Thm_OAI_ThreeManifold_ReturningCoefficients_actual_mixed_bound
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_dynamics

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

lemma a_pos {u : ℝ} (hu : u < 2 / 3) : 0 < a u :=
  expNegInvGlue.pos_of_pos (by linarith)

lemma a_zero : a 0 = Real.exp (-(3 : ℝ) / 2) := by norm_num [a_formula]

lemma a_eighth_ratio : a (1 / 8) / a 0 = Real.exp (-(9 : ℝ) / 26) := by
  rw [a_zero, a_formula]
  norm_num
  rw [← Real.exp_sub]
  congr 1
  norm_num

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

lemma pairing_sub_left (A : TMat) (u v w : TVec) :
    pairing A (u - v) w = pairing A u w - pairing A v w := by
  simp only [pairing, sub_dotProduct]
lemma pairing_sub_right (A : TMat) (u v w : TVec) :
    pairing A u (v - w) = pairing A u v - pairing A u w := by
  simp only [pairing, Matrix.mulVec_sub, dotProduct_sub]
lemma pairing_smul_left (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A (r • u) v = r * pairing A u v := by
  simp only [pairing, smul_dotProduct, smul_eq_mul]
lemma pairing_smul_right (A : TMat) (r : ℝ) (u v : TVec) :
    pairing A u (r • v) = r * pairing A u v := by
  simp only [pairing, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma pairing_symm {A : TMat} (hA : Aᵀ = A) (u v : TVec) :
    pairing A u v = pairing A v u := by
  unfold pairing
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hA, dotProduct_comm]

lemma continuous_pairing : Continuous (fun p : TMat × TVec × TVec =>
    pairing p.1 p.2.1 p.2.2) := by
  unfold pairing Matrix.mulVec dotProduct
  fun_prop

lemma continuousOn_pairing {X : Type*} [TopologicalSpace X]
    {A : X → TMat} {u v : X → TVec} {S : Set X}
    (hA : ContinuousOn A S) (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun s => pairing (A s) (u s) (v s)) S :=
  continuous_pairing.comp_continuousOn (hA.prodMk (hu.prodMk hv))

lemma pairing_matrix_neg (A : TMat) (u v : TVec) :
    pairing (-A) u v = -pairing A u v := by
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

lemma pairing_mulVec_left (A L : TMat) (u v : TVec) :
    pairing A (L *ᵥ u) v = pairing (Lᵀ * A) u v := by
  unfold pairing
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma P_smooth (δ : ℝ) : ContDiff ℝ ∞ (P δ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [P] <;> fun_prop

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

lemma sqnorm_eq_zero_iff (p : V2) : sqnorm p = 0 ↔ p = 0 := by
  rw [sqnorm, add_eq_zero_iff_of_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]
  simp only [sq_eq_zero_iff, funext_iff, Fin.forall_fin_two, Pi.zero_apply]

lemma sqnorm_pos {p : V2} (hp : p ≠ 0) : 0 < sqnorm p :=
  (sqnorm_nonneg p).lt_of_ne' (mt (sqnorm_eq_zero_iff p).mp hp)

lemma P_hermitian (δ t : ℝ) : (P δ t).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

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

-- ---- from OAI.Geometry.ConjugatePoints.Returning ----
namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.Turning

lemma aZero_pos : 0 < aZero := Real.exp_pos _

lemma small_half {Ce Cm δ : ℝ} ( _he : 0 < Ce) (hm : 0 < Cm)
    (hδ : SmallParameter Ce Cm δ) : Cm * δ ≤ 1 / 2 := by
  have h : δ * (2 * Cm) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * Cm)).mp hδ.2.2.1
  nlinarith

lemma small_gain {Ce Cm δ : ℝ} ( _he : 0 < Ce) (hm : 0 < Cm)
    (hδ : SmallParameter Ce Cm δ) : beta + Ce * aZero * δ ≤ (1 - Cm * δ) ^ 2 := by
  have hd : 0 < 2 * Cm + Ce * aZero := by have := aZero_pos; positivity
  have h := (le_div_iff₀ hd).mp hδ.2.2.2
  nlinarith [sq_nonneg (Cm * δ)]

lemma mixed_square_lower {L p1 c spe : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ 1 - c)
    (h : |spe - L * p1| ≤ c * L * |p1|) :
    (L * p1) ^ 2 * (1 - c) ^ 2 ≤ spe ^ 2 := by
  have habs : |L * p1| ≤ |spe| + |spe - L * p1| := by
    calc
      |L * p1| = |spe - (spe - L * p1)| := by congr 1; ring
      _ ≤ |spe| + |spe - L * p1| := abs_sub _ _
  rw [abs_mul, abs_of_nonneg hL] at habs
  have hlo : L * |p1| * (1 - c) ≤ |spe| := by nlinarith
  have hn : 0 ≤ L * |p1| * (1 - c) := by positivity
  have hs := sq_le_sq₀ hn (abs_nonneg spe) |>.mpr hlo
  simpa only [mul_pow, sq_abs] using hs

lemma endpoint_gain
    {Ce Cm δ L v0 p1 κ μ see spe : ℝ}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * p1 ^ 2)
    (htime : 4 * v0 ≤ beta * κ * p1 ^ 2 * L)
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * p1| ≤ Cm * δ * L * |p1|) :
    L * v0 ^ 2 ≤ spe ^ 2 / (see + μ⁻¹) := by
  have hhalf := small_half he hm hδ
  have hsquare := mixed_square_lower hL.le (by linarith : 0 ≤ 1 - Cm * δ) hmixed
  have ht := mul_le_mul_of_nonneg_right htime hv.le
  have ht' : v0 ^ 2 ≤ beta * L * p1 ^ 2 * μ := by
    rw [hμdef]
    nlinarith
  have hspeed : v0 ^ 2 * μ⁻¹ ≤ beta * L * p1 ^ 2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hμ).mpr ht'
  have hinc' : v0 ^ 2 ≤ δ * aZero * p1 ^ 2 := by simpa [hκ] using hinc
  have hden : 0 < see + μ⁻¹ := add_pos_of_nonneg_of_pos hsee (inv_pos.mpr hμ)
  apply (le_div_iff₀ hden).mpr
  calc
    L * v0 ^ 2 * (see + μ⁻¹) ≤ L * v0 ^ 2 * (Ce * L + μ⁻¹) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hsee_upper le_rfl) (by positivity)
    _ = Ce * L ^ 2 * v0 ^ 2 + L * (v0 ^ 2 * μ⁻¹) := by ring
    _ ≤ Ce * L ^ 2 * (δ * aZero * p1 ^ 2) + L * (beta * L * p1 ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hinc' (by positivity))
        (mul_le_mul_of_nonneg_left hspeed hL.le)
    _ = (L * p1) ^ 2 * (beta + Ce * aZero * δ) := by ring
    _ ≤ (L * p1) ^ 2 * (1 - Cm * δ) ^ 2 :=
      mul_le_mul_of_nonneg_left (small_gain he hm hδ) (sq_nonneg _)
    _ ≤ spe ^ 2 := hsquare

theorem returning_quadratic_bound
    {Ce Cm δ L v0 p1 κ μ spp see spe : ℝ}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * p1 ^ 2)
    (htime : 4 * v0 ≤ beta * κ * p1 ^ 2 * L)
    (hspp : spp ≤ L * (1 + v0 ^ 2))
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * p1| ≤ Cm * δ * L * |p1|) :
    ∃ α : ℝ, spp - 2 * α * spe + α ^ 2 * (see + μ⁻¹) ≤ L := by
  have hgain := endpoint_gain he hm hδ hL hv hμ hκ hμdef hinc htime
    hsee hsee_upper hmixed
  have hden : 0 < see + μ⁻¹ := add_pos_of_nonneg_of_pos hsee (inv_pos.mpr hμ)
  refine ⟨spe / (see + μ⁻¹), ?_⟩
  have heq : spp - 2 * (spe / (see + μ⁻¹)) * spe +
      (spe / (see + μ⁻¹)) ^ 2 * (see + μ⁻¹) = spp - spe ^ 2 / (see + μ⁻¹) := by
    field_simp
    ring
  rw [heq]
  nlinarith

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

lemma two_energy_nonneg {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : B ^ 2 ≤ A * C) (x y : ℝ) :
    0 ≤ A * x ^ 2 + 2 * B * x * y + C * y ^ 2 := by
  by_cases ha : A = 0
  · have hb : B = 0 := by nlinarith [sq_nonneg B]
    simp only [ha, hb, zero_mul, mul_zero, zero_add]
    exact mul_nonneg hC (sq_nonneg y)
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have hh := mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg y)
    nlinarith [sq_nonneg (A * x + B * y)]

lemma dual_pairing {P Q : TMat} (hQP : Q * P = 1) (hP : Pᵀ = P)
    (q ξ : TVec) : pairing Q (P *ᵥ q) ξ = q ⬝ᵥ ξ := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  rw [pairing_mulVec_left, hP, hPQ]
  simp [pairing]

lemma direct_pointwise_quadratic {P Q : TMat} (hQP : Q * P = 1)
    (hP : Pᵀ = P) (hQ : Qᵀ = Q) (hpos : ∀ ξ, 0 ≤ pairing Q ξ ξ)
    {K h g : ℝ} (hK : 0 ≤ K) (hh : 0 ≤ h) (hg : g ^ 2 ≤ h * K)
    (q ξ : TVec) (v w w' α r : ℝ) :
    0 ≤ (pairing Q ξ ξ + w' ^ 2 + h * w ^ 2) -
      2 * r * (q ⬝ᵥ ξ + 2 * v * w' - α * g * w) +
      r ^ 2 * (pairing P q q + 4 * v ^ 2 + α ^ 2 * K) := by
  have hp := hpos (ξ - r • (P *ᵥ q))
  have hs := two_energy_nonneg hh hK hg w (r * α)
  have hcross : pairing Q ξ (P *ᵥ q) = q ⬝ᵥ ξ := by
    rw [pairing_symm hQ, dual_pairing hQP hP]
  have hnorm : pairing Q (ξ - r • (P *ᵥ q)) (ξ - r • (P *ᵥ q)) =
      pairing Q ξ ξ - 2 * r * (q ⬝ᵥ ξ) + r ^ 2 * pairing P q q := by
    simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left,
      pairing_smul_right, dual_pairing hQP hP, hcross]
    unfold pairing
    ring
  rw [hnorm] at hp
  nlinarith [sq_nonneg (w' - 2 * r * v)]

lemma interval_cauchy_of_quadratic {a b : ℝ} (hab : a ≤ b)
    {E F A : ℝ → ℝ} (hE : ContinuousOn E (Icc a b))
    (hF : ContinuousOn F (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (hq : ∀ s ∈ Icc a b, ∀ r : ℝ, 0 ≤ E s - 2 * r * F s + r ^ 2 * A s) :
    (∫ s in a..b, F s) ^ 2 ≤ (∫ s in a..b, A s) * (∫ s in a..b, E s) := by
  have hEi : IntervalIntegrable E volume a b := (by simpa [uIcc_of_le hab] using hE :
    ContinuousOn E (uIcc a b)).intervalIntegrable
  have hFi : IntervalIntegrable F volume a b := (by simpa [uIcc_of_le hab] using hF :
    ContinuousOn F (uIcc a b)).intervalIntegrable
  have hAi : IntervalIntegrable A volume a b := (by simpa [uIcc_of_le hab] using hA :
    ContinuousOn A (uIcc a b)).intervalIntegrable
  have hi : ∀ r : ℝ, 0 ≤ (∫ s in a..b, E s) - 2 * r * (∫ s in a..b, F s) +
      r ^ 2 * (∫ s in a..b, A s) := by
    intro r
    have h := intervalIntegral.integral_nonneg (μ := volume) hab (fun s hs => hq s hs r)
    rw [intervalIntegral.integral_add (hEi.sub (hFi.const_mul (2 * r))) (hAi.const_mul (r ^ 2)),
      intervalIntegral.integral_sub hEi (hFi.const_mul (2 * r)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  have hd := discrim_le_zero (a := ∫ s in a..b, A s)
    (b := -2 * ∫ s in a..b, F s) (c := ∫ s in a..b, E s) (fun r => by
      nlinarith [hi r])
  simp only [discrim] at hd
  nlinarith

lemma add_boundary_cauchy {S E μ f y α : ℝ} (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hμ : 0 < μ) (hcs : f ^ 2 ≤ S * E) :
    (f + α * y) ^ 2 ≤ (S + α ^ 2 * μ⁻¹) * (E + μ * y ^ 2) := by
  have hh : (-f) ^ 2 ≤ (μ * S) * (E / μ) := by
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hcs hμ.le]
  have h := two_energy_nonneg (mul_nonneg hμ.le hS) (div_nonneg hE hμ.le) hh y α
  have heq : (S + α ^ 2 * μ⁻¹) * (E + μ * y ^ 2) - (f + α * y) ^ 2 =
      (S * E - f ^ 2) + (μ * S * y ^ 2 + 2 * (-f) * y * α + E / μ * α ^ 2) := by
    field_simp
    ring
  rw [← sub_nonneg, heq]
  linarith

lemma dotProduct_hasDerivAt {z z' : ℝ → TVec} {s : ℝ} (hz : HasDerivAt z (z' s) s)
    (q : TVec) : HasDerivAt (fun r => q ⬝ᵥ z r) (q ⬝ᵥ z' s) s := by
  let f : TVec →L[ℝ] ℝ := q 0 • ContinuousLinearMap.proj 0 +
    q 1 • ContinuousLinearMap.proj 1
  have h := f.hasFDerivAt.comp_hasDerivAt s hz
  simpa only [f, Function.comp_def, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, dotProduct, Fin.sum_univ_two] using h

lemma direct_endpoint_functional {a b : ℝ} {p e : TVec} {α : ℝ}
    {z z' k : ℝ → TVec} {v v' w w' : ℝ → ℝ}
    (hz : ∀ s ∈ uIcc a b, HasDerivAt z (z' s) s)
    (hv : ∀ s ∈ uIcc a b, HasDerivAt v (v' s) s)
    (hw : ∀ s ∈ uIcc a b, HasDerivAt w (w' s) s)
    (hode : ∀ s ∈ uIcc a b, p ⬝ᵥ k s = -2 * v' s)
    (hwa : w a = 0) (hwb : w b = 0)
    (hF : IntervalIntegrable (fun s => (p - α • e) ⬝ᵥ (z' s - w s • k s) +
      2 * v s * w' s - α * (e ⬝ᵥ k s) * w s) volume a b) :
    (∫ s in a..b, (p - α • e) ⬝ᵥ (z' s - w s • k s) +
      2 * v s * w' s - α * (e ⬝ᵥ k s) * w s) = (p - α • e) ⬝ᵥ (z b - z a) := by
  have hd : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r => (p - α • e) ⬝ᵥ z r + 2 * v r * w r)
        ((p - α • e) ⬝ᵥ (z' s - w s • k s) + 2 * v s * w' s -
          α * (e ⬝ᵥ k s) * w s) s := by
    intro s hs
    apply ((dotProduct_hasDerivAt (hz s hs) (p - α • e)).add
      (((hv s hs).const_mul 2).mul (hw s hs))).congr_deriv
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [hode s hs]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hF
  simpa only [hwa, hwb, mul_zero, add_zero, dotProduct_sub] using hi

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

lemma continuousOn_dot_left {f : ℝ → TVec} {S : Set ℝ}
    (hf : ContinuousOn f S) (q : TVec) : ContinuousOn (fun s => q ⬝ᵥ f s) S := by
  simp only [dotProduct, Fin.sum_univ_two]
  exact ((continuous_apply 0).comp_continuousOn hf).const_mul (q 0) |>.add
    (((continuous_apply 1).comp_continuousOn hf).const_mul (q 1))

lemma direct_endpoint_cauchy {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {P Q : ℝ → TMat} {k z z' : ℝ → TVec} {h v v' w w' : ℝ → ℝ} (p e : TVec)
    (hPc : ContinuousOn P (Icc 0 L)) (hQc : ContinuousOn Q (Icc 0 L))
    (hkc : ContinuousOn k (Icc 0 L)) (hhc : ContinuousOn h (Icc 0 L))
    (hvc : ContinuousOn v (Icc 0 L)) (hzc : ContinuousOn z' (Icc 0 L))
    (hwc : ContinuousOn w (Icc 0 L)) (hw'c : ContinuousOn w' (Icc 0 L))
    (hQP : ∀ s ∈ Icc 0 L, Q s * P s = 1)
    (hPs : ∀ s ∈ Icc 0 L, (P s)ᵀ = P s)
    (hQs : ∀ s ∈ Icc 0 L, (Q s)ᵀ = Q s)
    (hpos : ∀ s ∈ Icc 0 L, ∀ ξ, 0 ≤ pairing (Q s) ξ ξ)
    (hh : ∀ s ∈ Icc 0 L, 0 ≤ h s)
    (hdom : ∀ s ∈ Icc 0 L, (e ⬝ᵥ k s) ^ 2 ≤ h s * K)
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (v' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hode : ∀ s ∈ Icc 0 L, p ⬝ᵥ k s = -2 * v' s)
    (hwa : w 0 = 0) (hwb : w L = 0) (α : ℝ) :
    ((p - α • e) ⬝ᵥ (z L - z 0)) ^ 2 ≤
      (∫ s in (0 : ℝ)..L, pairing (P s) (p - α • e) (p - α • e) +
        4 * v s ^ 2 + α ^ 2 * K) *
      (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
  let q := p - α • e
  let ξ := fun s => z' s - w s • k s
  let F := fun s => q ⬝ᵥ ξ s + 2 * v s * w' s - α * (e ⬝ᵥ k s) * w s
  let A := fun s => pairing (P s) q q + 4 * v s ^ 2 + α ^ 2 * K
  have hξ : ContinuousOn ξ (Icc 0 L) := hzc.sub (hwc.smul hkc)
  have hE : ContinuousOn (energyDensity Q k h z' w w') (Icc 0 L) :=
    ((continuousOn_pairing hQc hξ hξ).add (hw'c.pow 2)).add (hhc.mul (hwc.pow 2))
  have hF : ContinuousOn F (Icc 0 L) := by
    apply ContinuousOn.sub
    · exact (continuousOn_dot_left hξ q).add ((hvc.const_mul 2).mul hw'c)
    · exact ((continuousOn_dot_left hkc e).const_mul α).mul hwc
  have hA : ContinuousOn A (Icc 0 L) :=
    ((continuousOn_pairing hPc continuousOn_const continuousOn_const).add
      ((hvc.pow 2).const_mul 4)).add continuousOn_const
  have hcs := interval_cauchy_of_quadratic hL hE hF hA (fun s hs r =>
    direct_pointwise_quadratic (hQP s hs) (hPs s hs) (hQs s hs) (hpos s hs)
      hK (hh s hs) (hdom s hs) q (ξ s) (v s) (w s) (w' s) α r)
  have hf : (∫ s in (0 : ℝ)..L, F s) = q ⬝ᵥ (z L - z 0) := by
    apply direct_endpoint_functional
    · simpa only [uIcc_of_le hL] using hz
    · simpa only [uIcc_of_le hL] using hv
    · simpa only [uIcc_of_le hL] using hw
    · simpa only [uIcc_of_le hL] using hode
    · exact hwa
    · exact hwb
    · exact (by simpa only [uIcc_of_le hL] using hF : ContinuousOn F (uIcc 0 L)).intervalIntegrable
  rw [hf] at hcs
  exact hcs

theorem returning_endpoint_bound
    {Ce Cm δ L v0 κ μ spp see spe E : ℝ} {p e X : TVec}
    (he : 0 < Ce) (hm : 0 < Cm) (hδ : SmallParameter Ce Cm δ)
    (hL : 0 < L) (hv : 0 < v0) (hμ : 0 < μ)
    (hκ : κ = δ * aZero) (hμdef : μ = κ * v0 / 4)
    (hinc : v0 ^ 2 ≤ κ * (p ⬝ᵥ e) ^ 2)
    (htime : 4 * v0 ≤ beta * κ * (p ⬝ᵥ e) ^ 2 * L)
    (hspp : spp ≤ L * (1 + v0 ^ 2))
    (hsee : 0 ≤ see) (hsee_upper : see ≤ Ce * L)
    (hmixed : |spe - L * (p ⬝ᵥ e)| ≤ Cm * δ * L * |p ⬝ᵥ e|)
    (hE : 0 ≤ E)
    (hS : ∀ α : ℝ, 0 ≤ spp - 2 * α * spe + α ^ 2 * see)
    (hcs : ∀ α : ℝ, ((p - α • e) ⬝ᵥ X) ^ 2 ≤
      (spp - 2 * α * spe + α ^ 2 * see) * E) :
    0 ≤ E + μ * (e ⬝ᵥ X) ^ 2 - (p ⬝ᵥ X) ^ 2 / L := by
  obtain ⟨α, hα⟩ := returning_quadratic_bound he hm hδ hL hv hμ hκ hμdef
    hinc htime hspp hsee hsee_upper hmixed
  have hb := add_boundary_cauchy (hS α) hE hμ (hcs α) (y := e ⬝ᵥ X) (α := α)
  have heq : (p - α • e) ⬝ᵥ X + α * (e ⬝ᵥ X) = p ⬝ᵥ X := by
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [heq] at hb
  have hnon : 0 ≤ E + μ * (e ⬝ᵥ X) ^ 2 := by positivity
  have ht := mul_le_mul_of_nonneg_right hα hnon
  have htop : (p ⬝ᵥ X) ^ 2 ≤ L * (E + μ * (e ⬝ᵥ X) ^ 2) := by
    nlinarith [hb, ht]
  have hdiv := (div_le_iff₀ hL).mpr (by nlinarith [htop] :
    (p ⬝ᵥ X) ^ 2 ≤ (E + μ * (e ⬝ᵥ X) ^ 2) * L)
  linarith

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

lemma concave_chord {H t₀ : ℝ} (hH : 0 < H) {t : ℝ → ℝ}
    (ht : ConcaveOn ℝ (Icc 0 H) t) (h0 : t 0 = 0) (h1 : t H = t₀)
    {s : ℝ} (hs : s ∈ Icc 0 H) : s / H * t₀ ≤ t s := by
  have hw0 : 0 ≤ 1 - s / H := sub_nonneg.mpr ((div_le_one hH).mpr hs.2)
  have hw1 : 0 ≤ s / H := div_nonneg hs.1 hH.le
  have hh := ht.2 (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH.le⟩)
    (show H ∈ Icc 0 H from ⟨hH.le, le_rfl⟩) hw0 hw1 (by ring : 1 - s / H + s / H = 1)
  simpa only [smul_eq_mul, h0, h1, mul_zero, zero_add, div_mul_cancel₀ _ hH.ne'] using hh

lemma middle_height {L tstar : ℝ} (hL : 0 < L) (hstar : 1 / 4 < tstar)
    {t : ℝ → ℝ} (ht : ConcaveOn ℝ (Icc 0 (L / 2)) t)
    (h0 : t 0 = 0) (h1 : t (L / 2) = tstar)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s) :
    ∀ s ∈ Icc (L / 4) (3 * L / 4), 1 / 8 ≤ t s := by
  have hH : 0 < L / 2 := half_pos hL
  have hhalf : ∀ s ∈ Icc (L / 4) (L / 2), 1 / 8 ≤ t s := by
    intro s hs
    have hs0 : s ∈ Icc 0 (L / 2) := ⟨by linarith [hs.1], hs.2⟩
    have hh := concave_chord hH ht h0 h1 hs0
    have hr : 1 / 2 ≤ s / (L / 2) := (le_div_iff₀ hH).mpr (by linarith [hs.1])
    nlinarith [mul_nonneg (by linarith : 0 ≤ tstar) (sub_nonneg.mpr hr)]
  intro s hs
  by_cases hfirst : s ≤ L / 2
  · exact hhalf s ⟨hs.1, hfirst⟩
  · have hss : L - s ∈ Icc (L / 4) (L / 2) := ⟨by linarith [hs.2], by linarith⟩
    have h := hhalf (L - s) hss
    rwa [hsym s ⟨by linarith [hs.1], by linarith [hs.2]⟩] at h

lemma integral_le_const {a b K : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc a b)) (hb : ∀ s ∈ Icc a b, f s ≤ K) :
    (∫ s in a..b, f s) ≤ (b - a) * K := by
  have h := intervalIntegral.integral_mono_on hab (hc.intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a b) hb
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

lemma integral_quarter_bound {L A B : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 L))
    (hout : ∀ s ∈ Icc 0 L, f s ≤ A)
    (hmid : ∀ s ∈ Icc (L / 4) (3 * L / 4), f s ≤ B) :
    (∫ s in (0 : ℝ)..L, f s) ≤ L * (A + B) / 2 := by
  have h0 : (0 : ℝ) ≤ L / 4 := by linarith
  have h1 : L / 4 ≤ 3 * L / 4 := by linarith
  have h2 : 3 * L / 4 ≤ L := by linarith
  have hc0 := hc.mono (Icc_subset_Icc le_rfl (show L / 4 ≤ L by linarith))
  have hc1 := hc.mono (Icc_subset_Icc h0 h2)
  have hc2 := hc.mono (Icc_subset_Icc (show 0 ≤ 3 * L / 4 by linarith) le_rfl)
  have hb0 := integral_le_const h0 hc0 (fun s hs => hout s ⟨hs.1, by linarith [hs.2]⟩)
  have hb1 := integral_le_const h1 hc1 hmid
  have hb2 := integral_le_const h2 hc2 (fun s hs => hout s ⟨by linarith [hs.1], hs.2⟩)
  have hi0 : IntervalIntegrable f volume 0 (L / 4) := hc0.intervalIntegrable_of_Icc h0
  have hi1 : IntervalIntegrable f volume (L / 4) (3 * L / 4) := hc1.intervalIntegrable_of_Icc h1
  have hi2 : IntervalIntegrable f volume (3 * L / 4) L := hc2.intervalIntegrable_of_Icc h2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2,
    ← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  linarith

lemma turning_time_margin {L tstar v₀ : ℝ} (hL : 0 < L) (hstar : 1 / 4 < tstar)
    {t v F₁ : ℝ → ℝ}
    (htc : ContinuousOn t (Icc 0 L))
    (hFc : ContinuousOn F₁ (Icc 0 tstar))
    (hrange : MapsTo t (Icc 0 L) (Icc 0 tstar))
    (hanti : AntitoneOn F₁ (Icc 0 tstar))
    (ht : ConcaveOn ℝ (Icc 0 (L / 2)) t)
    (h0 : t 0 = 0) (h1 : t (L / 2) = tstar)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-F₁ (t s) / 2) s)
    (hv0 : v 0 = v₀) (hv1 : v L = -v₀) :
    4 * v₀ ≤ L * (F₁ 0 + F₁ (1 / 8)) / 2 := by
  have hforce : ContinuousOn (fun s => F₁ (t s)) (Icc 0 L) := hFc.comp htc hrange
  have hint : (∫ s in (0 : ℝ)..L, F₁ (t s)) = 4 * v₀ := by
    have hd : ∀ s ∈ uIcc 0 L, HasDerivAt (fun s => -2 * v s) (F₁ (t s)) s := by
      intro s hs
      have hh := (hv s (by simpa only [uIcc_of_le hL.le] using hs)).const_mul (-2)
      convert hh using 1 <;> (first | rfl | ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hforce.intervalIntegrable_of_Icc hL.le), hv0, hv1]
    ring
  rw [← hint]
  apply integral_quarter_bound hL.le hforce
  · intro s hs
    exact hanti ⟨le_rfl, by linarith⟩ (hrange hs) (hrange hs).1
  · intro s hs
    have hss : s ∈ Icc 0 L := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact hanti ⟨by norm_num, by linarith⟩ (hrange hss)
      (middle_height hL hstar ht h0 h1 hsym s hs)

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

lemma constant_pairing_deriv {P : ℝ → TMat} {D : TMat} {u : ℝ}
    (hP : HasDerivAt P D u) (p q : TVec) :
    HasDerivAt (fun t => pairing (P t) p q) (pairing D p q) u := by
  simpa only [pairing, zero_dotProduct, Matrix.mulVec_zero, dotProduct_zero,
    zero_add, add_zero] using
    (pairing_hasDerivAt hP (hasDerivAt_const u p) (hasDerivAt_const u q))

lemma derivative_antitone {P₁ P₂ : ℝ → TMat} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt P₁ (P₂ t) t)
    (hc : ∀ t ∈ Icc 0 T, ∀ p, pairing (P₂ t) p p ≤ 0) (p : TVec) :
    AntitoneOn (fun t => pairing (P₁ t) p p) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
  · exact fun t ht => (constant_pairing_deriv (hd t ht) p p).continuousAt.continuousWithinAt
  · intro t ht
    exact (constant_pairing_deriv (hd t (interior_subset ht)) p p).hasDerivWithinAt
  · intro t ht
    exact hc t (interior_subset ht) p

lemma mixed_variation_bound {P P₁ : ℝ → TMat} {T t K p₁ : ℝ} {p e : TVec}
    (hT : T ≤ 1) (hK : 0 ≤ K) (ht : t ∈ Icc 0 T)
    (hd : ∀ u ∈ Icc 0 T, HasDerivAt P (P₁ u) u)
    (hb : ∀ u ∈ Icc 0 T, |pairing (P₁ u) e p| ≤ K)
    (hp0 : pairing (P 0) e p = p₁) : |pairing (P t) e p - p₁| ≤ K := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (constant_pairing_deriv (hd u hu) e p).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hb u hu)
    (convex_Icc 0 T) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
  rw [hp0, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at hh
  exact hh.trans (mul_le_of_le_one_right hK (ht.2.trans hT))

lemma mixed_integral_bound {L C δ p₁ : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hc : ContinuousOn f (Icc 0 L))
    (hb : ∀ s ∈ Icc 0 L, |f s - p₁| ≤ C * δ * |p₁|) :
    |(∫ s in (0 : ℝ)..L, f s) - L * p₁| ≤ C * δ * L * |p₁| := by
  have hf : IntervalIntegrable f volume 0 L := hc.intervalIntegrable_of_Icc hL
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := L) (C := C * δ * |p₁|) (f := fun s => f s - p₁)
    (fun s hs => by
      simpa only [Real.norm_eq_abs] using hb s (by simpa only [uIcc_of_le hL] using (uIoc_subset_uIcc hs)))
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    intervalIntegral.integral_const, Real.norm_eq_abs, sub_zero, abs_of_nonneg hL,
    smul_eq_mul] at hn
  nlinarith [hn]

lemma first_coefficient_bound {L v₀ : ℝ} {F v : ℝ → ℝ}
    (hL : 0 ≤ L) (hFc : ContinuousOn F (Icc 0 L)) (hvc : ContinuousOn v (Icc 0 L))
    (henergy : ∀ s ∈ Icc 0 L, F s + v s ^ 2 = 1)
    (hchord : (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * v₀ ^ 2 / 3) :
    (∫ s in (0 : ℝ)..L, F s) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2) ≤ L * (1 + v₀ ^ 2) := by
  have hvi : IntervalIntegrable (fun s => v s ^ 2) volume 0 L :=
    (hvc.pow 2).intervalIntegrable_of_Icc hL
  have hfi : IntervalIntegrable F volume 0 L := hFc.intervalIntegrable_of_Icc hL
  have hh : (∫ s in (0 : ℝ)..L, F s) + (∫ s in (0 : ℝ)..L, v s ^ 2) = L := by
    rw [← intervalIntegral.integral_add hfi hvi]
    have hc : (∫ s in (0 : ℝ)..L, F s + v s ^ 2) = (∫ _s in (0 : ℝ)..L, (1 : ℝ)) :=
      intervalIntegral.integral_congr (fun s hs => henergy s (by simpa only [uIcc_of_le hL] using hs))
    rw [hc]
    simp
  nlinarith

lemma second_coefficient_bound {L C δ : ℝ} {f : ℝ → ℝ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hδ : δ ∈ Icc 0 1)
    (hc : ContinuousOn f (Icc 0 L)) (hb : ∀ s ∈ Icc 0 L, f s ≤ C) :
    (∫ s in (0 : ℝ)..L, f s) + 2 * C * δ * L ≤ 3 * C * L := by
  have hi := ReturningTime.integral_le_const hL hc hb
  have hd := mul_le_mul_of_nonneg_left hδ.2 (show 0 ≤ 2 * C * L by positivity)
  nlinarith

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

lemma coordinateCometric_smooth (right : Bool) (δ : ℝ) :
    ContDiff ℝ ∞ (coordinateCometric right δ) := by
  cases right
  · exact P_smooth δ
  · exact (congruenceCLM (C₂ δ)).contDiff.comp
      ((P_smooth δ).comp (contDiff_const.sub contDiff_id))

lemma coordinateCometric_transpose (right : Bool) (δ t : ℝ) :
    (coordinateCometric right δ t)ᵀ = coordinateCometric right δ t := by
  cases right
  · exact Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ t)
  · change (C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ)ᵀ = C₂ δ * P δ (1 - t) * (C₂ δ)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ (1 - t)), Matrix.mul_assoc]

lemma endpoint_derivative_qform (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) p p = δ * a 0 * p 0 ^ 2 := by
  rw [coordinateCometric_end_deriv (by norm_num : (0 : ℝ) < 1 / 4)]
  simp only [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero]
  ring

lemma a_eighth : a (1 / 8) = a 0 * Real.exp (-(9 : ℝ) / 26) := by
  have hh := a_eighth_ratio
  have ha := a_pos (u := 0) (by norm_num)
  exact (div_eq_iff ha.ne').mp hh |>.trans (mul_comm _ _)

lemma exact_timing_constant (δ L p₁ : ℝ) :
    L * (δ * a 0 * p₁ ^ 2 + δ * a (1 / 8) * p₁ ^ 2) / 2 =
      Turning.beta * (δ * Turning.aZero) * p₁ ^ 2 * L := by
  rw [a_eighth, a_zero]
  dsimp [Turning.beta, Turning.aZero]
  ring

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

lemma sqnorm_e : sqnorm e = 1 := by norm_num [e, sqnorm]

lemma actual_force_end_values (right : Bool) (δ : ℝ) (p : TVec) :
    pairing (deriv (coordinateCometric right δ) 0) p p = δ * a 0 * p 0 ^ 2 ∧
    pairing (deriv (coordinateCometric right δ) (1 / 8)) p p = δ * a (1 / 8) * p 0 ^ 2 := by
  refine ⟨endpoint_derivative_qform right δ p, ?_⟩
  rw [coordinateCometric_end_deriv (by norm_num : (1 / 8 : ℝ) < 1 / 4)]
  simp only [pairing, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, add_zero]
  ring

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix

lemma contDiff_pairing_const {R : ℝ → TMat} {n : WithTop ℕ∞}
    (hR : ContDiff ℝ n R) (p q : TVec) : ContDiff ℝ n (fun u => pairing (R u) p q) := by
  simp only [pairing, Matrix.mulVec, dotProduct]
  fun_prop

lemma force_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (force right δ p) :=
  contDiff_pairing_const (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2 p p

lemma force_antitone {right : Bool} {δ T : ℝ} {p : TVec}
    (hT : T ≤ 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q) :
    AntitoneOn (force right δ p) (Icc 0 T) := by
  apply derivative_antitone (P₂ := deriv (deriv (coordinateCometric right δ)))
    (fun u _ => ((contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2.differentiable
      (by simp)).differentiableAt.hasDerivAt)
  intro u hu q
  have hh := hc u ⟨hu.1, hu.2.trans hT⟩ q
  change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) u) q q at hh
  rw [pairing_matrix_neg] at hh
  linarith

lemma incidence_bound {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hT : t (L / 2) ∈ Ioo 0 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hf : ∀ u ∈ Icc 0 (t (L / 2)), 0 < force right δ p u)
    (h0 : t 0 = 0) (hvc : v (L / 2) = 0)
    (he0 : potential right δ p (t 0) + v 0 ^ 2 = 1)
    (hec : potential right δ p (t (L / 2)) + v (L / 2) ^ 2 = 1) :
    v 0 ^ 2 ≤ δ * Turning.aZero * p 0 ^ 2 := by
  have ha := force_antitone hT.2.le hc (p := p)
  have hbound : ∀ u ∈ Icc 0 (t (L / 2)),
      |force right δ p u| ≤ δ * a 0 * p 0 ^ 2 := by
    intro u hu
    rw [abs_of_pos (hf u hu)]
    have hh := ha ⟨le_rfl, hT.1.le⟩ hu hu.1
    simpa only [force, endpoint_derivative_qform] using hh
  have hh := mixed_variation_bound hT.2.le
    (mul_nonneg (mul_nonneg hδ (a_nonneg 0)) (sq_nonneg (p 0)))
    (show t (L / 2) ∈ Icc 0 (t (L / 2)) from ⟨hT.1.le, le_rfl⟩)
    (fun u _ => ((coordinateCometric_smooth right δ).differentiable (by simp)).differentiableAt.hasDerivAt)
    hbound (show pairing (coordinateCometric right δ 0) p p = potential right δ p 0 from rfl)
  rw [h0] at he0
  rw [hvc] at hec
  change |potential right δ p (t (L / 2)) - potential right δ p 0| ≤ _ at hh
  rw [a_zero] at hh
  dsimp only [Turning.aZero]
  linarith [(abs_le.mp hh).2]

lemma actual_timing_margin {right : Bool} {δ L : ℝ} {p : TVec} {t v : ℝ → ℝ}
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2)) (hT : t (L / 2) < 1)
    (hc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (hrange : MapsTo t (Icc 0 L) (Icc 0 (t (L / 2))))
    (htconc : ConcaveOn ℝ (Icc 0 (L / 2)) t) (h0 : t 0 = 0)
    (hsym : ∀ s ∈ Icc 0 L, t (L - s) = t s ∧ v (L - s) = -v s) :
    4 * v 0 ≤ Turning.beta * (δ * Turning.aZero) * p 0 ^ 2 * L := by
  have he := hsym 0 ⟨le_rfl, hL.le⟩
  simp only [sub_zero] at he
  have hh := turning_time_margin hL hstar (HasDerivAt.continuousOn ht)
    (force_smooth right δ p).continuous.continuousOn hrange (force_antitone hT.le hc)
    htconc h0 rfl (fun s hs => (hsym s hs).1) hv rfl he.2
  dsimp only [force] at hh
  rw [(actual_force_end_values right δ p).1, (actual_force_end_values right δ p).2,
    exact_timing_constant] at hh
  exact hh

end

open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning

lemma coordinateCometric_posDef {right : Bool} {δ u : ℝ}
    (hbound : ∀ q, sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q) :
    (coordinateCometric right δ u).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr (coordinateCometric_transpose right δ u))
  intro q hq
  change 0 < qform (coordinateCometric right δ u) q
  have hs := sqnorm_pos hq
  have hh := hbound q
  linarith

lemma coordinateCometric_inv_continuousAt {right : Bool} {δ u : ℝ}
    (hbound : ∀ q, sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q) :
    ContinuousAt (fun t => (coordinateCometric right δ t)⁻¹) u := by
  have hd : (coordinateCometric right δ u).det ≠ 0 :=
    (coordinateCometric_posDef hbound).det_pos.ne'
  apply (continuousAt_matrix_inv (coordinateCometric right δ u) ?_).comp
    (coordinateCometric_smooth right δ).continuous.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hd

lemma coefficient_expansion {L K : ℝ} (hL : 0 ≤ L) {R : ℝ → TMat} {v : ℝ → ℝ}
    (hR : ContinuousOn R (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hs : ∀ s ∈ Icc 0 L, (R s)ᵀ = R s) (p e : TVec) (α : ℝ) :
    (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) =
    ((∫ s in (0 : ℝ)..L, pairing (R s) p p) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2)) -
      2 * α * (∫ s in (0 : ℝ)..L, pairing (R s) e p) +
      α ^ 2 * ((∫ s in (0 : ℝ)..L, pairing (R s) e e) + K * L) := by
  have hpp : IntervalIntegrable (fun s => pairing (R s) p p) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => p) (v := fun _ => p)).intervalIntegrable_of_Icc hL
  have hep : IntervalIntegrable (fun s => pairing (R s) e p) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => e) (v := fun _ => p)).intervalIntegrable_of_Icc hL
  have hee : IntervalIntegrable (fun s => pairing (R s) e e) volume 0 L := (continuousOn_pairing hR continuousOn_const continuousOn_const
    (u := fun _ => e) (v := fun _ => e)).intervalIntegrable_of_Icc hL
  have hvv : IntervalIntegrable (fun s => v s ^ 2) volume 0 L := (hv.pow 2).intervalIntegrable_of_Icc hL
  have heq : (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) =
      (∫ s in (0 : ℝ)..L, (pairing (R s) p p + 4 * v s ^ 2) -
        2 * α * pairing (R s) e p + α ^ 2 * (pairing (R s) e e + K)) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hss : s ∈ Icc 0 L := by simpa only [uIcc_of_le hL] using hs'
    simp only [pairing_sub_left, pairing_sub_right, pairing_smul_left, pairing_smul_right,
      pairing_symm (hs s hss) p e]
    ring
  rw [heq, intervalIntegral.integral_add ((hpp.add (hvv.const_mul 4)).sub
      (hep.const_mul (2 * α))) ((hee.add intervalIntegrable_const).const_mul (α ^ 2)),
    intervalIntegral.integral_sub (hpp.add (hvv.const_mul 4)) (hep.const_mul (2 * α)),
    intervalIntegral.integral_add hpp (hvv.const_mul 4),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hee intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

lemma direct_coefficient_nonneg {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {R : ℝ → TMat} {v : ℝ → ℝ}
    (hp : ∀ s ∈ Icc 0 L, ∀ q, 0 ≤ pairing (R s) q q) (p e : TVec) (α : ℝ) :
    0 ≤ (∫ s in (0 : ℝ)..L, pairing (R s) (p - α • e) (p - α • e) +
      4 * v s ^ 2 + α ^ 2 * K) := by
  apply intervalIntegral.integral_nonneg hL
  intro s hs
  have hh := hp s hs (p - α • e)
  positivity

lemma energy_nonnegative {L : ℝ} (hL : 0 ≤ L)
    {Q : ℝ → TMat} {k z' : ℝ → TVec} {h w w' : ℝ → ℝ}
    (hp : ∀ s ∈ Icc 0 L, ∀ q, 0 ≤ pairing (Q s) q q)
    (hh : ∀ s ∈ Icc 0 L, 0 ≤ h s) :
    0 ≤ (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
  apply intervalIntegral.integral_nonneg hL
  intro s hs
  dsimp only [energyDensity]
  have hh' := hh s hs
  have hp' := hp s hs (z' s - w s • k s)
  positivity

lemma sourceMixed_pos (C : ℝ) : 0 < sourceMixed C := by
  have hp := a_pos (u := 0) (by norm_num)
  dsimp only [sourceMixed]
  positivity

lemma e_dot (p : TVec) : p ⬝ᵥ e = p 0 := by
  simp [e, dotProduct, Fin.sum_univ_two]

theorem actual_returning_energy_bound {right : Bool} {δ C L : ℝ} {p : TVec}
    {t v : ℝ → ℝ} (hC : 18 ≤ C)
    (hδ : SmallParameter (3 * C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q,
      sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C ^ 2 * δ ^ 2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hL : 0 < L) (hstar : 1 / 4 < t (L / 2))
    (ht : ∀ s ∈ Icc 0 L, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 L, HasDerivAt v (-force right δ p (t s) / 2) s)
    (h0 : t 0 = 0) (h1 : t L = 0)
    (hrange : ∀ s ∈ Ioo 0 L, t s ∈ Ioo 0 1)
    (henergy : ∀ s ∈ Icc 0 L, potential right δ p (t s) + v s ^ 2 = 1)
    {z z' : ℝ → TVec} {w w' : ℝ → ℝ}
    (hzc : ContinuousOn z' (Icc 0 L)) (hw'c : ContinuousOn w' (Icc 0 L))
    (hz : ∀ s ∈ Icc 0 L, HasDerivAt z (z' s) s)
    (hw : ∀ s ∈ Icc 0 L, HasDerivAt w (w' s) s)
    (hwa : w 0 = 0) (hwb : w L = 0) :
    0 ≤ (∫ s in (0 : ℝ)..L,
      energyDensity (fun s => (coordinateCometric right δ (t s))⁻¹)
        (fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p)
        (fun s => -forceDerivative right δ p (t s) / 2) z' w w' s) +
      (δ * aZero * v 0 / 4) * (e ⬝ᵥ (z L - z 0)) ^ 2 - (p ⬝ᵥ (z L - z 0)) ^ 2 / L := by
  have hCp : 0 < C := by linarith
  have hδp := hδ.1
  have hap := aZero_pos
  obtain ⟨hv0, hvc, hT, hmaps, hsym, hforce, _, htconc, hchord⟩ :=
    returning_dynamics hL hconc ht hv h0 h1 hrange henergy
  have hmap : MapsTo t (Icc 0 L) (Icc 0 1) := by
    intro s hs
    exact ⟨(hmaps hs).1, (hmaps hs).2.trans hT.2.le⟩
  have hinc := incidence_bound hδ.1.le hT hconc hforce h0 hvc
    (henergy 0 ⟨le_rfl, hL.le⟩) (henergy (L / 2) ⟨by linarith, by linarith⟩)
  have htime := actual_timing_margin hL hstar hT.2 hconc ht hv hmaps htconc h0 hsym
  let R := fun s => coordinateCometric right δ (t s)
  let Q := fun s => (R s)⁻¹
  let k := fun s => deriv (coordinateCometric right δ) (t s) *ᵥ p
  let h := fun s => -forceDerivative right δ p (t s) / 2
  let K := 2 * C * δ
  let spp := (∫ s in (0 : ℝ)..L, pairing (R s) p p) + 4 * (∫ s in (0 : ℝ)..L, v s ^ 2)
  let see := (∫ s in (0 : ℝ)..L, pairing (R s) e e) + K * L
  let spe := (∫ s in (0 : ℝ)..L, pairing (R s) e p)
  have htc := HasDerivAt.continuousOn ht
  have hRc : ContinuousOn R (Icc 0 L) :=
    (coordinateCometric_smooth right δ).continuous.comp_continuousOn htc
  have hQc : ContinuousOn Q (Icc 0 L) := by
    intro s hs
    exact (coordinateCometric_inv_continuousAt (fun q => (hbound (t s) (hmap hs) q).1)).comp_continuousWithinAt (htc s hs)
  have hkc : ContinuousOn k (Icc 0 L) :=
    ((contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2.continuous.matrix_mulVec
      continuous_const).comp_continuousOn htc
  have hhc : ContinuousOn h (Icc 0 L) := by
    have hc : Continuous (forceDerivative right δ p) :=
      (contDiff_pairing_const (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2).2 p p).continuous
    exact (hc.comp_continuousOn htc).neg.div_const 2
  have hPs (s : ℝ) : (R s)ᵀ = R s := coordinateCometric_transpose right δ (t s)
  have hQs (s : ℝ) : (Q s)ᵀ = Q s := by
    dsimp only [Q]
    rw [Matrix.transpose_nonsing_inv, hPs]
  have hPd (s : ℝ) (hs : s ∈ Icc 0 L) : (R s).PosDef :=
    coordinateCometric_posDef (fun q => (hbound (t s) (hmap hs) q).1)
  have hQP (s : ℝ) (hs : s ∈ Icc 0 L) : Q s * R s = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hPd s hs).det_pos.ne')
  have hPnon (s : ℝ) (hs : s ∈ Icc 0 L) (q : TVec) : 0 ≤ pairing (R s) q q := by
    have hh := (hbound (t s) (hmap hs) q).1
    have hn := sqnorm_nonneg q
    change sqnorm q / 9 ≤ pairing (R s) q q at hh
    linarith
  have hQnon (s : ℝ) (hs : s ∈ Icc 0 L) (q : TVec) : 0 ≤ pairing (Q s) q q := by
    exact (hPd s hs).inv.posSemidef.dotProduct_mulVec_nonneg q
  have hh (s : ℝ) (hs : s ∈ Icc 0 L) : 0 ≤ h s := by
    have hc := hconc (t s) (hmap hs) p
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p at hc
    rw [pairing_matrix_neg] at hc
    exact div_nonneg hc (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hdom' (s : ℝ) (hs : s ∈ Icc 0 L) : (e ⬝ᵥ k s) ^ 2 ≤ h s * K := by
    have hd := hdom (t s) (hmap hs)
    have hk : (e ⬝ᵥ k s) ^ 2 ≤ sqnorm (k s) := by
      rw [dotProduct_comm, e_dot]
      dsimp only [sqnorm]
      nlinarith [sq_nonneg (k s 1)]
    have he : C * δ * qform (-deriv (deriv (coordinateCometric right δ)) (t s)) p = h s * K := by
      change C * δ * pairing (-deriv (deriv (coordinateCometric right δ)) (t s)) p p = _
      rw [pairing_matrix_neg]
      dsimp only [h, K, forceDerivative]
      ring
    exact hk.trans (he ▸ hd)
  have hvc' := HasDerivAt.continuousOn hv
  have hspp : spp ≤ L * (1 + v 0 ^ 2) :=
    first_coefficient_bound hL.le (continuousOn_pairing hRc continuousOn_const continuousOn_const)
      hvc' henergy hchord
  have hsee : 0 ≤ see := by
    have hi : 0 ≤ (∫ s in (0 : ℝ)..L, pairing (R s) e e) :=
      intervalIntegral.integral_nonneg hL.le (fun s hs => hPnon s hs e)
    dsimp only [see]
    positivity
  have hsee_upper : see ≤ (3 * C) * L := by
    apply second_coefficient_bound hL.le hCp.le ⟨hδ.1.le, hδ.2.1⟩
      (continuousOn_pairing hRc continuousOn_const continuousOn_const)
    intro s hs
    have hh := (hbound (t s) (hmap hs) e).2
    rw [sqnorm_e, mul_one] at hh
    exact hh.trans hC
  have hmixed : |spe - L * p 0| ≤ sourceMixed C * δ * L * |p 0| := by
    have hamb := actual_mixed_bound hδ.1.le hCp ⟨hT.1.le, hT.2.le⟩ hconc hder
      (fun u hu => (hforce u hu).le)
    have hi := mixed_integral_bound hL.le
      (continuousOn_pairing hRc continuousOn_const continuousOn_const)
      (fun s hs => hamb (t s) (hmaps hs))
    apply hi.trans
    have hm : a 0 + Real.sqrt (2 * C * a 0) ≤ sourceMixed C := by
      dsimp only [sourceMixed]
      linarith [Real.sqrt_nonneg (2 * C * a 0 / 3)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hδ.1.le) hL.le) (abs_nonneg _)
  have hcs (α : ℝ) : ((p - α • e) ⬝ᵥ (z L - z 0)) ^ 2 ≤
      (spp - 2 * α * spe + α ^ 2 * see) *
        (∫ s in (0 : ℝ)..L, energyDensity Q k h z' w w' s) := by
    have hh := direct_endpoint_cauchy hL.le hK p e hRc hQc hkc hhc hvc' hzc
      (HasDerivAt.continuousOn hw) hw'c hQP (fun s _ => hPs s) (fun s _ => hQs s)
      hQnon hh hdom' hz hv hw (fun s _ => by dsimp only [k, force, pairing]; ring) hwa hwb α
    rw [coefficient_expansion hL.le hRc hvc' (fun s _ => hPs s)] at hh
    exact hh
  apply returning_endpoint_bound (by positivity : 0 < 3 * C) (sourceMixed_pos C) hδ hL hv0
    (by positivity : 0 < δ * aZero * v 0 / 4) rfl rfl
    (by simpa only [e_dot] using hinc) (by simpa only [e_dot] using htime)
    hspp hsee hsee_upper (by simpa only [e_dot] using hmixed)
    (energy_nonnegative hL.le hQnon hh) ?_ hcs
  intro α
  rw [← coefficient_expansion hL.le hRc hvc' (fun s _ => hPs s)]
  exact direct_coefficient_nonneg hL.le hK hPnon p e α

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound := @_root_.OAI.ThreeManifold.ReturningPassage.actual_returning_energy_bound
