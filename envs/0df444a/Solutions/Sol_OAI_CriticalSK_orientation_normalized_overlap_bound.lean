-- Prove2me | solution 1 for OAI.CriticalSK.orientation_normalized_overlap_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:37:33.177834+00:00
-- url     : https://prove2.me/submissions/18f9eb5e-4201-4dd7-bef8-34fb1c95bef0

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK001
import Theorems.Thm_OAI_CriticalSK_pairMoment_variational_upper_general

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.SphereGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
namespace CriticalSK


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orthogonalIsometry_mul (U V : Matrix.orthogonalGroup ι ℝ) (x : EuclideanSpace ℝ ι) :
    orthogonalIsometry (U*V) x = orthogonalIsometry U (orthogonalIsometry V x) :=
  euclideanMatrix_mul_apply _ _ _

lemma orthogonalIsometry_fixed_continuous (x : EuclideanSpace ℝ ι) :
    Continuous (fun U : Matrix.orthogonalGroup ι ℝ => orthogonalIsometry U x) := by
  change Continuous (fun U : Matrix.orthogonalGroup ι ℝ =>
    WithLp.toLp 2 (fun i => ∑ j, (U : Matrix ι ι ℝ) i j * x j))
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hU : Continuous (fun U : Matrix.orthogonalGroup ι ℝ => (U : Matrix ι ι ℝ)) :=
    continuous_subtype_val
  exact ((continuous_apply j).comp ((continuous_apply i).comp hU)).mul continuous_const

lemma orthogonalIsometry_matrixOfIsometry (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    orthogonalIsometry (matrixOfIsometry U) = U := by
  ext x i
  change (Matrix.toEuclideanLin (LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis U.toLinearMap) x) i = U x i
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
  rfl

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereArea_pos : 0 < sphereArea (ι := ι) := by
  exact ENNReal.toReal_pos ((measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne')
    (measure_ne_top _ _)

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orthogonal_pair_transitive {x y x' y' : EuclideanSpace ℝ ι}
    (hx : ‖x‖ = ‖x'‖) (hy : ‖y‖ = ‖y'‖)
    (hxy : inner ℝ x y = inner ℝ x' y') :
    ∃ U : Matrix.orthogonalGroup ι ℝ,
      orthogonalIsometry U x = x' ∧ orthogonalIsometry U y = y' := by
  let A := Submodule.reflection (ℝ ∙ (x-x'))ᗮ
  have hA : A x = x' := Submodule.reflection_sub hx
  let B := Submodule.reflection (ℝ ∙ (A y-y'))ᗮ
  have hBx : B x' = x' := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right]
    have he : inner ℝ x' (A y) = inner ℝ x y := by
      rw [← hA, A.inner_map_map]
    rw [he, hxy, sub_self]
  have hBy : B (A y) = y' := Submodule.reflection_sub ((A.norm_map y).trans hy)
  refine ⟨matrixOfIsometry (A.trans B), ?_, ?_⟩
  · rw [orthogonalIsometry_matrixOfIsometry]
    change B (A x) = x'
    rw [hA, hBx]
  · rw [orthogonalIsometry_matrixOfIsometry]
    exact hBy

lemma orthogonal_pair_integral_eq (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ)
    {x y x' y' : EuclideanSpace ℝ ι} (hx : ‖x‖ = ‖x'‖) (hy : ‖y‖ = ‖y'‖)
    (hxy : inner ℝ x y = inner ℝ x' y') :
    (∫ U, f (orthogonalIsometry U x) (orthogonalIsometry U y) ∂orthogonalHaar ι) =
      ∫ U, f (orthogonalIsometry U x') (orthogonalIsometry U y') ∂orthogonalHaar ι := by
  obtain ⟨V,hVx,hVy⟩ := orthogonal_pair_transitive hx hy hxy
  rw [← hVx, ← hVy]
  simp_rw [← orthogonalIsometry_mul]
  exact (integral_mul_right_eq_self
    (fun U => f (orthogonalIsometry U x) (orthogonalIsometry U y)) V).symm

lemma orthogonal_pair_swap (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ)
    {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
    (∫ U, f (orthogonalIsometry U x) (orthogonalIsometry U y) ∂orthogonalHaar ι) =
      ∫ U, f (orthogonalIsometry U y) (orthogonalIsometry U x) ∂orthogonalHaar ι := by
  exact orthogonal_pair_integral_eq f hxy hxy.symm (real_inner_comm _ _)

omit [DecidableEq ι] in
lemma diagonalEnergy_continuous (lam : ι → ℝ) : Continuous (diagonalEnergy lam) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((PiLp.continuous_apply 2 _ i).pow 2)

lemma orthogonalHaar_integrable {f : Matrix.orthogonalGroup ι ℝ → ℝ} (hf : Continuous f) :
    Integrable f (orthogonalHaar ι) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

lemma pairIntegrand_continuous (lam : ι → ℝ) (x y : EuclideanSpace ℝ ι) (q : ℝ) :
    Continuous (pairIntegrand lam x y q) := by
  have hx := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous x)
  have hy := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous y)
  exact ((continuous_const.mul hx).add (continuous_const.mul hy)).div_const 2 |>.rexp

lemma pairMoment_nonneg (lam : ι → ℝ) (x y : EuclideanSpace ℝ ι) (q : ℝ) :
    0 ≤ pairMoment lam x y q := integral_nonneg (fun _ => (Real.exp_pos _).le)

lemma pairMoment_even (lam : ι → ℝ) {x y : EuclideanSpace ℝ ι}
    (hxy : ‖x‖ = ‖y‖) (q : ℝ) : pairMoment lam x y (-q) = pairMoment lam x y q := by
  unfold pairMoment pairIntegrand
  rw [orthogonal_pair_swap (fun a b => Real.exp (((1+-q)*diagonalEnergy lam a +
    (1- -q)*diagonalEnergy lam b)/2)) hxy]
  apply integral_congr_ae
  filter_upwards [] with U
  congr 1
  ring

lemma exp_pair_cosh (A D q : ℝ) :
    Real.exp ((A+D)/2) * Real.cosh (q*(A-D)/2) =
      (Real.exp (((1+q)*A+(1-q)*D)/2) + Real.exp (((1-q)*A+(1+q)*D)/2))/2 := by
  rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring_nf

lemma pairMoment_cosh (lam : ι → ℝ) {x y : EuclideanSpace ℝ ι}
    (hxy : ‖x‖ = ‖y‖) (q : ℝ) :
    pairMoment lam x y q = ∫ U,
      Real.exp ((diagonalEnergy lam (orthogonalIsometry U x) +
          diagonalEnergy lam (orthogonalIsometry U y))/2) *
        Real.cosh (q*(diagonalEnergy lam (orthogonalIsometry U x) -
          diagonalEnergy lam (orthogonalIsometry U y))/2) ∂orthogonalHaar ι := by
  simp_rw [exp_pair_cosh]
  have hf (U : Matrix.orthogonalGroup ι ℝ) :
      Real.exp (((1-q)*diagonalEnergy lam (orthogonalIsometry U x)+
        (1+q)*diagonalEnergy lam (orthogonalIsometry U y))/2) = pairIntegrand lam x y (-q) U := by
    unfold pairIntegrand
    congr 1
    ring
  simp_rw [hf]
  rw [integral_div]
  change pairMoment lam x y q =
    (∫ U, pairIntegrand lam x y q U + pairIntegrand lam x y (-q) U ∂orthogonalHaar ι)/2
  rw [integral_add (orthogonalHaar_integrable (pairIntegrand_continuous lam x y q))
    (orthogonalHaar_integrable (pairIntegrand_continuous lam x y (-q)))]
  change pairMoment lam x y q = (pairMoment lam x y q + pairMoment lam x y (-q))/2
  rw [pairMoment_even lam hxy]
  ring

lemma pairMoment_mono_abs (lam : ι → ℝ) {x y : EuclideanSpace ℝ ι}
    (hxy : ‖x‖ = ‖y‖) {q r : ℝ} (hqr : |q| ≤ |r|) :
    pairMoment lam x y q ≤ pairMoment lam x y r := by
  rw [pairMoment_cosh lam hxy q, pairMoment_cosh lam hxy r]
  have hx := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous x)
  have hy := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous y)
  have hc (t : ℝ) : Continuous (fun U : Matrix.orthogonalGroup ι ℝ =>
      Real.exp ((diagonalEnergy lam (orthogonalIsometry U x) +
          diagonalEnergy lam (orthogonalIsometry U y))/2) *
        Real.cosh (t*(diagonalEnergy lam (orthogonalIsometry U x) -
          diagonalEnergy lam (orthogonalIsometry U y))/2)) := by
    exact ((hx.add hy).div_const 2).rexp.mul
      (Real.continuous_cosh.comp ((continuous_const.mul (hx.sub hy)).div_const 2))
  apply integral_mono (orthogonalHaar_integrable (hc q)) (orthogonalHaar_integrable (hc r))
  intro U
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.cosh_le_cosh.mpr
  simp only [abs_div, abs_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqr (abs_nonneg _)) (abs_nonneg _)

end


section

lemma cubeVector_norm {n : ℕ} (x : Spin n) : ‖cubeVector x‖ = Real.sqrt n := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg _), EuclideanSpace.real_norm_sq_eq]
  change ∑ i : Fin n, spinValue (x i)^2 = (n : ℝ)
  simp only [spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma overlapPair_gram {u v : EuclideanSpace ℝ ι} {r q : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) (hq : |q| ≤ 1) :
    ‖overlapPlus u v q‖ = r ∧ ‖overlapMinus u v q‖ = r ∧
      inner ℝ (overlapPlus u v q) (overlapMinus u v q) = q * r^2 := by
  have hp : 0 ≤ (1+q)/2 := by linarith [(abs_le.mp hq).1]
  have hm : 0 ≤ (1-q)/2 := by linarith [(abs_le.mp hq).2]
  have hpu := Real.sq_sqrt hp
  have hmu := Real.sq_sqrt hm
  have horth' : inner ℝ v u = 0 := by rw [real_inner_comm, horth]
  have huu : inner ℝ u u = r^2 := by rw [real_inner_self_eq_norm_sq, hu]
  have hvv : inner ℝ v v = r^2 := by rw [real_inner_self_eq_norm_sq, hv]
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hplus : ‖overlapPlus u v q‖^2 = r^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [overlapPlus, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, horth, horth', huu, hvv]
    nlinarith
  have hminus : ‖overlapMinus u v q‖^2 = r^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [overlapMinus, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, horth, horth', huu, hvv]
    nlinarith
  refine ⟨(sq_eq_sq₀ (norm_nonneg _) hr).mp hplus,
    (sq_eq_sq₀ (norm_nonneg _) hr).mp hminus, ?_⟩
  simp only [overlapPlus, overlapMinus, inner_add_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, horth, horth', huu, hvv]
  nlinarith

omit [DecidableEq ι] in
lemma diagonalEnergy_overlap (lam : ι → ℝ) (u v : EuclideanSpace ℝ ι) {q : ℝ}
    (hq : |q| ≤ 1) :
    diagonalEnergy lam (overlapPlus u v q) + diagonalEnergy lam (overlapMinus u v q) =
      (1+q)*diagonalEnergy lam u + (1-q)*diagonalEnergy lam v := by
  have hp : 0 ≤ (1+q)/2 := by linarith [(abs_le.mp hq).1]
  have hm : 0 ≤ (1-q)/2 := by linarith [(abs_le.mp hq).2]
  have hpu := Real.sq_sqrt hp
  have hmu := Real.sq_sqrt hm
  unfold diagonalEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [overlapPlus, overlapMinus, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  calc
    _ = 2 * lam i * (Real.sqrt ((1+q)/2))^2 * (u i)^2 +
        2 * lam i * (Real.sqrt ((1-q)/2))^2 * (v i)^2 := by ring
    _ = _ := by rw [hpu, hmu]; ring

lemma pair_energy_orbit (lam : ι → ℝ) {x y u v : EuclideanSpace ℝ ι} {r q : ℝ}
    (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (horth : inner ℝ u v = 0) (hq : |q| ≤ 1) (hxy : inner ℝ x y = q*r^2) :
    (∫ U, Real.exp ((diagonalEnergy lam (orthogonalIsometry U x) +
        diagonalEnergy lam (orthogonalIsometry U y))/2) ∂orthogonalHaar ι) =
      pairMoment lam u v q := by
  obtain ⟨hplus,hminus,hgram⟩ := overlapPair_gram hu hv horth hq
  rw [orthogonal_pair_integral_eq
    (fun a b => Real.exp ((diagonalEnergy lam a + diagonalEnergy lam b)/2))
    (hx.trans hplus.symm) (hy.trans hminus.symm) (hxy.trans hgram.symm)]
  unfold pairMoment pairIntegrand
  apply integral_congr_ae
  filter_upwards [] with U
  have hplus' : orthogonalIsometry U (overlapPlus u v q) =
      overlapPlus (orthogonalIsometry U u) (orthogonalIsometry U v) q := by
    simp only [overlapPlus, map_add, map_smul]
  have hminus' : orthogonalIsometry U (overlapMinus u v q) =
      overlapMinus (orthogonalIsometry U u) (orthogonalIsometry U v) q := by
    simp only [overlapMinus, map_sub, map_smul]
  rw [hplus', hminus', diagonalEnergy_overlap lam _ _ hq]

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pairMoment_continuous (lam : ι → ℝ) (u v : EuclideanSpace ℝ ι) :
    Continuous (pairMoment lam u v) := by
  have hu : Continuous (fun p : ℝ × Matrix.orthogonalGroup ι ℝ =>
      diagonalEnergy lam (orthogonalIsometry p.2 u)) :=
    ((diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous u)).comp
      continuous_snd
  have hv : Continuous (fun p : ℝ × Matrix.orthogonalGroup ι ℝ =>
      diagonalEnergy lam (orthogonalIsometry p.2 v)) :=
    ((diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous v)).comp
      continuous_snd
  have hc : Continuous (fun p : ℝ × Matrix.orthogonalGroup ι ℝ =>
      pairIntegrand lam u v p.1 p.2) :=
    ((((continuous_const.add continuous_fst).mul hu).add
      ((continuous_const.sub continuous_fst).mul hv)).div_const 2).rexp
  have hi := continuous_parametric_integral_of_continuous (μ := orthogonalHaar ι)
    (f := fun q U => pairIntegrand lam u v q U) hc (s := Set.univ) isCompact_univ
  change Continuous (fun q : ℝ => ∫ U, pairIntegrand lam u v q U ∂orthogonalHaar ι)
  simpa only [setIntegral_univ] using hi

end

section

lemma spinValue_beq (a b : Bool) : spinValue (a == b) = spinValue a * spinValue b := by
  cases a <;> cases b <;> norm_num [spinValue]

lemma cubeOverlap_signMean {n : ℕ} (x y : Spin n) :
    cubeOverlap x y = signMean (spinProduct x y) := by
  unfold cubeOverlap signMean cubeVector
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, dotProduct, spinProduct, spinValue_beq, mul_comm]

lemma cubeOverlap_abs_le_one {n : ℕ} (x y : Spin n) : |cubeOverlap x y| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cubeOverlap]
  have h := abs_real_inner_le_norm (cubeVector x) (cubeVector y)
  rw [cubeVector_norm, cubeVector_norm, ← sq, Real.sq_sqrt (Nat.cast_nonneg _)] at h
  unfold cubeOverlap
  rw [abs_div, show |(n : ℝ)| = n from abs_of_nonneg (Nat.cast_nonneg n)]
  exact (div_le_one (Nat.cast_pos.mpr hn)).mpr h

lemma cubeOverlap_gram {n : ℕ} (hn : 0 < n) (x y : Spin n) :
    inner ℝ (cubeVector x) (cubeVector y) = cubeOverlap x y * (Real.sqrt n)^2 := by
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')).symm

lemma cubeOverlap_sum {n : ℕ} (x : Spin n) (f : ℝ → ℝ) :
    (∑ y : Spin n, f (cubeOverlap x y)) = ∑ y : Spin n, f (signMean y) := by
  simp_rw [cubeOverlap_signMean]
  exact (spinProductEquiv x).sum_comp (fun y => f (signMean y))

lemma cubeOverlap_average {n : ℕ} (f : ℝ → ℝ) :
    (Fintype.card (Spin n) : ℝ)⁻¹ ^ 2 * ∑ x : Spin n, ∑ y : Spin n, f (cubeOverlap x y) =
      (Fintype.card (Spin n) : ℝ)⁻¹ * ∑ y : Spin n, f (signMean y) := by
  simp_rw [cubeOverlap_sum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card (Spin n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma signMean_finset {n : ℕ} (hn : 0 < n) (x : Spin n) :
    signMean x = -1 + 2 * ((spinFinsetEquiv n x).card : ℝ) / n := by
  have he : (∑ i : Fin n, spinValue (x i)) =
      2 * ((spinFinsetEquiv n x).card : ℝ) - n := by
    have hv (i : Fin n) : spinValue (x i) = (if x i = true then 2 else 0) - 1 := by
      cases x i <;> norm_num [spinValue]
    simp_rw [hv, Finset.sum_sub_distrib]
    simp [spinFinsetEquiv, Finset.sum_ite, mul_comm]
  rw [signMean, he]
  field_simp [Nat.cast_ne_zero.mpr hn.ne']
  ring

lemma finset_card_sum (n : ℕ) (f : ℕ → ℝ) :
    (∑ s : Finset (Fin n), f s.card) =
      ∑ k ∈ Finset.range (n+1), (Nat.choose n k : ℝ) * f k := by
  have hm (s : Finset (Fin n)) (_ : s ∈ Finset.univ) : s.card ∈ Finset.range (n+1) := by
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (by simpa using s.card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  simp only [Finset.sum_const, Finset.univ_filter_card_eq, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma cubeOverlap_binomial_sum {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    (Fintype.card (Spin n) : ℝ)⁻¹ ^ 2 * ∑ x : Spin n, ∑ y : Spin n, f (cubeOverlap x y) =
      (2 : ℝ)⁻¹ ^ n * ∑ k ∈ Finset.range (n+1),
        (Nat.choose n k : ℝ) * f (-1 + 2 * (k : ℝ) / n) := by
  rw [cubeOverlap_average]
  simp_rw [signMean_finset hn]
  rw [(spinFinsetEquiv n).sum_comp (fun s => f (-1 + 2 * (s.card : ℝ) / n)),
    finset_card_sum n (fun k => f (-1 + 2 * (k : ℝ) / n))]
  congr 1
  simp [Spin, inv_pow]

lemma cube_pair_energy_continuous {n : ℕ} (lam : Fin n → ℝ) (x y : Spin n) :
    Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x)) +
        diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2)) := by
  have hx := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous (cubeVector x))
  have hy := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous (cubeVector y))
  exact ((hx.add hy).div_const 2).rexp

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.CubeOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter
open scoped Topology
open MeasureTheory Filter Set Real
namespace CriticalSK

lemma cubeOverlapMass_nonneg (n j : ℕ) : 0 ≤ cubeOverlapMass n j := by
  unfold cubeOverlapMass; positivity

lemma latticeOverlap_mul {n j : ℕ} (hn : 0 < n) :
    n * latticeOverlap n j = 2 * (j : ℝ) - n := by
  unfold latticeOverlap
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma binomial_exp_term {n j : ℕ} (hj : j ≤ n) (t : ℝ) :
    Real.exp (t * (2 * (j : ℝ) - n)) = Real.exp t ^ j * Real.exp (-t) ^ (n-j) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub hj]
  congr 1
  ring

lemma cubeOverlapMass_exp_bound {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) (t : ℝ) :
    cubeOverlapMass n j * Real.exp (t * n * latticeOverlap n j) ≤ Real.cosh t ^ n := by
  have hs : Real.exp t ^ j * Real.exp (-t) ^ (n-j) * (n.choose j : ℝ) ≤
      (Real.exp t + Real.exp (-t)) ^ n := by
    rw [add_pow]
    exact Finset.single_le_sum (f := fun i => Real.exp t ^ i * Real.exp (-t) ^ (n-i) * (n.choose i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (show j < n+1 by omega))
  have ht : t * n * latticeOverlap n j = t * (2 * (j : ℝ) - n) := by
    rw [mul_assoc, latticeOverlap_mul hn]
  rw [cubeOverlapMass, ht, binomial_exp_term hj t, Real.cosh_eq, div_pow]
  calc
    (2 : ℝ)⁻¹ ^ n * (n.choose j : ℝ) * (Real.exp t ^ j * Real.exp (-t) ^ (n-j)) =
        (Real.exp t ^ j * Real.exp (-t) ^ (n-j) * (n.choose j : ℝ)) / 2 ^ n := by
          rw [inv_pow]; ring
    _ ≤ (Real.exp t + Real.exp (-t)) ^ n / 2 ^ n := div_le_div_of_nonneg_right hs (by positivity)

lemma cubeOverlapMass_chernoff {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    cubeOverlapMass n j ≤ Real.exp (-(n : ℝ) * latticeOverlap n j ^ 2 / 2) := by
  set q := latticeOverlap n j
  have h := cubeOverlapMass_exp_bound hn hj q
  have hc : Real.cosh q ^ n ≤ Real.exp ((n : ℝ) * q ^ 2 / 2) := by
    calc
      Real.cosh q ^ n ≤ Real.exp (q ^ 2 / 2) ^ n :=
        pow_le_pow_left₀ (Real.cosh_pos q).le (Real.cosh_le_exp_half_sq q) n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmul : Real.exp (-(n : ℝ) * q ^ 2 / 2) * Real.exp (q * n * q) =
      Real.exp ((n : ℝ) * q ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (Real.exp_pos (q * n * q))).mp
  rw [hmul]
  exact h.trans hc

lemma log_cubic_error {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (1-q) + q + q^2/2 + q^3/3| ≤ 2*q^4 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |q| < 1 by linarith) 3
  have half : (0:ℝ) < 1-|q| := by linarith
  have hr : |q|^4/(1-|q|) ≤ 2*q^4 := by
    rw [div_le_iff₀ half, pow_abs, abs_of_nonneg (show 0 ≤ q^4 by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ 1/2-|q| by linarith) (show 0 ≤ q^4 by positivity)]
  calc
    |Real.log (1-q)+q+q^2/2+q^3/3| =
      |(∑ i ∈ range 3, q^(i+1)/(i+1)) + Real.log (1-q)| := by
        congr 1
        norm_num [sum_range_succ]
        ring
    _ ≤ _ := h
    _ ≤ _ := hr

lemma binaryEntropyRate_taylor {q : ℝ} (hq : |q| ≤ 1/2) :
    |binaryEntropyRate q-q^2/2| ≤ 4*q^4 := by
  have hqp := abs_le.mp hq
  let Ep := Real.log (1+q)-q+q^2/2-q^3/3
  let Em := Real.log (1-q)+q+q^2/2+q^3/3
  have hp : |Ep| ≤ 2*q^4 := by
    have hp0 := log_cubic_error (q := -q) (by simpa using hq)
    have heq : Real.log (1-(-q))+(-q)+(-q)^2/2+(-q)^3/3 = Ep := by dsimp [Ep]; ring_nf
    rw [heq] at hp0
    convert hp0 using 1; ring
  have hm : |Em| ≤ 2*q^4 := log_cubic_error hq
  have h1p : |1+q| ≤ 3/2 := by rw [abs_le]; constructor <;> linarith
  have h1m : |1-q| ≤ 3/2 := by rw [abs_le]; constructor <;> linarith
  have hid : binaryEntropyRate q-q^2/2 = ((1+q)*Ep+(1-q)*Em)/2 + q^4/3 := by
    unfold binaryEntropyRate Ep Em
    ring
  rw [hid]
  calc
    |((1+q)*Ep+(1-q)*Em)/2 + q^4/3| ≤
        (|1+q| *|Ep|+|1-q| *|Em|)/2 + q^4/3 := by
      calc
        _ ≤ |((1+q)*Ep+(1-q)*Em)/2| + |q^4/3| := abs_add_le _ _
        _ = |(1+q)*Ep+(1-q)*Em|/2 + q^4/3 := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (show 0 ≤ q^4/3 by positivity)]
        _ ≤ _ := by gcongr; simpa only [abs_mul] using abs_add_le ((1+q)*Ep) ((1-q)*Em)
    _ ≤ ((3/2)*(2*q^4)+(3/2)*(2*q^4))/2 + q^4/3 := by gcongr
    _ ≤ 4*q^4 := by nlinarith [show 0 ≤ q^4 by positivity]

lemma log_square_error {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (1-q^2)+q^2| ≤ 2*q^4 := by
  have hq2 : q^2 ≤ 1/4 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have h := Real.abs_log_sub_add_sum_range_le (x := q^2) (by rw [abs_of_nonneg (sq_nonneg q)]; linarith) 1
  norm_num [abs_of_nonneg (sq_nonneg q)] at h
  rw [add_comm] at h
  calc
    _ ≤ (q^2)^2/(1-q^2) := h
    _ ≤ 2*q^4 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1-q^2)]
      nlinarith [mul_nonneg (show 0 ≤ 1/2-q^2 by linarith) (show 0 ≤ q^4 by positivity)]

lemma entropy_error_tendsto {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*q n^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)*(binaryEntropyRate (q n)-q n^2/2)) atTop (𝓝 0) := by
  have hev : ∀ᶠ n in atTop, |q n| ≤ 1/2 :=
    (hq.abs).eventually (eventually_le_nhds (by norm_num : |(0:ℝ)| < 1/2))
  apply squeeze_zero_norm' _ (by simpa using hfour.const_mul 4)
  filter_upwards [hev] with n hn
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    (n:ℝ)*|binaryEntropyRate (q n)-q n^2/2| ≤ (n:ℝ)*(4*q n^4) :=
      mul_le_mul_of_nonneg_left (binaryEntropyRate_taylor hn) (Nat.cast_nonneg n)
    _ = 4*((n:ℝ)*q n^4) := by ring

lemma stirlingLogError_tendsto : Tendsto stirlingLogError atTop (𝓝 0) := by
  change Tendsto (fun n => Real.log (Stirling.stirlingSeq n) - Real.log Real.pi/2) atTop (𝓝 0)
  have h := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have hh := h.sub_const (Real.log Real.pi/2)
  simpa only [Function.comp_apply, Real.log_sqrt Real.pi_pos.le, sub_self] using hh

lemma log_factorial_stirling_exact {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = (n:ℝ)*Real.log n-n+Real.log n/2+
      Real.log (2*Real.pi)/2+stirlingLogError n := by
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
  unfold stirlingLogError
  linarith

lemma latticeOverlap_interior {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    -1 < latticeOverlap n j ∧ latticeOverlap n j < 1 := by
  have hn : (0:ℝ) < n := by exact_mod_cast (lt_trans hj hjn)
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have hjr : (j:ℝ) < n := by exact_mod_cast hjn
  unfold latticeOverlap
  constructor
  · have := div_pos (mul_pos (by norm_num : (0:ℝ) < 2) hj0) hn; linarith
  · have := (div_lt_iff₀ hn).mpr (show 2*(j:ℝ) < 2*n by linarith); linarith

lemma latticeOverlap_halves {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (j:ℝ) = n*(1+latticeOverlap n j)/2 ∧
    ((n-j:ℕ):ℝ) = n*(1-latticeOverlap n j)/2 := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  unfold latticeOverlap
  rw [Nat.cast_sub hj]
  constructor <;> field_simp <;> ring

lemma log_cubeOverlapMass_exact {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    Real.log (cubeOverlapMass n j) + Real.log n/2 +
      n*binaryEntropyRate (latticeOverlap n j) + Real.log (1-latticeOverlap n j^2)/2 =
    Real.log 2-Real.log (2*Real.pi)/2 +
      stirlingLogError n-stirlingLogError j-stirlingLogError (n-j) := by
  have hn : 0 < n := lt_trans hj hjn
  have hnj : 0 < n-j := Nat.sub_pos_of_lt hjn
  have hjp : (0:ℝ) < j := by exact_mod_cast hj
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hnjp : (0:ℝ) < (n-j:ℕ) := by exact_mod_cast hnj
  obtain ⟨hqm,hqp⟩ := latticeOverlap_interior hj hjn
  obtain ⟨hjhalf,hkhalf⟩ := latticeOverlap_halves hn hjn.le
  have hlj : Real.log (j:ℝ) = Real.log n+Real.log (1+latticeOverlap n j)-Real.log 2 := by
    conv_lhs => rw [hjhalf]
    rw [Real.log_div (mul_ne_zero hnp.ne' (by linarith)) (by norm_num), Real.log_mul hnp.ne' (by linarith)]
  have hlk : Real.log ((n-j:ℕ):ℝ) = Real.log n+Real.log (1-latticeOverlap n j)-Real.log 2 := by
    conv_lhs => rw [hkhalf]
    rw [Real.log_div (mul_ne_zero hnp.ne' (by linarith)) (by norm_num), Real.log_mul hnp.ne' (by linarith)]
  have hlq : Real.log (1-latticeOverlap n j^2) =
      Real.log (1+latticeOverlap n j)+Real.log (1-latticeOverlap n j) := by
    rw [show 1-latticeOverlap n j^2 = (1+latticeOverlap n j)*(1-latticeOverlap n j) by ring,
      Real.log_mul (by linarith) (by linarith)]
  rw [cubeOverlapMass, Real.log_mul (by positivity) (by exact_mod_cast (Nat.choose_pos hjn.le).ne'),
    Real.log_pow, Real.log_inv, Nat.cast_choose ℝ hjn.le,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    log_factorial_stirling_exact hn, log_factorial_stirling_exact hj, log_factorial_stirling_exact hnj,
    hlj, hlk, hlq]
  unfold binaryEntropyRate
  rw [hjhalf, hkhalf]
  ring

lemma cubeOverlapMass_pos {n j : ℕ} (hj : j ≤ n) : 0 < cubeOverlapMass n j := by
  unfold cubeOverlapMass
  exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos hj)

lemma cubeOverlapMass_local_limit {j : ℕ → ℕ}
    (hj : ∀ᶠ n : ℕ in atTop, j n ≤ n)
    (hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => cubeOverlapMass n (j n) * Real.sqrt n *
      Real.exp ((n:ℝ)*latticeOverlap n (j n)^2/2)) atTop
      (𝓝 (Real.exp (Real.log 2-Real.log (2*Real.pi)/2))) := by
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hqevent : ∀ᶠ n in atTop, |latticeOverlap n (j n)| < 1/2 :=
    hq.abs.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1/2))
  have hhalves : ∀ᶠ n : ℕ in atTop, (n:ℝ)/4 ≤ j n ∧ (n:ℝ)/4 ≤ (n-j n:ℕ) := by
    filter_upwards [hnpos,hj,hqevent] with n hn hjn hqn
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    obtain ⟨ha,hb⟩ := latticeOverlap_halves hn hjn
    have hab := abs_lt.mp hqn
    constructor <;> nlinarith
  have hjtop : Tendsto j atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    exact tendsto_atTop_mono' atTop (hhalves.mono fun n h => h.1)
      (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<4) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hktop : Tendsto (fun n => n-j n) atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    exact tendsto_atTop_mono' atTop (hhalves.mono fun n h => h.2)
      (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<4) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hint : ∀ᶠ n : ℕ in atTop, 0 < j n ∧ j n < n := by
    filter_upwards [hjtop.eventually_gt_atTop 0,hktop.eventually_gt_atTop 0] with n hn hk
    exact ⟨hn, Nat.sub_pos_iff_lt.mp hk⟩
  have hlq : Tendsto (fun n => Real.log (1-latticeOverlap n (j n)^2)/2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => 1-latticeOverlap n (j n)^2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (hq.pow 2)
    simpa using ((Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp ht).div_const 2
  have herr := ((stirlingLogError_tendsto.sub (stirlingLogError_tendsto.comp hjtop)).sub
    (stirlingLogError_tendsto.comp hktop)).sub (entropy_error_tendsto hq hfour)
  have hlim := (herr.const_add (Real.log 2-Real.log (2*Real.pi)/2)).sub hlq
  have hlog : Tendsto (fun n : ℕ => Real.log (cubeOverlapMass n (j n) * Real.sqrt n *
      Real.exp ((n:ℝ)*latticeOverlap n (j n)^2/2))) atTop
      (𝓝 (Real.log 2-Real.log (2*Real.pi)/2)) := by
    apply (show Tendsto (fun n : ℕ => Real.log 2-Real.log (2*Real.pi)/2 +
      ((stirlingLogError n-stirlingLogError (j n)-stirlingLogError (n-j n))-
        (n:ℝ)*(binaryEntropyRate (latticeOverlap n (j n))-latticeOverlap n (j n)^2/2))-
      Real.log (1-latticeOverlap n (j n)^2)/2) atTop _ from by simpa using hlim).congr'
    filter_upwards [hint,hnpos] with n hn hnp
    rw [Real.log_mul (mul_ne_zero (cubeOverlapMass_pos hn.2.le).ne' (by positivity)) (Real.exp_ne_zero _),
      Real.log_mul (cubeOverlapMass_pos hn.2.le).ne' (by positivity), Real.log_sqrt (by positivity), Real.log_exp]
    have h := log_cubeOverlapMass_exact hn.1 hn.2
    linarith
  apply (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr'
  filter_upwards [hj,hnpos] with n hjn hn
  dsimp only [Function.comp_apply]
  exact Real.exp_log (mul_pos (mul_pos (cubeOverlapMass_pos hjn) (by positivity)) (Real.exp_pos _))

lemma sqrt_sub_le_exp (u : ℝ) : Real.sqrt (1-u) ≤ Real.exp (-u/2) := by
  rw [Real.sqrt_le_iff]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  calc
    1-u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    _ = Real.exp (-u/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma scaledOverlapShape_nonneg (n : ℕ) (x : ℝ) : 0 ≤ scaledOverlapShape n x := by
  unfold scaledOverlapShape; positivity

lemma scaledOverlapShape_bound (n : ℕ) (x : ℝ) :
    scaledOverlapShape n x ≤ Real.exp (-(1/4 : ℝ) * x^2) := by
  unfold scaledOverlapShape
  calc
    (Real.sqrt (1-x^2/(n+6)))^(n+3) ≤ Real.exp (-(x^2/(n+6))/2)^(n+3) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_sub_le_exp _) _
    _ = Real.exp (-((n+3 : ℕ) : ℝ) * x^2 / (2*(n+6))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hp : (0 : ℝ) < 2*((n : ℝ)+6) := by positivity
      rw [div_le_iff₀ hp]
      push_cast
      nlinarith [mul_nonneg hn (sq_nonneg x)]

lemma sqrt_nat_pow {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.sqrt (a^n) = Real.sqrt a ^ n := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (pow_nonneg ha n), ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt ha]

lemma sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x/2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

lemma scaledOverlapShape_tendsto (x : ℝ) :
    Tendsto (fun n => scaledOverlapShape n x) atTop (𝓝 (Real.exp (-x^2/2))) := by
  have hinv : Tendsto (fun n : ℕ => (x^2 : ℝ)/(n+6)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 6 tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun n : ℕ => (1 : ℝ)-x^2/(n+6)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hbpos : ∀ᶠ n : ℕ in atTop, 0 < (1 : ℝ)-x^2/(n+6) := hb.eventually (eventually_gt_nhds zero_lt_one)
  have hp := (Real.tendsto_one_add_div_pow_exp (-x^2)).comp (tendsto_add_atTop_nat 6)
  have hnum : Tendsto (fun n : ℕ => Real.sqrt ((1-x^2/(n+6))^(n+6))) atTop
      (𝓝 (Real.exp (-x^2/2))) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hp using 1
    · ext n; congr 2; push_cast; ring
    · rw [sqrt_exp_half]
  have hden : Tendsto (fun n : ℕ => Real.sqrt (1-x^2/(n+6))^3) atTop (𝓝 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hb).pow 3
  have hr := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hr
  apply hr.congr'
  filter_upwards [hbpos] with n hn
  dsimp only [Pi.div_apply]
  rw [sqrt_nat_pow hn.le]
  unfold scaledOverlapShape
  have hne : Real.sqrt (1-x^2/((n : ℝ)+6)) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  rw [show n+6 = n+3+3 by omega, pow_add]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 3 hne)

lemma scaledOverlapShape_integrable (n : ℕ) : Integrable (scaledOverlapShape n) := by
  apply (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).mono' (by unfold scaledOverlapShape; fun_prop)
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (scaledOverlapShape_nonneg n x)] using scaledOverlapShape_bound n x)

lemma scaledOverlapShape_integral_tendsto :
    Tendsto (fun n => ∫ x, scaledOverlapShape n x) atTop (𝓝 (Real.sqrt (2*Real.pi))) := by
  have h := @tendsto_integral_of_dominated_convergence ℝ ℝ _ _ _ volume
    scaledOverlapShape (fun x => Real.exp (-(1/2:ℝ)*x^2)) (fun x => Real.exp (-(1/4:ℝ)*x^2))
    (fun n => (scaledOverlapShape_integrable n).aestronglyMeasurable)
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4))
    (fun n => ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (scaledOverlapShape_nonneg n x)] using scaledOverlapShape_bound n x))
    (ae_of_all _ (fun x => by convert scaledOverlapShape_tendsto x using 1; congr 2; ring))
  convert h using 1
  rw [integral_gaussian]
  congr 2
  ring

lemma scaledOverlapShape_eq (n : ℕ) (x : ℝ) :
    scaledOverlapShape n x = sphereOverlapShape (n+6) (x/Real.sqrt (n+6)) := by
  simp only [scaledOverlapShape, sphereOverlapShape, show n+6-3 = n+3 by omega,
    div_pow]
  rw [Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+6 by positivity)]

lemma overlapShape_normalizer_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt n * ∫ q : ℝ, sphereOverlapShape n q) atTop
      (𝓝 (Real.sqrt (2*Real.pi))) := by
  rw [← tendsto_add_atTop_iff_nat 6]
  convert scaledOverlapShape_integral_tendsto using 1
  ext n
  simp_rw [scaledOverlapShape_eq]
  rw [Measure.integral_comp_div, smul_eq_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  push_cast
  rfl

lemma sphereOverlapShape_pos {n : ℕ} {q : ℝ} (hq : |q| < 1) :
    0 < sphereOverlapShape n q := by
  unfold sphereOverlapShape
  apply pow_pos
  apply Real.sqrt_pos.mpr
  nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]

lemma sphereOverlapShape_log_error {n : ℕ} (hn : 3 ≤ n) {q : ℝ} (hq : |q| ≤ 1/2) :
    |Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2| ≤ (n:ℝ)*q^4+2*q^2 := by
  have hq2 : q^2 ≤ 1/4 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hnp : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnn : (0:ℝ) ≤ n-3 := by
    have : (3:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hid : Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2 =
      ((n:ℝ)-3)/2*(Real.log (1-q^2)+q^2)+3*q^2/2 := by
    rw [sphereOverlapShape, Real.log_pow, Real.log_sqrt (by linarith), Nat.cast_sub hn]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ |((n:ℝ)-3)/2| * |Real.log (1-q^2)+q^2| + 3*q^2/2 := by
      have h := abs_add_le (((n:ℝ)-3)/2*(Real.log (1-q^2)+q^2)) (3*q^2/2)
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 3*q^2/2 by positivity)] at h
      exact h
    _ = ((n:ℝ)-3)/2 * |Real.log (1-q^2)+q^2| + 3*q^2/2 := by
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ)-3)/2)]
    _ ≤ ((n:ℝ)-3)/2 * (2*q^4) + 3*q^2/2 := by gcongr; exact log_square_error hq
    _ ≤ _ := by nlinarith [show 0 ≤ q^4 by positivity, sq_nonneg q]

lemma sphereOverlapShape_local_limit {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*q n^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => sphereOverlapShape n (q n)*Real.exp ((n:ℝ)*q n^2/2))
      atTop (𝓝 1) := by
  have hev : ∀ᶠ n in atTop, |q n| ≤ 1/2 :=
    hq.abs.eventually (eventually_le_nhds (by norm_num : |(0:ℝ)| < 1/2))
  have hlog : Tendsto (fun n : ℕ => Real.log (sphereOverlapShape n (q n))+(n:ℝ)*q n^2/2)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n : ℕ => (n:ℝ)*q n^4+2*q n^2) atTop (𝓝 0) from by
      simpa using hfour.add ((hq.pow 2).const_mul 2))
    filter_upwards [hev,eventually_ge_atTop 3] with n hqn hn
    simpa only [Real.norm_eq_abs] using sphereOverlapShape_log_error hn hqn
  have he := Real.continuous_exp.continuousAt.tendsto.comp hlog
  rw [Real.exp_zero] at he
  apply he.congr'
  filter_upwards [hev] with n hn
  dsimp only [Function.comp_apply]
  rw [Real.exp_add, Real.exp_log (sphereOverlapShape_pos (lt_of_le_of_lt hn (by norm_num)))]

lemma local_overlap_constant : Real.exp (Real.log 2-Real.log (2*Real.pi)/2) *
    Real.sqrt (2*Real.pi) / 2 = 1 := by
  rw [Real.exp_sub, ← Real.log_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi),
    Real.exp_log (by norm_num : (0:ℝ)<2), Real.exp_log (by positivity)]
  field_simp

lemma local_overlap_const_pos : 0 < Real.sqrt (2*Real.pi) := by positivity

lemma cube_sphere_overlap_local_ratio {j : ℕ → ℕ}
    (hj : ∀ᶠ n : ℕ in atTop, j n ≤ n)
    (hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0))
    (hfour : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => cubeOverlapMass n (j n) /
      ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n (j n)))) atTop (𝓝 1) := by
  have hi := cubeOverlapMass_local_limit hj hq hfour
  have hs := sphereOverlapShape_local_limit hq hfour
  have hz := overlapShape_normalizer_tendsto
  have hr := (hi.mul hz).div (hs.const_mul 2) (by norm_num : (2:ℝ)*1≠0)
  simp only [mul_one, local_overlap_constant] at hr
  apply hr.congr'
  have heq : ∀ᶠ n in atTop, |latticeOverlap n (j n)| < 1 :=
    hq.abs.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1))
  have hzpos : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt n * ∫ q : ℝ, sphereOverlapShape n q :=
    hz.eventually (eventually_gt_nhds local_overlap_const_pos)
  filter_upwards [eventually_gt_atTop 0,heq,hzpos] with n hn hq hnz
  dsimp only [Pi.div_apply, Pi.mul_apply]
  unfold sphereOverlapDensity
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hS : Real.sqrt n ≠ 0 := by positivity
  have hZ : (∫ q : ℝ, sphereOverlapShape n q) ≠ 0 :=
    (mul_ne_zero_iff.mp hnz.ne').2
  have hf := (sphereOverlapShape_pos (n:=n) hq).ne'
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma latticeOverlap_center_bound {n : ℕ} (hn : 0 < n) :
    |latticeOverlap n (n/2)| ≤ 1/(n:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have ha : 2*(n/2:ℕ) ≤ n := by omega
  have hb : n ≤ 2*(n/2:ℕ)+1 := by omega
  have haR : 2*((n/2:ℕ):ℝ) ≤ n := by exact_mod_cast ha
  have hbR : (n:ℝ) ≤ 2*((n/2:ℕ):ℝ)+1 := by exact_mod_cast hb
  rw [abs_le]
  unfold latticeOverlap
  constructor
  · have h := div_le_div_of_nonneg_right (show (-1:ℝ) ≤ 2*((n/2:ℕ):ℝ)-n by linarith) hnR.le
    calc
      -(1/(n:ℝ)) = (-1)/(n:ℝ) := by ring
      _ ≤ _ := h
      _ = -1+2*((n/2:ℕ):ℝ)/(n:ℝ) := by rw [sub_div,div_self hnR.ne']; ring
  · have : 2*((n/2:ℕ):ℝ)/(n:ℝ) ≤ 1 := (div_le_iff₀ hnR).mpr (by linarith)
    have : 0 ≤ 1/(n:ℝ) := by positivity
    linarith

lemma cube_sphere_overlap_uniform {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, |latticeOverlap n j| ≤ c n →
      |cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))-1| < ε := by
  intro ε hε
  let P (n j : ℕ) : Prop := j ≤ n ∧ |latticeOverlap n j| ≤ c n ∧
    ε ≤ |cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))-1|
  classical
  let j : ℕ → ℕ := fun n => if h : ∃ j, P n j then h.choose else n/2
  have hj : ∀ n, j n ≤ n := by
    intro n
    unfold j
    split_ifs with h
    · exact h.choose_spec.1
    · exact Nat.div_le_self _ _
  have hjc : ∀ᶠ n : ℕ in atTop, |latticeOverlap n (j n)| ≤ c n := by
    filter_upwards [hcmin,eventually_gt_atTop 0] with n hcn hn
    unfold j
    split_ifs with h
    · exact h.choose_spec.2.1
    · exact (latticeOverlap_center_bound hn).trans hcn
  have hq : Tendsto (fun n => latticeOverlap n (j n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hc
    simpa only [Real.norm_eq_abs] using hjc
  have hq4 : Tendsto (fun n : ℕ => (n:ℝ)*latticeOverlap n (j n)^4) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hc4
    filter_upwards [hjc] with n hn
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_abs, abs_of_nonneg (show 0 ≤ latticeOverlap n (j n)^4 by positivity)] using pow_le_pow_left₀ (abs_nonneg _) hn 4) (Nat.cast_nonneg n)
  have hr := cube_sphere_overlap_local_ratio (Eventually.of_forall hj) hq hq4
  have he : ∀ᶠ n : ℕ in atTop,
      |cubeOverlapMass n (j n) / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n (j n)))-1| < ε := by
    have h := (hr.sub_const 1).abs
    simpa only [sub_self,abs_zero] using h.eventually (eventually_lt_nhds (by simpa using hε))
  filter_upwards [he] with n hn
  intro k hkn hkc
  by_contra hbad
  have hex : ∃ k, P n k := ⟨k,hkn,hkc,not_lt.mp hbad⟩
  have : P n (j n) := by simpa only [j,dite_eq_left hex] using hex.choose_spec
  exact (not_le_of_gt hn) this.2.2

lemma sphereOverlapShape_continuous (n : ℕ) : Continuous (sphereOverlapShape n) := by
  unfold sphereOverlapShape
  fun_prop

lemma sphereOverlapShape_nonneg (n : ℕ) (q : ℝ) : 0 ≤ sphereOverlapShape n q := by
  unfold sphereOverlapShape
  positivity

lemma sphereOverlapShape_eq_zero {n : ℕ} (hn : 4 ≤ n) {q : ℝ} (hq : 1 ≤ |q|) :
    sphereOverlapShape n q = 0 := by
  unfold sphereOverlapShape
  rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_abs q]), zero_pow (by omega : n-3≠0)]

lemma overlapShape_normalizer_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < ∫ q : ℝ, sphereOverlapShape n q := by
  apply (sphereOverlapShape_continuous n).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
  · apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1))
    intro q hq
    by_contra h
    apply hq
    exact sphereOverlapShape_eq_zero hn (by
      rw [Set.mem_Icc,not_and_or] at h
      rcases h with h | h <;> have ha := le_abs_self q <;> have hb := neg_le_abs q <;> linarith)
  · exact sphereOverlapShape_nonneg n
  · norm_num [sphereOverlapShape]

lemma sphereOverlapShape_log_variation {n : ℕ} (hn : 3 ≤ n) {q r a δ : ℝ}
    (ha : a ≤ 1/2) (hq : |q| ≤ a) (hr : |r| ≤ a) (hδ : |r-q| ≤ δ) :
    |Real.log (sphereOverlapShape n r)-Real.log (sphereOverlapShape n q)| ≤
      2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ := by
  have ha0 : 0 ≤ a := (abs_nonneg q).trans hq
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hq2 : q^2 ≤ a^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ a+|q| by positivity), sq_abs q]
  have hr2 : r^2 ≤ a^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ a+|r| by positivity), sq_abs r]
  have hq4 : q^4 ≤ a^4 := by nlinarith [sq_nonneg (a^2-q^2)]
  have hr4 : r^4 ≤ a^4 := by nlinarith [sq_nonneg (a^2-r^2)]
  have hsum : |r+q| ≤ 2*a := (abs_add_le _ _).trans (by linarith)
  have hdiff : |r^2-q^2| ≤ δ*(2*a) := by
    rw [show r^2-q^2=(r-q)*(r+q) by ring, abs_mul]
    exact mul_le_mul hδ hsum (abs_nonneg _) hd0
  have hqe := sphereOverlapShape_log_error hn (hq.trans ha)
  have hre := sphereOverlapShape_log_error hn (hr.trans ha)
  have hid : Real.log (sphereOverlapShape n r)-Real.log (sphereOverlapShape n q) =
      (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2)-
      (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)-(n:ℝ)/2*(r^2-q^2) := by ring
  rw [hid]
  calc
    _ ≤ |Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2| +
        |Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2| + |(n:ℝ)/2*(r^2-q^2)| :=
      by
        have h₁ := abs_sub (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2 - (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)) ((n:ℝ)/2*(r^2-q^2))
        have h₂ := abs_sub (Real.log (sphereOverlapShape n r)+(n:ℝ)*r^2/2) (Real.log (sphereOverlapShape n q)+(n:ℝ)*q^2/2)
        linarith
    _ ≤ ((n:ℝ)*r^4+2*r^2)+((n:ℝ)*q^4+2*q^2)+((n:ℝ)/2)*(δ*(2*a)) := by
      rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)/2)]
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hq4),
        mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hr4)]

lemma sphereOverlapDensity_variation {n : ℕ} (hn : 4 ≤ n) {q r a δ : ℝ}
    (ha : a ≤ 1/2) (hq : |q| ≤ a) (hr : |r| ≤ a) (hδ : |r-q| ≤ δ) :
    sphereOverlapDensity n q * Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ)) ≤
      sphereOverlapDensity n r := by
  have h := (abs_le.mp (sphereOverlapShape_log_variation (n:=n) (by omega) ha hq hr hδ)).1
  have hqp := sphereOverlapShape_pos (n:=n) (hq.trans_lt (ha.trans_lt (by norm_num)))
  have hrp := sphereOverlapShape_pos (n:=n) (hr.trans_lt (ha.trans_lt (by norm_num)))
  have he := Real.exp_le_exp.mpr (show Real.log (sphereOverlapShape n q)-
    (2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ) ≤ Real.log (sphereOverlapShape n r) by linarith)
  rw [Real.exp_sub,Real.exp_log hqp,Real.exp_log hrp,div_eq_mul_inv,← Real.exp_neg] at he
  unfold sphereOverlapDensity
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right he (overlapShape_normalizer_pos hn).le

lemma outwardBin_distance {δ q r : ℝ} (_hδ : 0 ≤ δ) (hr : r ∈ outwardBin δ q) :
    |r-q| ≤ δ ∧ |q| ≤ |r| := by
  unfold outwardBin outwardBinLeft at hr
  split_ifs at hr with hq hq
  · rw [Set.mem_Ioc] at hr
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_neg hq,abs_of_nonpos (by linarith : r ≤ 0)]; linarith
  · rw [Set.mem_Ioc] at hr
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_of_pos hq,abs_of_nonneg (by linarith : 0 ≤ r)]; linarith
  · have hq0 : q=0 := by linarith
    rw [Set.mem_Ioc] at hr
    constructor
    · rw [hq0,sub_zero,abs_le]; constructor <;> linarith
    · rw [hq0,abs_zero]; exact abs_nonneg _

lemma outwardBin_separated {δ q r : ℝ} (hδ : 0 < δ) (hqr : q+δ ≤ r) :
    outwardBinLeft δ q+δ ≤ outwardBinLeft δ r := by
  unfold outwardBinLeft
  split_ifs <;> linarith

lemma outwardBin_disjoint {δ q r : ℝ} (hδ : 0 < δ) (hqr : q+δ ≤ r) :
    Disjoint (outwardBin δ q) (outwardBin δ r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hb := outwardBin_separated hδ hqr
  have hx' := (show x ∈ Set.Ioc _ _ from hx).2
  have hy' := (show x ∈ Set.Ioc _ _ from hy).1
  linarith

lemma sphereOverlapDensity_nonneg (n : ℕ) (q : ℝ) : 0 ≤ sphereOverlapDensity n q := by
  exact div_nonneg (sphereOverlapShape_nonneg _ _) (integral_nonneg (sphereOverlapShape_nonneg n))

lemma sphereOverlapDensity_continuous (n : ℕ) : Continuous (sphereOverlapDensity n) :=
  (sphereOverlapShape_continuous n).div_const _

lemma sphereOverlapDensity_mul_integrable {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun q => h q*sphereOverlapDensity n q) := by
  apply (hh.mul (sphereOverlapDensity_continuous n)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  intro q hq
  by_contra hnq
  apply hq
  have : sphereOverlapShape n q = 0 := sphereOverlapShape_eq_zero hn (by
    rw [Set.mem_Icc,not_and_or] at hnq
    rcases hnq with h | h <;> have ha := le_abs_self q <;> have hb := neg_le_abs q <;> linarith)
  change h q * sphereOverlapDensity n q = 0
  rw [sphereOverlapDensity,this,zero_div,mul_zero]

lemma outwardBin_integral_const (δ q c : ℝ) (hδ : 0 ≤ δ) :
    (∫ _ : ℝ in outwardBin δ q, c) = δ*c := by
  rw [integral_const,measureReal_restrict_apply_univ,outwardBin,Real.volume_real_Ioc]
  simp only [add_sub_cancel_left,max_eq_left hδ,smul_eq_mul]

lemma outwardBin_integral_lower {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ r, 0 ≤ h r) (hm : ∀ q r, |q| ≤ |r| → h q ≤ h r)
    {a δ q : ℝ} (hδ : 0 ≤ δ) (ha : a ≤ 1/2) (hq : |q|+δ ≤ a) :
    δ*(h q*sphereOverlapDensity n q*Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ))) ≤
      ∫ r in outwardBin δ q, h r*sphereOverlapDensity n r := by
  rw [← outwardBin_integral_const δ q _ hδ]
  apply setIntegral_mono_on continuous_const.integrableOn_Ioc
    ((hc.mul (sphereOverlapDensity_continuous n)).integrableOn_Ioc) measurableSet_Ioc
  intro r hr
  obtain ⟨hd,hmr⟩ := outwardBin_distance hδ hr
  have hra : |r| ≤ a := by
    have hl : |r| ≤ |r-q|+|q| := by simpa only [sub_add_cancel] using abs_add_le (r-q) q
    linarith
  have hvar := sphereOverlapDensity_variation hn ha (show |q| ≤ a by linarith) hra hd
  calc
    _ = h q*(sphereOverlapDensity n q*Real.exp (-(2*(n:ℝ)*a^4+4*a^2+(n:ℝ)*a*δ))) := by ring
    _ ≤ h r*sphereOverlapDensity n r := mul_le_mul (hm q r hmr) hvar (mul_nonneg (sphereOverlapDensity_nonneg n q) (Real.exp_pos _).le) (h0 r)

lemma latticeOverlap_spacing {n j k : ℕ} (hn : 0 < n) (hjk : j < k) :
    latticeOverlap n j+2/(n:ℝ) ≤ latticeOverlap n k := by
  have h : (j:ℝ)+1 ≤ k := by exact_mod_cast hjk
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold latticeOverlap
  have hd := div_le_div_of_nonneg_right (show 2*(j:ℝ)+2 ≤ 2*k by linarith) hnR.le
  rw [add_div] at hd
  linarith

lemma outwardBin_lattice_disjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (fun j k : ℕ => Disjoint (outwardBin (2/(n:ℝ)) (latticeOverlap n j))
      (outwardBin (2/(n:ℝ)) (latticeOverlap n k))) := by
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact outwardBin_disjoint (by positivity) (latticeOverlap_spacing hn hjk)
  · exact (outwardBin_disjoint (by positivity) (latticeOverlap_spacing hn hkj)).symm

lemma outwardBin_sum_integral_le {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ q, 0 ≤ h q) (t : Finset ℕ) :
    (∑ j ∈ t, ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r) ≤
      ∫ r : ℝ, h r*sphereOverlapDensity n r := by
  rw [← integral_biUnion_finset t (s := fun j => outwardBin (2/(n:ℝ)) (latticeOverlap n j)) (fun _ _ => measurableSet_Ioc)
    (fun _ _ _ _ hjk => outwardBin_lattice_disjoint (n:=n) (by omega) hjk)
    (fun _ _ => (sphereOverlapDensity_mul_integrable hn hc).integrableOn)]
  apply setIntegral_le_integral (sphereOverlapDensity_mul_integrable hn hc)
  exact ae_of_all _ (fun q => mul_nonneg (h0 q) (sphereOverlapDensity_nonneg n q))

lemma central_overlap_sum_bound {n : ℕ} (hn : 4 ≤ n) {h : ℝ → ℝ} (hc : Continuous h)
    (h0 : ∀ r, 0 ≤ h r) (hm : ∀ q r, |q| ≤ |r| → h q ≤ h r)
    {a e : ℝ} (ha : a ≤ 1/2) (he : 0 ≤ e) (t : Finset ℕ)
    (ht : ∀ j ∈ t, |latticeOverlap n j|+2/(n:ℝ) ≤ a)
    (hp : ∀ j ∈ t, cubeOverlapMass n j ≤ (1+e)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j)) :
    (∑ j ∈ t, cubeOverlapMass n j*h (latticeOverlap n j)) ≤
      (1+e)*Real.exp (2*(n:ℝ)*a^4+4*a^2+2*a) * ∫ r : ℝ, h r*sphereOverlapDensity n r := by
  have hnR : (n:ℝ)≠0 := by positivity
  have hE : (n:ℝ)*a*(2/(n:ℝ))=2*a := by field_simp
  let C := (1+e)*Real.exp (2*(n:ℝ)*a^4+4*a^2+2*a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ j ∈ t, C * ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r := by
      apply Finset.sum_le_sum
      intro j hj
      have hbin := outwardBin_integral_lower hn hc h0 hm (by positivity) ha (ht j hj)
      rw [hE] at hbin
      have hi := mul_le_mul_of_nonneg_left hbin hC
      have hid : C * ((2/(n:ℝ))*(h (latticeOverlap n j)*sphereOverlapDensity n (latticeOverlap n j)*
          Real.exp (-(2*(n:ℝ)*a^4+4*a^2+2*a)))) =
          ((1+e)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j))*h (latticeOverlap n j) := by
        dsimp [C]
        rw [Real.exp_neg]
        field_simp
      rw [hid] at hi
      exact (mul_le_mul_of_nonneg_right (hp j hj) (h0 _)).trans hi
    _ = C * (∑ j ∈ t, ∫ r in outwardBin (2/(n:ℝ)) (latticeOverlap n j), h r*sphereOverlapDensity n r) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (outwardBin_sum_integral_le hn hc h0 t) hC

lemma overlap_bin_error_tendsto {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) :
    Tendsto (fun n : ℕ => 2*(n:ℝ)*(c n+2/(n:ℝ))^4+4*(c n+2/(n:ℝ))^2+
      2*(c n+2/(n:ℝ))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => c n+2/(n:ℝ)) atTop (𝓝 0) := by simpa using hc.add hd
  have hfour : Tendsto (fun n : ℕ => (n:ℝ)*(c n+2/(n:ℝ))^4) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ (show Tendsto (fun n : ℕ => 81*((n:ℝ)*c n^4)) atTop (𝓝 0) from by simpa using hc4.const_mul 81)
    filter_upwards [hcmin] with n hn
    have hc0 : 0 ≤ c n := (by positivity : 0 ≤ 1/(n:ℝ)).trans hn
    have hδ : 2/(n:ℝ) ≤ 2*c n := by
      calc
        2/(n:ℝ) = 2*(1/(n:ℝ)) := by ring
        _ ≤ 2*c n := mul_le_mul_of_nonneg_left hn (by norm_num)
    have h := pow_le_pow_left₀ (show 0 ≤ c n+2/(n:ℝ) by positivity) (show c n+2/(n:ℝ) ≤ 3*c n by linarith) 4
    have hi := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
    nlinarith
  convert ((hfour.const_mul 2).add ((ha.pow 2).const_mul 4)).add (ha.const_mul 2) using 1
  · ext n; ring
  · norm_num

lemma central_overlap_uniform_bound {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    (hc4 : Tendsto (fun n : ℕ => (n:ℝ)*c n^4) atTop (𝓝 0))
    (hcmin : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ c n) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℝ → ℝ, Continuous h → (∀ q, 0 ≤ h q) →
      (∀ q r, |q| ≤ |r| → h q ≤ h r) →
      (∑ j ∈ (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ c n),
        cubeOverlapMass n j*h (latticeOverlap n j)) ≤
          (1+ε)*∫ r : ℝ, h r*sphereOverlapDensity n r := by
  have hd : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun n : ℕ => c n+2/(n:ℝ)) atTop (𝓝 0) := by simpa using hc.add hd
  have hfac : Tendsto (fun n : ℕ => (1+ε/2)*Real.exp (2*(n:ℝ)*(c n+2/(n:ℝ))^4+
      4*(c n+2/(n:ℝ))^2+2*(c n+2/(n:ℝ)))) atTop (𝓝 (1+ε/2)) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp (overlap_bin_error_tendsto hc hc4 hcmin)).const_mul (1+ε/2)
  have hfe := hfac.eventually (eventually_le_nhds (show 1+ε/2 < 1+ε by linarith))
  have hae := ha.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2))
  have hpe := cube_sphere_overlap_uniform hc hc4 hcmin (ε/2) (by linarith)
  filter_upwards [eventually_ge_atTop 4,hfe,hae,hpe] with n hn hf ha hp
  intro h hcont h0 hmono
  classical
  let t := (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ c n)
  have hbin := central_overlap_sum_bound hn hcont h0 hmono ha (show 0 ≤ ε/2 by linarith) t
    (fun j hj => by have := (Finset.mem_filter.mp hj).2; linarith)
  have hmass : ∀ j ∈ t, cubeOverlapMass n j ≤
      (1+ε/2)*(2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j) := by
    intro j hj
    have hjR := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hjq := (Finset.mem_filter.mp hj).2
    have hq : |latticeOverlap n j| < 1 := by
      have : 0 ≤ 2/(n:ℝ) := by positivity
      linarith
    have hpos : 0 < (2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j) :=
      mul_pos (by positivity) (div_pos (sphereOverlapShape_pos hq) (overlapShape_normalizer_pos hn))
    have hh := (abs_lt.mp (hp j (by omega) hjq)).2
    have hh' : cubeOverlapMass n j / ((2/(n:ℝ))*sphereOverlapDensity n (latticeOverlap n j)) ≤ 1+ε/2 := by linarith
    simpa only [mul_assoc] using (div_le_iff₀ hpos).mp hh'
  exact (hbin hmass).trans (mul_le_mul_of_nonneg_right hf (integral_nonneg (fun q => mul_nonneg (h0 q) (sphereOverlapDensity_nonneg n q))))

lemma overlapCentralCutoff_tendsto : Tendsto overlapCentralCutoff atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/24)).comp tendsto_natCast_atTop_atTop

lemma overlapCentralCutoff_fourth :
    Tendsto (fun n : ℕ => (n:ℝ)*overlapCentralCutoff n^4) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_apply,overlapCentralCutoff]
  have hpow : ((n:ℝ)^(-(7/24:ℝ)))^4 = (n:ℝ)^(-(7/24:ℝ)*(4:ℝ)) := by
    rw [Real.rpow_mul (by positivity)]
    norm_num
  rw [hpow]
  conv_rhs => lhs; rw [← Real.rpow_one (n:ℝ)]
  rw [← Real.rpow_add (by positivity)]
  congr 1
  norm_num

lemma overlapCentralCutoff_min : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) ≤ overlapCentralCutoff n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold overlapCentralCutoff
  rw [one_div,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)

open MeasureTheory Set

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SphereSaddle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma spherePartition_pos (lam : ι → ℝ) (a r : ℝ) : 0 < spherePartition lam a r := by
  apply div_pos _ sphereArea_pos
  have hc : Continuous (fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val))) := by
    unfold diagonalEnergy
    fun_prop
  have hi : Integrable (fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val)))
      (volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  let _ : NeZero (volume : Measure (EuclideanSpace ℝ ι)).toSphere := ⟨Measure.toSphere_ne_zero _⟩
  exact integral_exp_pos hi

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.CubeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

section

lemma rotatedCubePair_haar {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (g : ℝ → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n) (hv : ‖v‖ = Real.sqrt n)
    (horth : inner ℝ u v = 0) :
    (∫ U, rotatedCubePair lam g U ∂orthogonalHaar (Fin n)) =
      (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1), (Nat.choose n j:ℝ)*
        (g (-1+2*(j:ℝ)/n)*pairMoment lam u v (-1+2*(j:ℝ)/n)) := by
  have hi (x y : Spin n) := (orthogonalHaar_integrable (cube_pair_energy_continuous lam x y)).const_mul
    (g (cubeOverlap x y))
  simp_rw [rotatedCubePair]
  rw [integral_const_mul]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  have hinner (x : Spin n) : (∫ U, ∑ y : Spin n,
      g (cubeOverlap x y)*Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
        diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2) ∂orthogonalHaar (Fin n)) =
      ∑ y : Spin n, g (cubeOverlap x y)*pairMoment lam u v (cubeOverlap x y) := by
    rw [integral_finsetSum _ (fun y _ => hi x y)]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul,pair_energy_orbit lam (cubeVector_norm x) (cubeVector_norm y) hu hv horth
      (cubeOverlap_abs_le_one x y) (cubeOverlap_gram hn x y)]
  simp_rw [hinner]
  exact cubeOverlap_binomial_sum hn (fun q => g q*pairMoment lam u v q)

lemma rotatedCubePair_lattice {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (g : ℝ → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n) (hv : ‖v‖ = Real.sqrt n)
    (horth : inner ℝ u v = 0) :
    (∫ U, rotatedCubePair lam g U ∂orthogonalHaar (Fin n)) =
      ∑ j ∈ Finset.range (n+1), cubeOverlapMass n j*
        (g (latticeOverlap n j)*pairMoment lam u v (latticeOverlap n j)) := by
  rw [rotatedCubePair_haar hn lam g hu hv horth,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cubeOverlapMass,latticeOverlap,mul_assoc]

lemma squaredPairMoment_mono_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} (huv : ‖u‖ = ‖v‖)
    {q t : ℝ} (hqt : |q| ≤ |t|) : q^2*pairMoment lam u v q ≤ t^2*pairMoment lam u v t := by
  have hsq : q^2 ≤ t^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q) hqt 2
  exact mul_le_mul hsq (pairMoment_mono_abs lam huv hqt) (pairMoment_nonneg lam u v q) (sq_nonneg t)

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK


section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[simp] lemma upperRead_upperWrite (a : UpperEntry ι → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

end Upper

open scoped BigOperators

end

open scoped BigOperators

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PartitionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma spectralStieltjes_pos (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    0 < spectralStieltjes lam r := by
  unfold spectralStieltjes
  apply mul_pos (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_pos (fun i _ => inv_pos.mpr (by linarith [le_spectralTop lam i])) Finset.univ_nonempty

lemma spectralStieltjes_strictAnti (lam : ι → ℝ) : StrictAntiOn (spectralStieltjes lam) (Ioi (spectralTop lam)) := by
  intro r hr s _ hrs
  change spectralTop lam < r at hr
  unfold spectralStieltjes
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  exact inv_strictAnti₀ (by linarith [le_spectralTop lam i] : 0 < r-lam i) (by linarith)

lemma spectralStieltjesSlope_neg (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    spectralStieltjesSlope lam r < 0 := by
  unfold spectralStieltjesSlope
  apply mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr cardinal_pos_real))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (by linarith [le_spectralTop lam i]))) Finset.univ_nonempty

lemma saddleRadius_spec (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    spectralTop lam < saddleRadius lam a ∧ spectralStieltjes lam (saddleRadius lam a) = a := by
  simpa only [saddleRadius,dite_eq_left ha] using (spectralStieltjes_exists lam ha).choose_spec

lemma saddleRadius_unique (lam : ι → ℝ) {a r : ℝ} (hr : spectralTop lam < r)
    (heq : spectralStieltjes lam r = a) : saddleRadius lam a = r := by
  have ha : 0 < a := heq ▸ spectralStieltjes_pos lam hr
  exact (spectralStieltjes_strictAnti lam).injOn (saddleRadius_spec lam ha).1 hr
    ((saddleRadius_spec lam ha).2.trans heq.symm)

lemma saddleRadius_hasStrictDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasStrictDerivAt (saddleRadius lam) (spectralStieltjesSlope lam (saddleRadius lam a))⁻¹ a := by
  obtain ⟨hr,heq⟩ := saddleRadius_spec lam ha
  have hd := spectralStieltjes_hasStrictDerivAt lam hr
  have hg : ∀ᶠ r in 𝓝 (saddleRadius lam a), saddleRadius lam (spectralStieltjes lam r) = r := by
    filter_upwards [eventually_gt_nhds hr] with r hr
    exact saddleRadius_unique lam hr rfl
  have h := hd.to_local_left_inverse (spectralStieltjesSlope_neg lam hr).ne hg
  rwa [heq] at h

lemma saddleZ_pos_gap (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a*spectralTop lam < saddleZ lam a := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · simp only [saddleZ,ite_eq_right h.ne']
    exact mul_lt_mul_of_pos_left (saddleRadius_spec lam h).1 h

lemma saddleZ_gap_pos (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    0 < saddleZ lam a-a*lam i := by
  have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
  linarith [saddleZ_pos_gap lam ha]

lemma saddleZ_reciprocal_sum (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ i, (saddleZ lam a-a*lam i)⁻¹ = Fintype.card ι := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · have heq := (saddleRadius_spec lam h).2
    unfold spectralStieltjes at heq
    have hs : ∑ i, (saddleRadius lam a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a := by
      have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
      exact (inv_mul_eq_iff_eq_mul₀ hN).mp heq
    simp only [saddleZ,ite_eq_right h.ne',← mul_sub,_root_.mul_inv_rev]
    rw [← Finset.sum_mul, hs]
    field_simp

lemma saddleObjective_min (lam : ι → ℝ) {a z : ℝ} (ha : 0 ≤ a)
    (hz : a*spectralTop lam < z) :
    saddleObjective lam a (saddleZ lam a) ≤ saddleObjective lam a z := by
  have hzpos (i : ι) : 0 < z-a*lam i := by
    have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
    linarith
  have hl (i : ι) : Real.log (z-a*lam i)-Real.log (saddleZ lam a-a*lam i) ≤
      (z-saddleZ lam a)*(saddleZ lam a-a*lam i)⁻¹ := by
    rw [← Real.log_div (hzpos i).ne' (saddleZ_gap_pos lam ha i).ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos (hzpos i) (saddleZ_gap_pos lam ha i))
    convert hh using 1
    field_simp [(saddleZ_gap_pos lam ha i).ne']
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,saddleZ_reciprocal_sum lam ha] at hs
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ by positivity)
  unfold saddleObjective
  have he : (2*(Fintype.card ι : ℝ))⁻¹ * ((z-saddleZ lam a)*(Fintype.card ι : ℝ)) =
      (z-saddleZ lam a)/2 := by field_simp
  rw [he] at hm
  linarith

lemma sphericalVariational_eq (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    sphericalVariational lam a = saddleObjective lam a (saddleZ lam a) := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨saddleZ lam a,saddleZ_pos_gap lam ha,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact saddleObjective_min lam ha hz

lemma sphericalVariational_zero (lam : ι → ℝ) : sphericalVariational lam 0 = 0 := by
  rw [sphericalVariational_eq lam (le_refl 0)]
  simp [saddleObjective,saddleZ]

lemma sphericalVariational_radius_expr (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    sphericalVariational lam a = (a*saddleRadius lam a-1)/2-Real.log a/2 -
      (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (saddleRadius lam a-lam i) := by
  rw [sphericalVariational_eq lam ha.le]
  simp only [saddleObjective,saddleZ,ite_eq_right ha.ne',← mul_sub]
  have hr := (saddleRadius_spec lam ha).1
  have he (i : ι) := Real.log_mul ha.ne' (ne_of_gt (show 0 < saddleRadius lam a-lam i by linarith [le_spectralTop lam i]))
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  field_simp
  ring

lemma sphericalVariational_hasDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (sphericalVariational lam) ((saddleRadius lam a-a⁻¹)/2) a := by
  let r := saddleRadius lam
  let d := (spectralStieltjesSlope lam (r a))⁻¹
  have hr : HasDerivAt r d a := (saddleRadius_hasStrictDerivAt lam ha).hasDerivAt
  have hpos (i : ι) : 0 < r a-lam i := by
    have hs := (saddleRadius_spec lam ha).1
    dsimp [r]
    linarith [le_spectralTop lam i]
  have hlog (i : ι) := (hr.sub_const (lam i)).log (hpos i).ne'
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hlog i)
  have hd := (((hasDerivAt_id a).mul hr).sub_const 1).div_const 2
  have hd := (hd.sub ((hasDerivAt_log ha.ne').div_const 2)).sub
    (hsum.const_mul (2*(Fintype.card ι : ℝ))⁻¹)
  have heq : ∀ᶠ b in 𝓝 a, sphericalVariational lam b =
      (b*r b-1)/2-Real.log b/2 - (2*(Fintype.card ι : ℝ))⁻¹*∑ i, Real.log (r b-lam i) := by
    filter_upwards [eventually_gt_nhds ha] with b hb
    exact sphericalVariational_radius_expr lam hb
  simp only [Pi.mul_apply, Finset.sum_apply, id_eq] at hd
  have hres := hd.congr_of_eventuallyEq heq
  have hs := (saddleRadius_spec lam ha).2
  unfold spectralStieltjes at hs
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  have hs' : ∑ i, (r a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a :=
    (inv_mul_eq_iff_eq_mul₀ hN).mp hs
  convert! hres using 1
  simp only [div_eq_mul_inv,← Finset.mul_sum,hs']
  field_simp
  ring

lemma saddleZ_weighted_identity (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (saddleZ lam a-1)*(Fintype.card ι : ℝ) =
      a*∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹ := by
  have h (i : ι) : saddleZ lam a*(saddleZ lam a-a*lam i)⁻¹ -
      a*(lam i*(saddleZ lam a-a*lam i)⁻¹) = 1 := by
    rw [← mul_assoc,← sub_mul,mul_inv_cancel₀ (saddleZ_gap_pos lam ha i).ne']
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
    saddleZ_reciprocal_sum lam ha,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
  linarith

lemma sphericalVariational_slope_bound (lam : ι → ℝ) {a C : ℝ} (ha : 0 < a)
    (hlam : ∀ i, |lam i| ≤ C) : |(saddleRadius lam a-a⁻¹)/2| ≤ C/2 := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hw := saddleZ_weighted_identity lam ha.le
  have hb : |∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹| ≤ C*(Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, |lam i*(saddleZ lam a-a*lam i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C*(saddleZ lam a-a*lam i)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_pos (inv_pos.mpr (saddleZ_gap_pos lam ha.le i))]
        exact mul_le_mul_of_nonneg_right (hlam i) (inv_pos.mpr (saddleZ_gap_pos lam ha.le i)).le
      _ = _ := by rw [← Finset.mul_sum,saddleZ_reciprocal_sum lam ha.le]
  have hwb := congrArg abs hw
  rw [abs_mul,abs_of_pos hN,abs_mul,abs_of_pos ha] at hwb
  have hzbound : |saddleZ lam a-1| ≤ a*C := by nlinarith
  have heq : (saddleRadius lam a-a⁻¹)/2 = (saddleZ lam a-1)/(2*a) := by
    simp only [saddleZ,ite_eq_right ha.ne']
    field_simp
  rw [heq,abs_div,abs_of_pos (by positivity : 0 < 2*a)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

lemma sphericalVariational_abs_le (lam : ι → ℝ) {a C : ℝ} (ha : 0 ≤ a)
    (hlam : ∀ i, |lam i| ≤ C) : |sphericalVariational lam a| ≤ a*C/2 := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have htop : spectralTop lam ≤ C := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    rw [← hi]
    exact (abs_le.mp (hlam i)).2
  have hz : a*spectralTop lam < 1+a*C := by nlinarith [mul_le_mul_of_nonneg_left htop ha]
  have hu := saddleObjective_min lam ha hz
  have hlogs : 0 ≤ ∑ i, Real.log (1+a*C-a*lam i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Real.log_nonneg
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp (hlam i)).2 ha]
  have hlo := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Real.log_le_sub_one_of_pos (saddleZ_gap_pos lam ha i))
  have hsumlow : -(C*(Fintype.card ι : ℝ)) ≤ ∑ i, lam i := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (abs_le.mp (hlam i)).1)
    simpa [Finset.sum_const,Finset.card_univ,mul_comm] using hs
  rw [sphericalVariational_eq lam ha,abs_le]
  constructor
  · unfold saddleObjective
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ← Finset.mul_sum,mul_one] at hlo
    have hl := mul_le_mul_of_nonneg_left hsumlow ha
    have hb : ∑ i, Real.log (saddleZ lam a-a*lam i) ≤
        (Fintype.card ι : ℝ)*(saddleZ lam a-1+a*C) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ by positivity)
    have he : (2*(Fintype.card ι : ℝ))⁻¹ *((Fintype.card ι : ℝ)*(saddleZ lam a-1+a*C)) =
        (saddleZ lam a-1+a*C)/2 := by field_simp
    rw [he] at hh
    linarith
  · unfold saddleObjective at hu ⊢
    have hh : 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (1+a*C-a*lam i) := mul_nonneg (by positivity) hlogs
    linarith

lemma sphericalVariational_continuousOn (lam : ι → ℝ) :
    ContinuousOn (sphericalVariational lam) (Ici 0) := by
  intro a ha
  change 0 ≤ a at ha
  rcases ha.eq_or_lt with h | h
  · subst a
    let C := Finset.univ.sup' Finset.univ_nonempty (fun i => |lam i|)
    have hC (i : ι) : |lam i| ≤ C := Finset.le_sup' (fun i => |lam i|) (Finset.mem_univ i)
    rw [ContinuousWithinAt]
    rw [sphericalVariational_zero]
    apply squeeze_zero_norm' (f := sphericalVariational lam) (a := fun a : ℝ => a*C/2)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simpa only [norm_eq_abs] using sphericalVariational_abs_le lam ha hC
    · simpa using (((continuousAt_id.mul_const C).div_const 2).tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun a : ℝ => a*C/2) (𝓝[Ici 0] 0) (𝓝 (0*C/2)))
  · exact (sphericalVariational_hasDerivAt lam h).continuousAt.continuousWithinAt

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SaddleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma saddleRadius_le_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    saddleRadius lam a ≤ r ↔ spectralStieltjes lam r ≤ a := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hs.1 hr h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hr hs.1 (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma le_saddleRadius_iff (lam : ι → ℝ) {a r : ℝ} (ha : 0 < a) (hr : spectralTop lam < r) :
    r ≤ saddleRadius lam a ↔ a ≤ spectralStieltjes lam r := by
  have hs := saddleRadius_spec lam ha
  constructor
  · intro h
    rw [← hs.2]
    exact (spectralStieltjes_strictAnti lam).antitoneOn hr hs.1 h
  · intro h
    by_contra hc
    have he := spectralStieltjes_strictAnti lam hs.1 hr (lt_of_not_ge hc)
    rw [hs.2] at he
    exact (not_lt_of_ge h) he

lemma semicircleResolvent_gt_from_inverse {s x : ℝ} (hs : 0 < s) (hx : x ≤ 1)
    (h : s*x < (1-x)^2) : x < semicircleResolvent s := by
  have hsq := Real.sq_sqrt (show 0 ≤ s*(4+s) by positivity)
  have hp : 0 < 2+s-2*x := by linarith
  have hr : Real.sqrt (s*(4+s)) < 2+s-2*x := by nlinarith
  unfold semicircleResolvent
  linarith

lemma semicircleResolvent_subcritical_margin {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/4) :
    1-u+(1/100)*Real.sqrt ((9/10)*u^2/(1-u)) <
      semicircleResolvent ((9/10)*u^2/(1-u)) := by
  have hden : 0 < 1-u := by linarith
  have hs : 0 < (9/10:ℝ)*u^2/(1-u) := by positivity
  have hpoly : ((9/10:ℝ)*u^2/(1-u))*(1-(49/50)*u) < (1-(1-(49/50)*u))^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_pos_of_pos hu,mul_nonneg (sq_nonneg u) (show 0 ≤ 1/4-u by linarith)]
  have hx := semicircleResolvent_gt_from_inverse hs (show 1-(49/50:ℝ)*u ≤ 1 by linarith) hpoly
  have hsqrt : Real.sqrt ((9/10:ℝ)*u^2/(1-u)) ≤ 2*u := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1/4-u by linarith)]
  linarith

lemma subcritical_test_scale {s₀ u : ℝ} (hs₀ : 0 ≤ s₀) (hu : 0 < u)
    (hu1 : u ≤ 1/4) (hum : 16*s₀ ≤ u^2) :
    s₀ ≤ (9/10:ℝ)*u^2/(1-u) ∧ (9/10:ℝ)*u^2/(1-u) ≤ 1 := by
  have hden : 0 < 1-u := by linarith
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith [sq_nonneg (u-1/4)]

lemma saddleRadius_subcritical_lower (lam : ι → ℝ) {s₀ u : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hu : 0 < u) (hu1 : u ≤ 1/4) (hum : 16*s₀ ≤ u^2) :
    2+(9/10)*u^2/(1-u) ≤ saddleRadius lam (1-u) := by
  have hs := subcritical_test_scale hs₀ hu hu1 hum
  have htest := hres _ hs
  have hmargin := semicircleResolvent_subcritical_margin hu hu1
  have hle : 1-u ≤ spectralStieltjes lam (2+(9/10)*u^2/(1-u)) := by
    have hh := (abs_le.mp htest).1
    linarith
  exact (le_saddleRadius_iff lam (by linarith) (by linarith)).mpr hle

lemma saddlePairDeficit_zero (lam : ι → ℝ) : saddlePairDeficit lam 0 = 0 := by
  simp [saddlePairDeficit]; ring

lemma saddlePairDeficit_hasDerivAt (lam : ι → ℝ) {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (saddlePairDeficit lam) (saddlePairSlope lam u) u := by
  have h1 := (sphericalVariational_hasDerivAt lam (show 0 < 1+u by linarith [(abs_lt.mp hu).1])).comp u
    ((hasDerivAt_const u 1).add (hasDerivAt_id u))
  have h2 := (sphericalVariational_hasDerivAt lam (show 0 < 1-u by linarith [(abs_lt.mp hu).2])).comp u
    ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
  convert! ((h1.add h2).sub_const (2*sphericalVariational lam 1)) using 1
  simp only [saddlePairSlope,zero_add,zero_sub,mul_one,mul_neg_one]
  ring

lemma saddlePairDeficit_continuousOn (lam : ι → ℝ) : ContinuousOn (saddlePairDeficit lam) (Icc 0 1) := by
  have h1 := (sphericalVariational_continuousOn lam).comp (continuous_const.add continuous_id).continuousOn
    (show MapsTo (fun q : ℝ => 1+q) (Icc 0 1) (Ici 0) by intro q hq; simp only [mem_Ici]; linarith [hq.1])
  have h2 := (sphericalVariational_continuousOn lam).comp (continuous_const.sub continuous_id).continuousOn
    (show MapsTo (fun q : ℝ => 1-q) (Icc 0 1) (Ici 0) by intro q hq; simp only [mem_Ici]; linarith [hq.2])
  exact (h1.add h2).sub continuousOn_const

lemma subcritical_coefficient {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/4) :
    (1:ℝ)/3 ≤ 1/(2*(1+u))-1/(20*(1-u)) := by
  have hP : 0 < 1+u := by linarith
  have hM : 0 < 1-u := by linarith
  have hD : 0 < 1-u^2 := by nlinarith
  have he : 1/(2*(1+u))-1/(20*(1-u)) = (9-11*u)/(20*(1-u^2)) := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1/4-u by linarith) (show 0 ≤ 7/5-u by linarith)]

lemma subcritical_short_coefficient {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/4) :
    u/(1-u^2) ≤ u+u^2/3 := by
  have hD : 0 < 1-u^2 := by nlinarith
  apply (div_le_iff₀ hD).mpr
  have hp : 0 ≤ 1-3*u-u^2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg u) hp]

lemma saddlePairSlope_small_bound (lam : ι → ℝ) {s₀ u : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hu : 0 < u) (hu1 : u ≤ 1/4) :
    saddlePairSlope lam u ≤ u-u^2/3+12*s₀ := by
  have hP : 0 < 1+u := by linarith
  have hM : 0 < 1-u := by linarith
  have hD : 0 < 1-u^2 := by nlinarith
  have hp : saddleRadius lam (1+u) ≤ 2+s₀ :=
    (saddleRadius_le_iff lam hP hedge).mpr (by linarith)
  by_cases hum : 16*s₀ ≤ u^2
  · have hm := saddleRadius_subcritical_lower lam hs₀ hedge hres hu hu1 hum
    have halg : (2+s₀-(1+u)⁻¹)/2-((2+(9/10)*u^2/(1-u))-(1-u)⁻¹)/2 =
        u-u^2*(1/(2*(1+u))-1/(20*(1-u)))+s₀/2 := by
      field_simp
      ring
    have hc := subcritical_coefficient hu.le hu1
    unfold saddlePairSlope
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg u)]
  · have hm : 2-s₀ < saddleRadius lam (1-u) := hlow.trans_lt (saddleRadius_spec lam hM).1
    have halg : (2+s₀-(1+u)⁻¹)/2-(2-s₀-(1-u)⁻¹)/2 = s₀+u/(1-u^2) := by
      field_simp
      ring
    have hc := subcritical_short_coefficient hu.le hu1
    unfold saddlePairSlope
    nlinarith

lemma saddlePairDeficit_small_bound (lam : ι → ℝ) {s₀ q : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hq : q ∈ Icc 0 (1/4)) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/9+12*s₀*q := by
  let g : ℝ → ℝ := fun u => u^2/2-u^3/9+12*s₀*u
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hdg (u : ℝ) : HasDerivAt g (u-u^2/3+12*s₀) u := by
    convert! ((((hasDerivAt_id u).pow 2).div_const 2).sub (((hasDerivAt_id u).pow 3).div_const 9)).add
      ((hasDerivAt_id u).const_mul (12*s₀)) using 1
    simp only [id_eq]
    ring
  have hD (u : ℝ) (hu : u ∈ Ioo 0 q) :
      HasDerivAt (fun u => saddlePairDeficit lam u-g u)
        (saddlePairSlope lam u-(u-u^2/3+12*s₀)) u := by
    exact (saddlePairDeficit_hasDerivAt lam (by rw [abs_of_pos hu.1]; linarith [hu.2,hq.2])).sub (hdg u)
  have hc : ContinuousOn (fun u => saddlePairDeficit lam u-g u) (Icc 0 q) :=
    ((saddlePairDeficit_continuousOn lam).mono (fun _ hu => ⟨hu.1,by linarith [hu.2,hq.2]⟩)).sub hg.continuousOn
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc 0 q) hc
    (fun u hu => (hD u (by rwa [interior_Icc] at hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Icc] at hu
      rw [(hD u hu).deriv]
      have hh := saddlePairSlope_small_bound lam hs₀ hedge hlow hres₀ hres hu.1 (by linarith [hu.2,hq.2])
      linarith)
  have hh := hmono (show (0:ℝ) ∈ Icc 0 q from ⟨le_refl 0,hq.1⟩) (show q ∈ Icc 0 q from ⟨hq.1,le_refl q⟩) hq.1
  simpa [g,saddlePairDeficit_zero] using hh

lemma saddlePairDeficit_shrinking_cubic (lam : ι → ℝ) {s₀ q : ℝ}
    (hs₀ : 0 ≤ s₀) (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hq : q ∈ Icc 0 (1/4)) (hscale : 216*s₀ ≤ q^2) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/18 := by
  have hh := saddlePairDeficit_small_bound lam hs₀ hedge hlow hres₀ hres hq
  nlinarith [mul_le_mul_of_nonneg_right hscale hq.1]

end

open Set Filter

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.OrientationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma sphericalVariational_deriv_integrable (lam : ι → ℝ) {a b C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (deriv (sphericalVariational lam)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  apply ((continuousOn_const.integrableOn_Icc (μ := volume) (a := a) (b := b) (f := fun _ : ℝ => C/2)).mono_set Ioo_subset_Icc_self).mono'
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : 0 < x := ha.trans_lt hx.1
  rw [norm_eq_abs,(sphericalVariational_hasDerivAt lam hx0).deriv]
  exact sphericalVariational_slope_bound lam hx0 hlam

lemma saddleSubcriticalError_bound (lam : ι → ℝ) {C a : ℝ} (hlam : ∀ i, |lam i| ≤ C)
    (ha : a ∈ Set.Icc 0 1) :
    |sphericalVariational lam 1-sphericalVariational lam a-(1-a^2)/4| ≤ saddleSubcriticalError lam := by
  have hpoly : IntervalIntegrable (fun x : ℝ => x/2) volume 0 1 :=
    (continuous_id.div_const 2).intervalIntegrable _ _
  have hint := (sphericalVariational_deriv_integrable lam hlam (le_refl 0) (by norm_num : (0:ℝ) ≤ 1)).sub hpoly
  have hint' := hint.mono_set (show uIcc a 1 ⊆ uIcc (0:ℝ) 1 by
    rw [uIcc_of_le ha.2,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc ha.1 (le_refl 1))
  have hc : ContinuousOn (fun x => sphericalVariational lam x-x^2/4) (Set.Icc a 1) :=
    ((sphericalVariational_continuousOn lam).mono (fun _ hx => ha.1.trans hx.1)).sub
      ((continuous_id.pow 2).div_const 4).continuousOn
  have hd (x : ℝ) (hx : x ∈ Ioo a 1) :
      HasDerivAt (fun x => sphericalVariational lam x-x^2/4)
        (deriv (sphericalVariational lam) x-x/2) x := by
    have hh := sphericalVariational_hasDerivAt lam (ha.1.trans_lt hx.1)
    convert! hh.sub (((hasDerivAt_id x).pow 2).div_const 4) using 1
    rw [hh.deriv]
    simp only [id_eq]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 hc hd hint'
  have hmono := intervalIntegral.integral_mono_interval ha.1 ha.2 (le_refl (1:ℝ))
    (Eventually.of_forall (fun x => abs_nonneg (deriv (sphericalVariational lam) x-x/2))) hint.abs
  have hh := (intervalIntegral.abs_integral_le_integral_abs (f := fun x => deriv (sphericalVariational lam) x-x/2) ha.2).trans hmono
  rw [hFTC] at hh
  convert hh using 1 <;> try rfl
  congr 1
  ring

lemma sphericalVariational_supercritical_bound (lam : ι → ℝ) {s₀ q : ℝ}
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc 0 1) :
    sphericalVariational lam (1+q)-sphericalVariational lam 1 ≤ q/2+q^2/4-q^3/12+s₀*q/2 := by
  let g : ℝ → ℝ := fun u => u/2+u^2/4-u^3/12+s₀*u/2
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hdg (u : ℝ) : HasDerivAt g ((1+u)/2-u^2/4+s₀/2) u := by
    convert! ((((hasDerivAt_id u).div_const 2).add (((hasDerivAt_id u).pow 2).div_const 4)).sub
      (((hasDerivAt_id u).pow 3).div_const 12)).add (((hasDerivAt_id u).const_mul s₀).div_const 2) using 1
    simp only [id_eq]
    ring
  have hB (u : ℝ) (hu : 0 ≤ u) : HasDerivAt (fun u => sphericalVariational lam (1+u))
      ((saddleRadius lam (1+u)-(1+u)⁻¹)/2) u := by
    simpa only [zero_add,mul_one,Function.comp_def] using
      (sphericalVariational_hasDerivAt lam (show 0 < 1+u by linarith)).comp u
        ((hasDerivAt_const u 1).add (hasDerivAt_id u))
  have hdBound (u : ℝ) (hu : u ∈ Ioo 0 q) :
      (saddleRadius lam (1+u)-(1+u)⁻¹)/2 ≤ (1+u)/2-u^2/4+s₀/2 := by
    have hP : 0 < 1+u := by linarith [hu.1]
    have hp := (saddleRadius_le_iff lam hP hedge).mpr (show spectralStieltjes lam (2+s₀) ≤ 1+u by linarith [hu.1])
    have he : (2+s₀-(1+u)⁻¹)/2 = (1+u)/2-u^2/(2*(1+u))+s₀/2 := by field_simp; ring
    have hc : u^2/4 ≤ u^2/(2*(1+u)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 1-u by linarith [hu.2,hq.2])]
    linarith
  have hc : ContinuousOn (fun u => sphericalVariational lam (1+u)-g u) (Set.Icc 0 q) := by
    apply ContinuousOn.sub _ hg.continuousOn
    exact (sphericalVariational_continuousOn lam).comp (continuous_const.add continuous_id).continuousOn
      (fun u hu => show 0 ≤ 1+u by linarith [hu.1])
  have hd (u : ℝ) (hu : u ∈ Ioo 0 q) :
      HasDerivAt (fun u => sphericalVariational lam (1+u)-g u)
        ((saddleRadius lam (1+u)-(1+u)⁻¹)/2-((1+u)/2-u^2/4+s₀/2)) u :=
    (hB u hu.1.le).sub (hdg u)
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc 0 q) hc
    (fun u hu => (hd u (by rwa [interior_Icc] at hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Icc] at hu
      rw [(hd u hu).deriv]
      linarith [hdBound u hu])
  have hh := hmono (show (0:ℝ) ∈ Set.Icc 0 q from ⟨le_refl 0,hq.1⟩) (show q ∈ Set.Icc 0 q from ⟨hq.1,le_refl q⟩) hq.1
  dsimp [g] at hh
  simp only [add_zero,zero_div,zero_pow (by omega : 2 ≠ 0),zero_pow (by omega : 3 ≠ 0),mul_zero,sub_zero] at hh
  linarith

lemma saddlePairDeficit_macro_bound (lam : ι → ℝ) {s₀ q C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc 0 1) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/12+saddleSubcriticalError lam+s₀/2 := by
  have hsub := (abs_le.mp (saddleSubcriticalError_bound lam hlam (show 1-q ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hq.1,hq.2]))).1
  have hsup := sphericalVariational_supercritical_bound lam hedge hres₀ hq
  unfold saddlePairDeficit
  nlinarith [mul_le_mul_of_nonneg_left hq.2 hs₀]

lemma saddlePairDeficit_macro_cubic (lam : ι → ℝ) {s₀ q C : ℝ}
    (hlam : ∀ i, |lam i| ≤ C) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hq : q ∈ Set.Icc (1/4) 1) (herr : saddleSubcriticalError lam+s₀/2 ≤ 1/1536) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/24 := by
  have hh := saddlePairDeficit_macro_bound lam hlam hs₀ hedge hres₀ (show q ∈ Set.Icc (0:ℝ) 1 by constructor <;> linarith [hq.1,hq.2])
  have hq3 : (1:ℝ)/64 ≤ q^3 := by
    calc (1:ℝ)/64 = (1/4)^3 := by norm_num
         _ ≤ q^3 := pow_le_pow_left₀ (by norm_num) hq.1 3
  nlinarith

end

section

open Set

variable {n : ℕ}

lemma weighted_overlap_tail_term {m j : ℕ} (hm : 0 < m) (hj : j ≤ m)
    {h D : ℝ → ℝ} {A c δ : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (htail : δ ≤ |latticeOverlap m j|)
    (hh : h (latticeOverlap m j) ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|))
    (hD : D |latticeOverlap m j| ≤ latticeOverlap m j^2/2-c*|latticeOverlap m j|^3) :
    cubeOverlapMass m j*h (latticeOverlap m j) ≤ A*Real.exp (-(m:ℝ)*c*δ^3) := by
  have hp := cubeOverlapMass_chernoff hm hj
  have hmul := (mul_le_mul_of_nonneg_left hh (cubeOverlapMass_nonneg m j)).trans
    (mul_le_mul_of_nonneg_right hp (show 0 ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|) by positivity))
  have he : Real.exp (-(m:ℝ)*latticeOverlap m j^2/2) *
      (A*Real.exp ((m:ℝ)*D |latticeOverlap m j|)) =
      A*Real.exp ((m:ℝ)*(D |latticeOverlap m j|-latticeOverlap m j^2/2)) := by
    rw [← mul_assoc,mul_comm _ A,mul_assoc,← Real.exp_add]
    congr 1
    congr 1
    ring
  rw [he] at hmul
  apply hmul.trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Real.exp_le_exp.mpr
  have hcub := pow_le_pow_left₀ hδ htail 3
  have hh0 := mul_le_mul_of_nonneg_left hcub hc
  have hh1 : D |latticeOverlap m j|-latticeOverlap m j^2/2 ≤ -c*δ^3 := by linarith
  have hh2 := mul_le_mul_of_nonneg_left hh1 (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  nlinarith

lemma weighted_overlap_tail_sum {m : ℕ} (hm : 0 < m) {h D : ℝ → ℝ} {A c δ : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hh : ∀ j ≤ m, δ < |latticeOverlap m j| →
      h (latticeOverlap m j) ≤ A*Real.exp ((m:ℝ)*D |latticeOverlap m j|))
    (hD : ∀ j ≤ m, δ < |latticeOverlap m j| →
      D |latticeOverlap m j| ≤ latticeOverlap m j^2/2-c*|latticeOverlap m j|^3) :
    (∑ j ∈ (Finset.range (m+1)).filter (fun j => ¬ |latticeOverlap m j| ≤ δ),
      cubeOverlapMass m j*h (latticeOverlap m j)) ≤ (m+1)*(A*Real.exp (-(m:ℝ)*c*δ^3)) := by
  let s := (Finset.range (m+1)).filter (fun j => ¬ |latticeOverlap m j| ≤ δ)
  have hc0 : (s.card:ℝ) ≤ m+1 := by
    have h : s.card ≤ m+1 := by
      simpa only [s,Finset.card_range] using Finset.card_filter_le (s := Finset.range (m+1)) (p := fun j => ¬ |latticeOverlap m j| ≤ δ)
    exact_mod_cast h
  have hs : ∀ j ∈ s, cubeOverlapMass m j*h (latticeOverlap m j) ≤ A*Real.exp (-(m:ℝ)*c*δ^3) := by
    intro j hj
    obtain ⟨hjm,hjt⟩ := Finset.mem_filter.mp hj
    have hjm' : j ≤ m := by have := Finset.mem_range.mp hjm; omega
    have hjt' := lt_of_not_ge hjt
    exact weighted_overlap_tail_term hm hjm' hA hc hδ hjt'.le (hh j hjm' hjt') (hD j hjm' hjt')
  have hsum := Finset.sum_le_card_nsmul s _ _ hs
  rw [nsmul_eq_mul] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_right hc0 (by positivity))

end

open Set MeasureTheory Filter

lemma latticeOverlap_abs_le {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) : |latticeOverlap n j| ≤ 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ n := by exact_mod_cast hj
  have hnon : 0 ≤ 2*(j:ℝ)/n := by positivity
  have hup : 2*(j:ℝ)/n ≤ 2 := (div_le_iff₀ hn').mpr (by linarith)
  rw [abs_le]
  unfold latticeOverlap
  constructor <;> linarith

lemma saddlePairDeficit_full_cubic {ι : Type*} [Fintype ι] [Nonempty ι] (lam : ι → ℝ)
    {s₀ δ q : ℝ} (hlam : ∀ i, |lam i| ≤ 3) (hs₀ : 0 ≤ s₀)
    (hedge : spectralTop lam < 2+s₀) (hlow : 2-s₀ ≤ spectralTop lam)
    (hres₀ : spectralStieltjes lam (2+s₀) ≤ 1)
    (hres : ∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s)
    (hδ : 0 ≤ δ) (hscale : 216*s₀ ≤ δ^2)
    (herr : saddleSubcriticalError lam+s₀/2 ≤ 1/1536) (hq : q ∈ Set.Icc δ 1) :
    saddlePairDeficit lam q ≤ q^2/2-q^3/24 := by
  have hq0 : 0 ≤ q := hδ.trans hq.1
  by_cases hsmall : q ≤ 1/4
  · have hsc : 216*s₀ ≤ q^2 := hscale.trans (pow_le_pow_left₀ hδ hq.1 2)
    have hh := saddlePairDeficit_shrinking_cubic lam hs₀ hedge hlow hres₀ hres ⟨hq0,hsmall⟩ hsc
    nlinarith [pow_nonneg hq0 3]
  · exact saddlePairDeficit_macro_cubic lam hlam hs₀ hedge hres₀ ⟨(le_of_not_ge hsmall),hq.2⟩ herr

lemma orientation_normalized_overlap_bound_oai (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
      ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
      (∀ i, |lam i| ≤ 3) → 0 < K →
      K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
      0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
      spectralStieltjes lam (2+s₀) ≤ 1 →
      (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
      216*s₀ ≤ overlapCentralCutoff n^2 →
      saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
      (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n)) /
        spherePartition lam 1 (Real.sqrt n)^2 ≤
        (1+ε)*((∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity n q) /
          spherePartition lam 1 (Real.sqrt n)^2)+
        (n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3)) := by
  have hc := central_overlap_uniform_bound overlapCentralCutoff_tendsto overlapCentralCutoff_fourth
    overlapCentralCutoff_min ε hε
  filter_upwards [hc,eventually_ge_atTop 4] with n hn hfour
  intro _ lam u v K s₀ hu hv horth hlam hK hlo hs₀ hedge hlow hres₀ hres hscale herr
  let S := spherePartition lam 1 (Real.sqrt n)
  let A := (26*Real.exp 1*n/K)^2
  let M := fun q => q^2*pairMoment lam u v q
  let δ := overlapCentralCutoff n
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpos : 0 < S := spherePartition_pos _ _ _
  have hM : Continuous M := (continuous_id.pow 2).mul (pairMoment_continuous lam u v)
  have hMpos (q) : 0 ≤ M q := mul_nonneg (sq_nonneg _) (pairMoment_nonneg lam u v q)
  have hcentral := hn M hM hMpos (fun _ _ hh => squaredPairMoment_mono_abs lam (hu.trans hv.symm) hh)
  have hdivcentral : (∑ j ∈ (Finset.range (n+1)).filter (fun j => |latticeOverlap n j| ≤ δ),
      cubeOverlapMass n j*(M (latticeOverlap n j)/S^2)) ≤
      (1+ε)*((∫ q : ℝ, M q*sphereOverlapDensity n q)/S^2) := by
    simp_rw [← mul_div_assoc,← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcentral (sq_nonneg S)
  have hpair (j : ℕ) (hj : j ≤ n) : M (latticeOverlap n j)/S^2 ≤
      A*Real.exp ((n:ℝ)*saddlePairDeficit lam |latticeOverlap n j|) := by
    have hq := latticeOverlap_abs_le (by omega : 0 < n) hj
    have hsq : latticeOverlap n j^2 ≤ 1 := by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (latticeOverlap n j)) hq 2
    have hh : M (latticeOverlap n j) ≤ pairMoment lam u v (latticeOverlap n j) := by
      dsimp only [M]
      exact mul_le_of_le_one_left (pairMoment_nonneg lam u v _) hsq
    exact (div_le_div_of_nonneg_right hh (sq_nonneg S)).trans
      (pairMoment_variational_upper_general (by omega) lam hu hv horth hlam hq hK hlo)
  have hcubic (j : ℕ) (hj : j ≤ n) (ht : δ < |latticeOverlap n j|) :
      saddlePairDeficit lam |latticeOverlap n j| ≤ latticeOverlap n j^2/2-(1/24)*|latticeOverlap n j|^3 := by
    have hh := saddlePairDeficit_full_cubic lam hlam hs₀ hedge hlow hres₀ hres hδ hscale herr
      ⟨ht.le,latticeOverlap_abs_le (by omega) hj⟩
    rw [sq_abs] at hh
    linarith
  have htail := weighted_overlap_tail_sum (h := fun q => M q/S^2) (D := saddlePairDeficit lam)
    (by omega : 0 < n) (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1/24) hδ
    (fun j hj _ => hpair j hj) hcubic
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (n+1))
    (fun j => |latticeOverlap n j| ≤ δ) (fun j => cubeOverlapMass n j*(M (latticeOverlap n j)/S^2))
  have hwhole := add_le_add hdivcentral htail
  rw [hsum] at hwhole
  simp_rw [← mul_div_assoc,← Finset.sum_div] at hwhole
  rw [← rotatedCubePair_lattice (by omega) lam (fun q => q^2) hu hv horth] at hwhole
  dsimp only [S,M,δ] at hwhole ⊢
  convert hwhole using 1 <;> first | rfl | ring1 | ring_nf

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.orientation_normalized_overlap_bound_oai := @OAI.CriticalSK.orientation_normalized_overlap_bound_oai
