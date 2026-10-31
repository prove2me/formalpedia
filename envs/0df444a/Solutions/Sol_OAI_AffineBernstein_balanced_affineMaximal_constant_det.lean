-- Prove2me | solution 1 for OAI.AffineBernstein.balanced_affineMaximal_constant_det
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:10:14.399371+00:00
-- url     : https://prove2.me/submissions/538f0021-4152-4812-b792-4bbef1189f85

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_normalized_balanced_det_bounds
import Theorems.Thm_OAI_AffineBernstein_normalized_harmonic_no_two_extremes

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
theorem matrixLinearEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (x : Space n) (i : Fin n) :
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A hA x i =
      A.mulVec x i := by
  simp [Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    EuclideanSpace.basisFun_apply, Pi.single_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.mulVec, dotProduct]

/- A convex combination allowing unused mass at the origin. -/
theorem convex_sum_mem_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (c : ι → ℝ) (v : ι → E) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, c i ≤ 1) (hv : ∀ i, v i ∈ K) : (∑ i, c i • v i) ∈ K := by
  classical
  have hn : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  by_cases hz : ∑ i, c i = 0
  · have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    simpa [hc0] using h0
  · have hp : 0 < ∑ i, c i := lt_of_le_of_ne hn (Ne.symm hz)
    have hm := hK.centerMass_mem (t := Finset.univ) (w := c) (z := v)
      (fun i _ => hc i) hp (fun i _ => hv i)
    have he := hK.smul_mem_of_zero_mem h0 hm ⟨hn, hsum⟩
    simpa [Finset.centerMass, smul_smul, hz] using he

/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
theorem symmetric_convex_sum_mem {n : ℕ} {K : Set (Space n)}
    (hK : Convex ℝ K) (h0 : (0 : Space n) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (v : Fin n → Space n)
    (hv : ∀ i, v i ∈ K) (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) :
    (∑ i, c i • v i) ∈ K := by
  classical
  let w : Fin n → Space n := fun i => if 0 ≤ c i then v i else -v i
  have hw (i : Fin n) : w i ∈ K := by
    dsimp [w]; split_ifs <;> first | exact hv i | exact hneg _ (hv i)
  have he (i : Fin n) : |c i| • w i = c i • v i := by
    dsimp [w]; split_ifs with hi
    · rw [abs_of_nonneg hi]
    · rw [abs_of_neg (lt_of_not_ge hi), neg_smul, smul_neg, neg_neg]
  simpa only [he] using convex_sum_mem_le_one hK h0 (fun i => |c i|) w
    (fun i => abs_nonneg _) hc hw

/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
theorem sum_abs_coordinate_le {n : ℕ} (x : Space n) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have he := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => |x i|)
    (fun _ => (1 : ℝ))
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul, ← Real.norm_eq_abs, ← hn, Real.sqrt_sq (norm_nonneg _),
    mul_comm] using he

/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
theorem norm_le_sqrt_card_of_coordinate_le {n : ℕ} (x : Space n)
    (hx : ∀ i, |x i| ≤ 1) : ‖x‖ ≤ Real.sqrt n := by
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  have hs : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    calc
      _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hx i
        rw [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|x i| - 1), abs_nonneg (x i)]
      _ = n := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg n)])

/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/
theorem exists_max_det_columns {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ v : Fin n → Space n, (∀ i, v i ∈ K) ∧
      (Matrix.det (fun i j => v j i) ≠ 0) ∧
      ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
        |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| := by
  classical
  let S : Set (Fin n → Space n) := {v | ∀ i, v i ∈ K}
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => hK)
  let w : Fin n → Space n := fun j => r • EuclideanSpace.single j 1
  have hw : w ∈ S := by
    intro i
    apply hball
    simp [w, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
  have hM : (fun i j => w j i) = (r : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [w, Matrix.one_apply]
  have hd : Matrix.det (fun i j => w j i) ≠ 0 := by rw [hM]; simp [hr.ne']
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn ⟨w, hw⟩
    (show Continuous (fun v : Fin n → Space n => |Matrix.det (fun i j => v j i)|) by
      fun_prop).continuousOn
  refine ⟨v, hv, ?_, fun w hw => hmax hw⟩
  intro hz
  have hh := hmax hw
  change |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| at hh
  rw [hz, abs_zero] at hh
  exact hd (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
theorem maxdet_coordinate_bound {n : ℕ} {K : Set (Space n)}
    (v : Fin n → Space n) (hv : ∀ i, v i ∈ K)
    (hd : Matrix.det (fun i j => v j i) ≠ 0)
    (hmax : ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
      |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)|) :
    ∃ q : Space n ≃ₗ[ℝ] Space n,
      (∀ x : Space n, q x = ∑ i, x i • v i) ∧
      ∀ x ∈ K, ∀ i, |q.symm x i| ≤ 1 := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => v j i
  let q : Space n ≃ₗ[ℝ] Space n :=
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis M
      (isUnit_iff_ne_zero.mpr hd)
  have hq (x : Space n) : q x = ∑ i, x i • v i := by
    ext j
    rw [show q x j = M.mulVec x j from matrixLinearEquiv_apply M _ x j]
    simp [Matrix.mulVec, dotProduct, M, mul_comm]
  refine ⟨q, hq, ?_⟩
  intro x hx j
  have hw : ∀ i, Function.update v j x i ∈ K := by
    intro i
    by_cases h : i = j
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using hv i
  have hm := hmax (Function.update v j x) hw
  have hcol : (fun i k => Function.update v j x k i) = M.updateCol j x := by
    ext i k
    simp [Matrix.updateCol, M, Function.update_apply]
    split_ifs <;> rfl
  have hsum : (fun k => ∑ i, (q.symm x i) • M k i) = (fun k => x k) := by
    funext k
    have he := congrArg (fun p : Space n => p k) (hq (q.symm x))
    simpa [M, mul_comm] using he.symm
  rw [hcol] at hm
  change |(M.updateCol j (fun k => x k)).det| ≤ |M.det| at hm
  rw [← hsum, Matrix.det_updateCol_sum, smul_eq_mul, abs_mul] at hm
  have hdpos : 0 < |M.det| := abs_pos.mpr hd
  change |q.symm x j| * |M.det| ≤ |M.det| at hm
  exact (mul_le_mul_iff_left₀ hdpos).mp (by simpa using hm)

/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
theorem symmetric_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (h0 : (0 : Space n) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 1 ⊆ A '' K ∧ A '' K ⊆ Metric.closedBall 0 n := by
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK hr hball
  obtain ⟨q, hq, hh⟩ := maxdet_coordinate_bound v hv hd hmax
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  let S := LinearEquiv.smulOfNeZero ℝ (Space n) (Real.sqrt n) hspos.ne'
  let A := (q.symm.trans S).toContinuousLinearEquiv
  have hA (x : Space n) : A x = Real.sqrt n • q.symm x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    let y : Space n := (Real.sqrt n)⁻¹ • x
    have hy : ∑ i, |y i| ≤ 1 := by
      calc
        _ ≤ Real.sqrt n * ‖y‖ := sum_abs_coordinate_le y
        _ = ‖x‖ := by simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
          hspos.ne']
        _ ≤ 1 := hxn
    have hmem : q y ∈ K := hq y ▸ symmetric_convex_sum_mem hconv h0 hneg v hv
      (fun i => y i) hy
    refine ⟨q y, hmem, ?_⟩
    rw [hA, LinearEquiv.symm_apply_apply]
    simp [y, smul_smul, hspos.ne']
  · rintro x ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos]
    calc
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left
        (norm_le_sqrt_card_of_coordinate_le _ (hh y hy)) hspos.le
      _ = n := Real.mul_self_sqrt hnpos.le

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
theorem centered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K)
    {C : ℝ} (hC : 1 ≤ C) (hbal : -K ⊆ C • K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 (2 / (C + 1)) ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * n) := by
  let D := K - K
  have hDeq : D = (fun p : Space n × Space n => p.1 - p.2) '' (K ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hDc : IsCompact D := by
    rw [hDeq]
    exact (hK.prod hK).image (continuous_fst.sub continuous_snd)
  have hDv : Convex ℝ D := hconv.sub hconv
  have hD0 : (0 : Space n) ∈ D := ⟨0, h0, 0, h0, sub_self _⟩
  have hDneg : ∀ x ∈ D, -x ∈ D := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (neg_sub _ _).symm⟩
  obtain ⟨p, hp⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  have hDb : Metric.closedBall (0 : Space n) r ⊆ D := by
    intro x hx
    have hpx : p + x ∈ K := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    exact ⟨p + x, hpx, p, interior_subset hp, by abel_nf⟩
  obtain ⟨L, hLin, hLout⟩ := symmetric_body_normalization hn hDc hDv hD0 hDneg hr hDb
  have hCp : 0 < C + 1 := by linarith
  have hscale : ∀ d ∈ D, (C + 1)⁻¹ • d ∈ K := by
    rintro d ⟨a, ha, b, hb, rfl⟩
    have hnb : -b ∈ -K := by simpa using hb
    obtain ⟨z, hz, hzb⟩ := Set.mem_smul_set.mp (hbal hnb)
    have h := hconv ha hz (inv_nonneg.mpr hCp.le)
      (div_nonneg (by linarith : 0 ≤ C) hCp.le)
      (show (C + 1)⁻¹ + C / (C + 1) = 1 by field_simp; ring)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_sub, sub_eq_add_neg, ← smul_neg, ← hzb, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) 2 (by norm_num))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = (2 : ℝ) • L x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hn : ‖x‖ ≤ 2 / (C + 1) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hy : ((C + 1) / 2) • x ∈ Metric.closedBall (0 : Space n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (C + 1) / 2)]
      have := mul_le_mul_of_nonneg_left hn (show 0 ≤ (C + 1) / 2 by positivity)
      have he : (C + 1) / 2 * (2 / (C + 1)) = 1 := by field_simp
      simpa [he] using this
    obtain ⟨d, hd, he⟩ := hLin hy
    refine ⟨(C + 1)⁻¹ • d, hscale d hd, ?_⟩
    rw [hA, map_smul, he, smul_smul, smul_smul]
    have heq : 2 * ((C + 1)⁻¹ * ((C + 1) / 2)) = 1 := by field_simp
    rw [mul_assoc, heq, one_smul]
  · rintro x ⟨y, hy, rfl⟩
    have hyd : y ∈ D := ⟨y, hy, 0, h0, sub_zero _⟩
    have hn : ‖L y‖ ≤ n := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hLout ⟨y, hyd, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith

/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
theorem contDiffAt_hessian_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => hessian u y i j) x := by
  exact (((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Determinants of the actual Hessian are smooth, by row multilinearity. -/
theorem contDiffAt_det_hessian {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : ContDiffAt ℝ ∞ (fun y => (hessian u y).det) x := by
  have hH : ContDiffAt ℝ ∞ (fun y i j => hessian u y i j) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu i j
  exact continuousDetRows.contDiff.contDiffAt.comp x hH

/-- The real determinant weight has its original exponent throughout the proof. -/
theorem contDiffAt_affineWeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineWeight u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commuting fixed-direction differentiation with evaluation of a derivative. -/
theorem dirDeriv_eq_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = fderiv ℝ (fderiv ℝ f) x v z := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const z x)
  change fderiv ℝ (fun y => fderiv ℝ f y z) x v = _
  rw [he.fderiv]
  simp

/-- Symmetry of the second derivative in fixed directions. -/
theorem dirDeriv_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = dirDeriv z (dirDeriv v f) x := by
  rw [dirDeriv_eq_second hf, dirDeriv_eq_second hf]
  exact hf.isSymmSndFDerivAt (by simp) v z

end RadialCalculus

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

theorem dirDeriv_graphAffineFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (a : Space n →L[ℝ] ℝ) (b d : ℝ) (v : Space n) :
    dirDeriv v (graphAffineFunction u a b d) x = a v + b * dirDeriv v u x := by
  unfold dirDeriv graphAffineFunction
  rw [fderiv_add_const, fderiv_fun_add a.differentiableAt (hu.const_mul b),
    fderiv_const_mul hu]
  simp

theorem hessian_graphAffineFunction {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) (i j : Fin n) :
    hessian (graphAffineFunction u a b d) x i j = b * hessian u x i j := by
  have he : dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) =ᶠ[nhds x]
      (fun y => a (coordinateVector n j) + b * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_graphAffineFunction
      ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) a b d _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (graphAffineFunction u a b d)) x
    (coordinateVector n i) = _
  rw [he.fderiv_eq, fderiv_const_add,
    fderiv_const_mul ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx))
      (coordinateVector n j)).differentiableAt (by simp))]
  rfl

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

theorem hessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : (hessian u x).IsSymm := by
  ext i j
  exact dirDeriv_comm hu (coordinateVector n j) (coordinateVector n i)

theorem matrix_trace_pair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) : (A * B).trace = ∑ i, ∑ j, A i j * B i j := by
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, A i j * B j i) = ∑ j, A i j * B i j
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB.apply j i]

/-- First derivative of composition with an affine base change. -/
theorem dirDeriv_comp_affine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (affineBaseMap B d x))
    (v : Space n) :
    dirDeriv v (fun y => u (affineBaseMap B d y)) x =
      dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B v) u (affineBaseMap B d x) := by
  have ht : HasFDerivAt (affineBaseMap B d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B) x := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).hasFDerivAt.add_const d
  change fderiv ℝ (u ∘ affineBaseMap B d) x v = _
  rw [(hu.hasFDerivAt.comp x ht).fderiv]
  rfl

/-- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
theorem hessian_comp_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) {x : Space n}
    (hx : affineBaseMap B d x ∈ Ω) :
    hessian (fun y => u (affineBaseMap B d y)) x =
      B.transpose * hessian u (affineBaseMap B d x) * B := by
  have hT : Continuous (affineBaseMap B d) := by unfold affineBaseMap; fun_prop
  have hΩ' : IsOpen (affineBaseMap B d ⁻¹' Ω) := hΩ.preimage hT
  ext i j
  have he : dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y)) =ᶠ[nhds x]
      (fun y => dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact dirDeriv_comp_affine B d ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y))) x (coordinateVector n i) =
    (B.transpose * hessian u (affineBaseMap B d x) * B) i j
  rw [he.fderiv_eq]
  change dirDeriv (coordinateVector n i) (fun y =>
    dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) x = _
  rw [dirDeriv_comp_affine B d
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp))]
  rw [dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx))]
  rw [← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n i)),
      ← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, euclideanCLM_coordinateVector, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hd : fderiv ℝ (fderiv ℝ u) (affineBaseMap B d x) (coordinateVector n l) (coordinateVector n k) =
      hessian u (affineBaseMap B d x) l k :=
    (dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx)) _ _).symm
  rw [hd]
  ring

/-- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
theorem hessian_const_mul {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => c * u y) x = c • hessian u x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => c * u z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => c * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_const_mul ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) c]
    rfl
  change fderiv ℝ _ x (coordinateVector n i) = c * _
  rw [he.fderiv_eq, fderiv_const_mul
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp)) c]
  rfl

/-- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
theorem posDef_affine_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c) :
    (c • (B.transpose * H * B)).PosDef := by
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)
  have hBt : B.conjTranspose = B.transpose := by ext i j; simp
  simpa only [hBt] using
    (hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hBu)).smul hc

/-- Exact determinant normalization used for rescaled sections. -/
theorem det_affine_congruence {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • (B.transpose * H * B)).det = (c ^ n * B.det ^ 2) * H.det := by
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
theorem trace_inverse_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c)
    (K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((c • (B.transpose * H * B))⁻¹ * (t • (B.transpose * K * B))).trace =
    (c⁻¹ * t) * (H⁻¹ * K).trace := by
  let : Invertible c := invertibleOfNonzero (ne_of_gt hc)
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBt : IsUnit B.transpose.det := by simpa using hBu
  have hPu : IsUnit (B.transpose * H * B).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hB (ne_of_gt hH.det_pos)) hB
  rw [Matrix.inv_smul _ c hPu, invOf_eq_inv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  suffices hs : (((B.transpose * H * B)⁻¹) * (B.transpose * K * B)).trace =
      (H⁻¹ * K).trace by rw [hs]; ring
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have he : (B⁻¹ * (H⁻¹ * B.transpose⁻¹)) * (B.transpose * K * B) =
      B⁻¹ * (H⁻¹ * K) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B.transpose⁻¹ B.transpose, Matrix.nonsing_inv_mul _ hBt, one_mul]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hBu, one_mul]

/-- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
theorem affineMaximalOn_iff_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) :
    AffineMaximalOn Ω u ↔ ∀ x ∈ Ω,
      ((hessian u x)⁻¹ * hessian (affineWeight u) x).trace = 0 := by
  apply forall₂_congr
  intro x hx
  have hw := hessian_isSymm (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hx)) (hpos x hx))
  rw [matrix_trace_pair _ _ hw]
  change (∑ i, ∑ j, (hessian u x).det * (hessian u x)⁻¹ i j * hessian (affineWeight u) x i j) = 0 ↔ _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact mul_eq_zero_iff_left (ne_of_gt (hpos x hx).det_pos)

theorem contDiff_affineBaseMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) :
    ContDiff ℝ ∞ (affineBaseMap B d) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).contDiff.add contDiff_const

theorem contDiffOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) :
    ContDiffOn ℝ ∞ (affineGraphPullback u B d a c e) (affineBaseMap B d ⁻¹' Ω) := by
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  exact (a.contDiff.contDiffOn.add (contDiffOn_const.mul hut)).add contDiffOn_const

theorem hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    hessian (affineGraphPullback u B d a c e) x =
      c • (B.transpose * hessian u (affineBaseMap B d x) * B) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hh : hessian (affineGraphPullback u B d a c e) x =
      c • hessian (fun y => u (affineBaseMap B d y)) x := by
    ext i j
    exact hessian_graphAffineFunction hΩ' hut hx a c e i j
  rw [hh, hessian_comp_affine hΩ hu B d hx]

theorem posDef_hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    (hessian (affineGraphPullback u B d a c e) x).PosDef := by
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx]
  exact posDef_affine_congruence (hpos _ hx) hB hc

/-- The actual determinant weight transforms by its exact positive constant. -/
theorem affineWeight_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    affineWeight (affineGraphPullback u B d a c e) x =
      Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2))) *
        affineWeight u (affineBaseMap B d x) := by
  unfold affineWeight
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx, det_affine_congruence]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_pos_of_ne_zero hB).le)
    (hpos _ hx).det_pos.le

/-- Hessians are local, including their inner derivative. -/
theorem hessian_congr_nhds {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (he : u =ᶠ[nhds x] v) : hessian u x = hessian v x := by
  ext i j
  have hd : (fun y => fderiv ℝ u y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ v y (coordinateVector n j)) :=
    he.fderiv.mono (fun _ hy => congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n j)) hy)
  exact congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n i)) hd.fderiv_eq

/-- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/
theorem affineMaximalOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    AffineMaximalOn (affineBaseMap B d ⁻¹' Ω) (affineGraphPullback u B d a c e) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hv := contDiffOn_affineGraphPullback hu B d a c e
  have hpv : ∀ x ∈ affineBaseMap B d ⁻¹' Ω,
      (hessian (affineGraphPullback u B d a c e) x).PosDef :=
    fun _ hx => posDef_hessian_affineGraphPullback hΩ hu hpos hB d a hc e hx
  apply (affineMaximalOn_iff_trace hΩ' hv hpv).mpr
  intro x hx
  let t := Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))
  have hw : ContDiffOn ℝ ∞ (affineWeight u) Ω := by
    intro y hy
    exact (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy)).contDiffWithinAt
  have hwt : ContDiffOn ℝ ∞ (fun y => affineWeight u (affineBaseMap B d y))
      (affineBaseMap B d ⁻¹' Ω) :=
    hw.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hew : affineWeight (affineGraphPullback u B d a c e) =ᶠ[nhds x]
      (fun y => t * affineWeight u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact affineWeight_affineGraphPullback hΩ hu hpos hB d a hc e hy
  rw [hessian_congr_nhds hew, hessian_const_mul hΩ' hwt t hx,
    hessian_comp_affine hΩ hw B d hx, hessian_affineGraphPullback hΩ hu B d a c e hx,
    trace_inverse_congruence (hpos _ hx) hB hc,
    (affineMaximalOn_iff_trace hΩ hu hpos).mp hmax _ hx, mul_zero]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphPatchArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricAffineArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The augmented tangent frame, with its transverse column last. -/

lemma hessian_add_constant {n : ℕ} (f : Space n → ℝ) (r : ℝ) (x : Space n) :
    hessian (fun y => f y + r) x = hessian f x := by
  ext i j
  simp only [hessian, fderiv_add_const]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformSphericalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral
open scoped Pointwise

open Filter
open scoped Topology
/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
theorem enorm_sub_le_graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ‖y - x‖ₑ ≤ graphEDist Ω u x y := by
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  apply le_iInf
  intro hγΩ
  apply le_iInf
  intro hγ0
  apply le_iInf
  intro hγ1
  have hl := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hγ (show (0 : ℝ) ≤ 1 by norm_num)
  rw [hγ1, hγ0] at hl
  apply hl.trans
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (le_add_of_nonneg_right (sq_nonneg _))

/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
theorem derivWithin_baseSegment {n : ℕ} (x v : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun s : ℝ => x + s • v) (Icc (0 : ℝ) 1) t = v := by
  have hd := ((hasDerivAt_id t).smul_const v).const_add x
  simpa using hd.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num) t ht)

/- Length estimate on a segment on which the graph height is nondecreasing. -/
theorem graphEDist_le_of_segment_deriv_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ fderiv ℝ u (x + t • (y - x)) (y - x)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hdu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (u ∘ γ) (d t) t :=
    ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hd : ContinuousOn d (Icc (0 : ℝ) 1) := by
    intro t ht
    have hc : ContinuousAt (fderiv ℝ u) (γ t) :=
      ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).fderiv_right
        (m := ∞) (by simp)).continuousAt
    have hc' : ContinuousAt (fun t => fderiv ℝ u (γ t)) t :=
      hc.comp hγ.continuous.continuousAt
    exact (hc'.clm_apply continuousAt_const).continuousWithinAt
  have hid : IntegrableOn d (Icc (0 : ℝ) 1) := hd.integrableOn_Icc
  have hic : IntegrableOn (fun _ : ℝ => ‖y - x‖) (Icc (0 : ℝ) 1) :=
    continuousOn_const.integrableOn_Icc
  have hi : IntegrableOn (fun t => ‖y - x‖ + d t) (Icc (0 : ℝ) 1) :=
    hic.add hid
  have hftc : ∫ t in Icc (0 : ℝ) 1, d t = u y - u x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hdu t (by simpa using ht))
      ((by simpa using hd : ContinuousOn d (uIcc (0 : ℝ) 1)).intervalIntegrable)
    simpa [γ, Function.comp_def] using he
  have hl : graphPathLength u γ ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖y - x‖ + d t) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0 : ℝ) 1) t = y - x from derivWithin_baseSegment x (y - x) ht]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [d, γ]
        apply Real.sqrt_le_iff.mpr
        constructor
        · exact add_nonneg (norm_nonneg _) (hp t ht)
        · nlinarith [norm_nonneg (y - x), hp t ht]
      _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, (‖y - x‖ + d t)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hi
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact add_nonneg (norm_nonneg _) (hp t ht)
      _ = _ := by
        rw [integral_add hic hid,
          setIntegral_const, hftc]
        simp
  have hdist : graphEDist Ω u x y ≤ graphPathLength u γ := by
    unfold graphEDist
    exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
      (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
        (iInf_le_of_le (by simp [γ]) le_rfl))))
  exact hdist.trans hl

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem graphEDist_le_segment_monotone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  apply (graphEDist_le_of_segment_deriv_nonneg hΩ hu x y hseg ?_).trans
  · exact ENNReal.ofReal_le_ofReal (add_le_add_right (le_abs_self _) _)
  · intro t ht
    have hd : HasDerivAt (fun t : ℝ => u (x + t • (y - x)))
        (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
      have hγ : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ
    rw [← hd.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht)]
    exact hm.derivWithin_nonneg

theorem graphEDist_le_segment_antitone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : AntitoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  have he := graphEDist_le_segment_monotone hΩ hu.neg x y hseg hm.neg
  change graphEDist Ω (-u) x y ≤ ENNReal.ofReal
    (‖y - x‖ + |(-u) y - (-u) x|) at he
  simpa only [graphEDist_neg, Pi.neg_apply, neg_sub_neg, abs_sub_comm] using he

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
theorem tendsto_of_graphEDist {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} {a : Space n}
    (ha : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun i hi => ?_⟩
  have h := (enorm_sub_le_graphEDist Ω u (x i) a).trans_lt (hN i hi)
  rw [← ofReal_norm] at h
  have h' := (ENNReal.ofReal_lt_ofReal_iff hε).mp h
  simpa [dist_eq_norm, norm_sub_rev] using h'

/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
theorem mem_of_complete_graph_cauchy {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : EuclideanGraphComplete Ω u) {x : ℕ → Space n} {a : Space n}
    (hx : ∀ i, x i ∈ Ω) (ha : Tendsto x atTop (𝓝 a))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) : a ∈ Ω := by
  obtain ⟨b, hb, hxb⟩ := hc x hx hC
  exact (tendsto_nhds_unique ha (tendsto_of_graphEDist hxb)) ▸ hb

/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
theorem graph_cauchy_of_segment_bound {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} (hx : CauchySeq x) (hu : CauchySeq (u ∘ x))
    (hbound : ∀ i j, graphEDist Ω u (x i) (x j) ≤
      ENNReal.ofReal (‖x j - x i‖ + |u (x j) - u (x i)|)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨max N M, fun i hi j hj => (hbound i j).trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have hx' : ‖x j - x i‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN j (le_trans (le_max_left _ _) hj) i
      (le_trans (le_max_left _ _) hi)
  have hu' : |u (x j) - u (x i)| < ε / 2 := by
    simpa [Function.comp_def, Real.dist_eq] using hM j
      (le_trans (le_max_right _ _) hj) i (le_trans (le_max_right _ _) hi)
  linarith

/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
theorem graphEDist_le_on_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (a v : Space n) (q : ℝ)
    (hseg : ∀ t ∈ Ico q 1, a + t • v ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1))
    {s r : ℝ} (hs : s ∈ Ico q 1) (hr : r ∈ Ico q 1) :
    graphEDist Ω u (a + s • v) (a + r • v) ≤
      ENNReal.ofReal (‖(a + r • v) - (a + s • v)‖ +
        |u (a + r • v) - u (a + s • v)|) := by
  have heq (t : ℝ) : (a + s • v) + t • ((a + r • v) - (a + s • v)) =
      a + (s + t * (r - s)) • v := by module
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : s + t * (r - s) ∈ Ico q 1 := by
    simpa [smul_eq_mul] using (convex_Ico q (1 : ℝ)).add_smul_mem hs
      (by simpa using hr) ht
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (a + s • v) + t • ((a + r • v) - (a + s • v)) ∈ Ω := by
    rw [heq]
    exact hseg _ (hmap t ht)
  rcases hm with hm | hm
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith

/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
theorem endpoint_mem_of_bounded_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hc : EuclideanGraphComplete Ω u) (a b : Space n) {q : ℝ} (hq : q < 1)
    (hseg : ∀ t ∈ Ico q 1, a + t • (b - a) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1))
    (hbdd : ∃ C : ℝ, ∀ t ∈ Ico q 1, |u (a + t • (b - a))| ≤ C) : b ∈ Ω := by
  obtain ⟨t, htm, htmem, htlim⟩ := exists_seq_strictMono_tendsto' hq
  have ht (i : ℕ) : t i ∈ Ico q 1 := ⟨(htmem i).1.le, (htmem i).2⟩
  let x : ℕ → Space n := fun i => a + t i • (b - a)
  have hx (i : ℕ) : x i ∈ Ω := hseg _ (ht i)
  have hxlim : Tendsto x atTop (𝓝 b) := by
    have he := (tendsto_const_nhds (x := a)).add (htlim.smul_const (b - a))
    simpa [x] using he
  obtain ⟨C, hC⟩ := hbdd
  have hxheight : CauchySeq (u ∘ x) := by
    rcases hm with hm | hm
    · have hmono : Monotone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddAbove (range (u ∘ x)) := by
        refine ⟨C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (le_abs_self _).trans (hC _ (ht i))
      exact (tendsto_atTop_ciSup hmono hbounded).cauchySeq
    · have hanti : Antitone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddBelow (range (u ∘ x)) := by
        refine ⟨-C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (neg_le_neg (hC _ (ht i))).trans (neg_abs_le _)
      exact (tendsto_atTop_ciInf hanti hbounded).cauchySeq
  apply mem_of_complete_graph_cauchy hc hx hxlim
  apply graph_cauchy_of_segment_bound hxlim.cauchySeq hxheight
  intro i j
  exact graphEDist_le_on_monotone_ray hΩ hu a (b - a) q hseg hm (ht i) (ht j)

/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
theorem convexOn_monotone_tail {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f t) :
    ∃ q ∈ Ico (0 : ℝ) 1, MonotoneOn f (Ico q 1) ∨ AntitoneOn f (Ico q 1) := by
  by_cases hex : ∃ q ∈ Ico (0 : ℝ) 1, 0 ≤ deriv f q
  · obtain ⟨q, hq, hqp⟩ := hex
    refine ⟨q, hq, Or.inl ?_⟩
    have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
      (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hsub (interior_subset ht))).differentiableWithinAt)
    intro t ht
    exact hqp.trans (hf.monotoneOn_deriv hd hq (hsub (interior_subset ht))
      (interior_subset ht).1)
  · refine ⟨0, by norm_num, Or.inr ?_⟩
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableWithinAt)
    intro t ht
    exact le_of_lt (lt_of_not_ge (fun h => hex ⟨t, interior_subset ht, h⟩))

/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
theorem convexOn_bounded_ray {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : DifferentiableAt ℝ f 0) {A : ℝ} (hA : ∀ t ∈ Ico (0 : ℝ) 1, f t ≤ A) :
    ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, |f t| ≤ C := by
  refine ⟨|A| + |f 0| + |deriv f 0|, ?_⟩
  intro t ht
  have hs : f 0 + t * deriv f 0 ≤ f t := by
    rcases eq_or_lt_of_le ht.1 with he | he
    · subst t
      simp
    · have h := hf.le_slope_of_hasDerivAt (by norm_num) ht he hd.hasDerivAt
      simp only [slope_def_field, sub_zero] at h
      have h' := (le_div_iff₀ he).mp h
      linarith
  have hp : -|deriv f 0| ≤ t * deriv f 0 := by
    calc
      _ ≤ t * (-|deriv f 0|) := by nlinarith [abs_nonneg (deriv f 0), ht.2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (neg_abs_le _) ht.1
  apply abs_le.mpr
  constructor
  · have h0 := neg_abs_le (f 0)
    have hAA := abs_nonneg A
    linarith
  · exact (hA t ht).trans (by linarith [le_abs_self A, abs_nonneg (f 0), abs_nonneg (deriv f 0)])

/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
theorem endpoint_mem_of_bounded_convex_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u) (a b : Space n)
    (hseg : ∀ t ∈ Ico (0 : ℝ) 1, a + t • (b - a) ∈ Ω)
    (hbounded : ∃ A : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, u (a + t • (b - a)) ≤ A) : b ∈ Ω := by
  let f : ℝ → ℝ := fun t => u (a + t • (b - a))
  have hfc : ConvexOn ℝ (Ico (0 : ℝ) 1) f := by
    have hh := (hcv.comp_affineMap (AffineMap.lineMap a b)).subset
      (s := Ico (0 : ℝ) 1) (fun t ht => ?_) (convex_Ico _ _)
    · simpa [f, Function.comp_def, AffineMap.lineMap_apply, add_comm] using hh
    · simpa [AffineMap.lineMap_apply, add_comm] using hseg t ht
  have hfd (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : DifferentiableAt ℝ f t := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
    exact (((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ).differentiableAt
  obtain ⟨A, hA⟩ := hbounded
  obtain ⟨C, hC⟩ := convexOn_bounded_ray hfc (hfd 0 (by norm_num)) hA
  obtain ⟨q, hq, hm⟩ := convexOn_monotone_tail hfc hfd
  have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
  exact endpoint_mem_of_bounded_monotone_ray hΩ hu hc a b hq.2
    (fun t ht => hseg t (hsub ht)) hm ⟨C, fun t ht => hC t (hsub ht)⟩

/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
theorem mem_of_bounded_graph_sequence {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u)
    {a : Space n} (ha : a ∈ Ω) {x : ℕ → Space n} {b : Space n}
    (hx : ∀ i, x i ∈ Ω) (hlim : Tendsto x atTop (𝓝 b))
    {A : ℝ} (hA : ∀ i, u (x i) ≤ A) : b ∈ Ω := by
  have hb : b ∈ closure Ω := mem_closure_iff_seq_limit.mpr ⟨x, hx, hlim⟩
  have hseg (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : a + t • (b - a) ∈ Ω := by
    have hh := hcv.1.combo_interior_closure_mem_interior
      (show a ∈ interior Ω by simpa [hΩ.interior_eq] using ha) hb
      (sub_pos.mpr ht.2) ht.1 (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • a + t • b = a + t • (b - a) := by module
    rw [he, hΩ.interior_eq] at hh
    exact hh
  apply endpoint_mem_of_bounded_convex_ray hΩ hu hcv hc a b hseg
  refine ⟨max (u a) A, ?_⟩
  intro t ht
  have hzlim : Tendsto (fun i => a + t • (x i - a)) atTop
      (𝓝 (a + t • (b - a))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.smul (hlim.sub tendsto_const_nhds))
  have hulim := (hu.continuousOn.continuousAt (hΩ.mem_nhds (hseg t ht))).tendsto.comp hzlim
  apply le_of_tendsto' hulim
  intro i
  have hv := hcv.2 ha (hx i) (sub_nonneg.mpr ht.2.le) ht.1
    (show (1 - t) + t = 1 by ring)
  have he : (1 - t) • a + t • x i = a + t • (x i - a) := by module
  rw [he] at hv
  calc
    _ ≤ (1 - t) * u a + t * u (x i) := hv
    _ ≤ (1 - t) * max (u a) A + t * max (u a) A :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2.le))
        (mul_le_mul_of_nonneg_left ((hA i).trans (le_max_right _ _)) ht.1)
    _ = _ := by ring

/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
theorem isClosed_epigraph_of_complete {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    IsClosed {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} := by
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  obtain ⟨a, ha⟩ := hne
  obtain ⟨A, hA⟩ := hlim.snd_nhds.bddAbove_range
  have hpΩ : p.1 ∈ Ω := mem_of_bounded_graph_sequence hΩ hu hcv hc ha
    (fun i => (hz i).1) hlim.fst_nhds (fun i => (hz i).2.trans (hA (mem_range_self i)))
  refine ⟨hpΩ, ?_⟩
  apply le_of_tendsto_of_tendsto
    ((hu.continuousOn.continuousAt (hΩ.mem_nhds hpΩ)).tendsto.comp hlim.fst_nhds) hlim.snd_nhds
  exact Eventually.of_forall fun i => (hz i).2

-- END

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCenteringFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/
/- Strict version of the second-derivative test, with specified derivatives. -/
theorem strictConvexOn_of_hasDerivWithinAt2_pos {D : Set ℝ} (hD : Convex ℝ D)
    {f f' f'' : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 < f'' x) : StrictConvexOn ℝ D f := by
  have he : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine strictConvexOn_of_deriv2_pos hD hf fun x hx => ?_
  convert hf''₀ x hx using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
  exact (hf'' _ hy).congr he (by rw [he hy])

/- The standing Hessian hypothesis gives strict convexity on every nonconstant
base segment, with the literal coordinate Hessian, not an abstract Hessian. -/
theorem strictConvexOn_segment {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {x y : Space n} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : y ≠ x) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u (x + t • (y - x))) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  exact strictConvexOn_of_hasDerivWithinAt2_pos (convex_Icc _ _) hf hdf hdd
    (fun t ht => second_fderiv_pos
      (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
      (hp _ (hseg t (interior_subset ht))) (sub_ne_zero.mpr hxy))

/- The tangent-plane height used in all source sections. -/

theorem tangentHeight_pos {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) (hxa : x ≠ a) :
    0 < tangentHeight u a x := by
  have hc := strictConvexOn_segment hΩ hcv hu hp ha hx hxa
  have hd : HasDerivAt (fun t : ℝ => u (a + t • (x - a)))
      (fderiv ℝ u a (x - a)) 0 := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (x - a)) (x - a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add a
    have hdu : HasFDerivAt u (fderiv ℝ u a) (a + (0 : ℝ) • (x - a)) := by
      simpa using ((hu.contDiffAt (hΩ.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
    exact hdu.comp_hasDerivAt 0 hγ
  have hs := hc.lt_slope_of_hasDerivAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul,
    add_sub_cancel] at hs
  exact sub_pos.mpr hs

theorem convexOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hcv : ConvexOn ℝ Ω u) (a : Space n) :
    ConvexOn ℝ Ω (tangentHeight u a) := by
  refine ⟨hcv.1, ?_⟩
  intro x hx y hy s t hs ht hst
  have he := hcv.2 hx hy hs ht hst
  have hv : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    rw [smul_sub, smul_sub]
    have heq : s • a + t • a = a := by rw [← add_smul, hst, one_smul]
    calc
      _ = s • x + t • y - (s • a + t • a) := by rw [heq]
      _ = _ := by module
  simp only [tangentHeight, hv, map_add, map_smul, smul_eq_mul]
  simp only [smul_eq_mul] at he
  have heq : s * u a + t * u a = u a := by rw [← add_mul, hst, one_mul]
  nlinarith

theorem continuousOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (a : Space n) :
    ContinuousOn (tangentHeight u a) Ω := by
  exact (hu.sub continuousOn_const).sub
    ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)).continuousOn

/- Tangent-plane sublevels are closed, by closedness of the actual epigraph.
No implicit completeness-invariance under a shear is needed. -/
theorem isClosed_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) (a : Space n) (t : ℝ) :
    IsClosed {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have he := isClosed_epigraph_of_complete hΩ hne hu hcv hc
  have hf : Continuous (fun x : Space n => (x, u a + fderiv ℝ u a (x - a) + t)) :=
    continuous_id.prodMk ((continuous_const.add
      ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
  convert he.preimage hf using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_preimage, tangentHeight]
  constructor <;> rintro ⟨hx, hh⟩ <;> exact ⟨hx, by linarith⟩

/- A finite-radius positive support gap yields a linear coercivity bound.
This replaces only the choice of constants in geometry.tex:56–67, not any
standing hypothesis or conclusion. -/
theorem tangentHeight_coercive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a : Space n} (ha : a ∈ Ω) :
    ∃ r > 0, ∃ m > 0, ∀ x ∈ Ω, r ≤ ‖x - a‖ →
      m * ‖x - a‖ ≤ r * tangentHeight u a x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ha)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrΩ : Metric.closedBall a r ⊆ Ω :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  have hct := continuousOn_tangentHeight hu.continuousOn a
  have hsΩ : Metric.sphere a r ⊆ Ω := Metric.sphere_subset_closedBall.trans hrΩ
  obtain ⟨m, hm, hmlow⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Metric.sphere a r, m ≤ tangentHeight u a x := by
    by_cases hne : (Metric.sphere a r).Nonempty
    · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere a r).exists_isMinOn hne (hct.mono hsΩ)
      refine ⟨tangentHeight u a y, tangentHeight_pos hΩ hcv hu hp ha (hsΩ hy) ?_, hmin⟩
      intro he
      subst y
      have hh : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hy
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  refine ⟨r, hr, m, hm, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x - a‖ := hr.trans_le hxr
  let q := r / ‖x - a‖
  have hq : 0 < q := div_pos hr hn
  have hq1 : q ≤ 1 := (div_le_one hn).mpr hxr
  let y := a + q • (x - a)
  have hyn : ‖y - a‖ = r := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    exact div_mul_cancel₀ r hn.ne'
  have hys : y ∈ Metric.sphere a r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hyn
  have hv : (1 - q) • a + q • x = y := by dsimp [y]; module
  have hineq := hcg.2 ha hx (sub_nonneg.mpr hq1) hq.le (show (1 - q) + q = 1 by ring)
  rw [hv, tangentHeight_self] at hineq
  simp only [smul_eq_mul, mul_zero, zero_add] at hineq
  have hmm : m ≤ r / ‖x - a‖ * tangentHeight u a x := (hmlow y hys).trans hineq
  have heq : r / ‖x - a‖ * tangentHeight u a x =
      (r * tangentHeight u a x) / ‖x - a‖ := by ring
  rw [heq] at hmm
  exact (le_div_iff₀ hn).mp hmm

/- The compact tangent sections required throughout the manuscript, proved
from PD Hessian, convexity of the open base, and intrinsic graph completeness. -/
theorem isCompact_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed := isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t
  obtain ⟨r, hr, m, hm, hbound⟩ := tangentHeight_coercive hΩ hcv hu hp ha
  apply (isCompact_closedBall a (max r (r * t / m))).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_cases hxr : r ≤ ‖x - a‖
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hm).mpr
    have hb := (hbound x hx.1 hxr).trans (mul_le_mul_of_nonneg_left hx.2 hr.le)
    simpa [mul_comm] using hb
  · exact (le_of_not_ge hxr).trans (le_max_left _ _)

theorem closure_tangentSection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    closure (tangentSection Ω u a t) = {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  apply le_antisymm
  · refine closure_minimal ?_ (isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t)
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  · intro x hx
    obtain ⟨q, hqm, hqmem, hqlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun i => a + q i • (x - a), ?_, ?_⟩
    · intro i
      have hqi : q i ∈ Ioo (0 : ℝ) 1 := hqmem i
      refine ⟨hcv.add_smul_mem ha (by simpa using hx.1) ⟨hqi.1.le, hqi.2.le⟩, ?_⟩
      have hv : (1 - q i) • a + q i • x = a + q i • (x - a) := by module
      have he := hcg.2 ha hx.1 (sub_nonneg.mpr hqi.2.le) hqi.1.le
        (show (1 - q i) + q i = 1 by ring)
      rw [hv, tangentHeight_self] at he
      simp only [smul_eq_mul, mul_zero, zero_add] at he
      exact lt_of_le_of_lt (he.trans (mul_le_mul_of_nonneg_left hx.2 hqi.1.le))
        (by nlinarith [ht, hqi.2])
    · have hh := (tendsto_const_nhds (x := a)).add (hqlim.smul_const (x - a))
      simpa using hh

/- Source equation uniform-section-balance, in unshifted coordinates;
equivalently, -ρ(closure S-a) ⊆ closure S-a. -/
theorem sectionBalance_reflection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hbal : SectionBalance Ω u ρ)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a - ρ • (x - a) ∈ Ω ∧
    tangentHeight u a (a - ρ • (x - a)) ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp only [hxa, sub_self, smul_zero, sub_zero, le_refl, and_true]
    exact ha
  · have ht := tangentHeight_pos hΩ hcv hu hp ha hx hxa
    have he := hbal a ha _ ht x (by
      rw [closure_tangentSection hΩ hcv hu hp hc ha ht]
      exact ⟨hx, le_rfl⟩)
    rwa [closure_tangentSection hΩ hcv hu hp hc ha ht] at he

/- An open set containing a point and invariant under one dilation about it
of factor greater than one is the whole vector space. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireAndDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology

lemma affineMaximal_inverseHessianTrace_zero {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hm : AffineMaximalOn Ω u)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (affineWeight u) x = 0 := by
  have hh := hm x hx
  have he : (∑ i, ∑ j, cofactorHessian u x i j * hessian (affineWeight u) x i j) =
      (hessian u x).det * inverseHessianTrace u (affineWeight u) x := by
    simp only [cofactorHessian, Matrix.smul_apply, smul_eq_mul, inverseHessianTrace,
      Finset.mul_sum, mul_assoc]
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hp.det_pos)

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EllipticComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EllipticComparison
open Filter
open scoped Topology

lemma inverseHessianTrace_add_constant {n : ℕ} {f u : Space n → ℝ} (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => f y+c) x = inverseHessianTrace u f x := by
  simp only [inverseHessianTrace,hessian_add_constant]

lemma inverseHessianTrace_sub_constant {n : ℕ} {f u : Space n → ℝ} (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => f y-c) x = inverseHessianTrace u f x := by
  simpa only [sub_eq_add_neg] using inverseHessianTrace_add_constant (f := f) (u := u) (-c) x

end EllipticComparison


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TangentShiftCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TangentShiftCalculus
open Filter
open scoped Topology

lemma affineMaximalOn_add_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f)
    (L : Space n →L[ℝ] ℝ) (c : ℝ) : AffineMaximalOn Ω (graphAffineFunction f L 1 c) := by
  have he (x : Space n) (hx : x ∈ Ω) : hessian (graphAffineFunction f L 1 c) x = hessian f x := by
    ext i j
    simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx L 1 c i j
  intro x hx
  have hw : affineWeight (graphAffineFunction f L 1 c) =ᶠ[𝓝 x] affineWeight f := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simp only [affineWeight,he y hy]
  rw [show cofactorHessian (graphAffineFunction f L 1 c) x = cofactorHessian f x by
    simp only [cofactorHessian,he x hx],hessian_congr_nhds hw]
  exact hm x hx

lemma tangentShift_eq_graphAffineFunction {n : ℕ} (f : Space n → ℝ) (a : Space n) (h : ℝ) :
    tangentShift f a h = graphAffineFunction f (-fderiv ℝ f a) 1
      (-f a + fderiv ℝ f a a - h) := by
  funext x
  simp only [tangentShift,tangentHeight,graphAffineFunction,neg_apply,map_sub,one_mul]
  ring

lemma contDiffOn_tangentShift {n : ℕ} {Ω : Set (Space n)} {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ) :
    ContDiffOn ℝ ∞ (tangentShift f a h) Ω := by
  exact ((hf.sub contDiffOn_const).sub
    ((fderiv ℝ f a).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn).sub contDiffOn_const

lemma hessian_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ)
    {x : Space n} (hx : x ∈ Ω) : hessian (tangentShift f a h) x = hessian f x := by
  rw [tangentShift_eq_graphAffineFunction]
  ext i j
  simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx (-fderiv ℝ f a) 1
    (-f a + fderiv ℝ f a a - h) i j

lemma affineMaximalOn_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f) (a : Space n) (h : ℝ) :
    AffineMaximalOn Ω (tangentShift f a h) := by
  rw [tangentShift_eq_graphAffineFunction]
  exact affineMaximalOn_add_affine hΩ hf hm _ _

lemma fderiv_tangentShift {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (a : Space n) (h : ℝ) :
    fderiv ℝ (tangentShift f a h) x = fderiv ℝ f x - fderiv ℝ f a := by
  change fderiv ℝ (fun y => f y - f a - fderiv ℝ f a (y-a) - h) x = _
  have hh := ((hf.hasFDerivAt.sub_const (f a)).sub
    ((fderiv ℝ f a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))).sub_const h
  simpa only [tangentShift,tangentHeight,Pi.sub_apply,Function.comp_apply,id_eq,
    ContinuousLinearMap.comp_id] using hh.fderiv

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireGraphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGraphComplete
open Filter
open scoped Topology

lemma graphEDist_le_segment_fderiv_bound {n : ℕ} {O : Set (Space n)}
    (f : Space n → ℝ) (x y : Space n) {M : ℝ} (hM : 0 ≤ M)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x+t • (y-x) ∈ O)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x+t • (y-x))‖ ≤ M) :
    graphEDist O f x y ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
  let γ : ℝ → Space n := fun t => x+t • (y-x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hp : graphPathLength f γ ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((1+M)*‖y-x‖) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0:ℝ) 1) t = y-x from derivWithin_baseSegment x (y-x) ht]
        apply ENNReal.ofReal_le_ofReal
        have H := (fderiv ℝ f (γ t)).le_opNorm (y-x)
        have H' : |fderiv ℝ f (γ t) (y-x)| ≤ M*‖y-x‖ := by
          simpa only [Real.norm_eq_abs] using H.trans (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity,?_⟩
        have Hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (norm_nonneg _)) |>.mpr H'
        rw [sq_abs] at Hsq
        nlinarith [mul_nonneg hM (sq_nonneg ‖y-x‖)]
      _ = _ := by simp
  apply le_trans _ hp
  unfold graphEDist
  exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
    (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
      (iInf_le_of_le (by simp [γ]) le_rfl))))

/-- An entire C∞ graph is complete for the literal induced Euclidean path
metric, not merely for the ambient chord metric. Straight segments and a
local derivative bound produce intrinsic convergence of every Cauchy sequence. -/
lemma euclideanGraphComplete_entire {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) : EuclideanGraphComplete univ f := by
  intro x _ hc
  have hcx : CauchySeq x := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun i hi j hj => ?_⟩
    have H := (enorm_sub_le_graphEDist univ f (x i) (x j)).trans_lt (hN i hi j hj)
    rw [← ofReal_norm,ENNReal.ofReal_lt_ofReal_iff hε] at H
    simpa only [dist_eq_norm,norm_sub_rev] using H
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hcx
  have hdf : ContinuousAt (fderiv ℝ f) a :=
    ((hf.contDiffAt.fderiv_right (m := ∞) (by simp))).continuousAt
  obtain ⟨δ,hδ,hδb⟩ := Metric.continuousAt_iff.mp hdf 1 zero_lt_one
  let M : ℝ := ‖fderiv ℝ f a‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbd : ∀ z ∈ Metric.ball a δ, ‖fderiv ℝ f z‖ ≤ M := by
    intro z hz
    have H := hδb hz
    have HT := norm_le_norm_add_norm_sub (fderiv ℝ f a) (fderiv ℝ f z)
    rw [dist_eq_norm] at H
    rw [norm_sub_rev] at HT
    dsimp [M]
    linarith
  refine ⟨a,mem_univ a,?_⟩
  intro ε hε
  have hp : 0 < 1+M := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ha (min δ (ε/(1+M))) (lt_min hδ (div_pos hε hp))
  refine ⟨N,fun i hi => ?_⟩
  have Hi := hN i hi
  have hib : x i ∈ Metric.ball a δ := lt_of_lt_of_le Hi (min_le_left _ _)
  have hab : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hs : ∀ t ∈ Icc (0:ℝ) 1, x i+t • (a-x i) ∈ Metric.ball a δ := by
    intro t ht
    have H := (convex_ball a δ) hib hab (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    module
  apply (graphEDist_le_segment_fderiv_bound f (x i) a hM (fun _ _ => mem_univ _) (fun t ht => hbd _ (hs t ht))).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have Hnorm : ‖a-x i‖ < ε/(1+M) := by
    simpa only [dist_eq_norm,norm_sub_rev] using lt_of_lt_of_le Hi (min_le_right _ _)
  simpa only [mul_comm] using (lt_div_iff₀ hp).mp Hnorm

end EntireGraphComplete


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedFamilyDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedFamilyDet

lemma tangentHeight_tangentShift {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (a x y : Space n) (h : ℝ) :
    tangentHeight (tangentShift v a h) x y = tangentHeight v x y := by
  simp only [tangentHeight, tangentShift, fderiv_tangentShift (hv x),
    sub_apply, map_sub]
  ring

end NormalizedFamilyDet


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearNormalizationCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearNormalizationCalculus

lemma cleMatrix_det_ne_zero {n : ℕ} (A : Space n ≃L[ℝ] Space n) : (cleMatrix A).det ≠ 0 := by
  have H : cleMatrix A * cleMatrix A.symm = 1 := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
    simp only [map_mul,map_one]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A)) *
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A.symm)) = 1
    rw [cleMatrix_apply,cleMatrix_apply]
    apply ContinuousLinearMap.ext
    intro x
    exact A.apply_symm_apply x
  have Hd : (cleMatrix A).det * (cleMatrix A.symm).det = 1 := by
    rw [← Matrix.det_mul,H,Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one Hd

lemma normalizedFunction_eq_pullback {n : ℕ} (u : Space n → ℝ)
    (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    normalizedFunction u A t = affineGraphPullback u (cleMatrix A) 0 0 t⁻¹ 0 := by
  ext y
  simp [normalizedFunction,affineGraphPullback,graphAffineFunction,affineBaseMap]

lemma contDiff_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    ContDiff ℝ ∞ (normalizedFunction u A t) := contDiff_const.mul (hu.comp A.contDiff)

lemma hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    hessian (normalizedFunction u A t) x =
      t⁻¹ • ((cleMatrix A).transpose * hessian u (A x) * cleMatrix A) := by
  rw [normalizedFunction_eq_pullback,hessian_affineGraphPullback isOpen_univ hu.contDiffOn _ _ _ _ _ (mem_univ _)]
  simp only [affineBaseMap,cleMatrix_apply,ContinuousLinearEquiv.coe_coe,add_zero]

lemma posDef_hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    (hessian (normalizedFunction u A t) x).PosDef := by
  rw [hessian_normalizedFunction hu]
  exact posDef_affine_congruence (hp _) (cleMatrix_det_ne_zero A) (inv_pos.mpr ht)

lemma affineMaximalOn_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) :
    AffineMaximalOn univ (normalizedFunction u A t) := by
  rw [normalizedFunction_eq_pullback]
  simpa only [preimage_univ] using affineMaximalOn_affineGraphPullback isOpen_univ hu.contDiffOn
    (fun x _ => hp x) hm (cleMatrix_det_ne_zero A) 0 0 (inv_pos.mpr ht) 0

lemma fderiv_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    fderiv ℝ (normalizedFunction u A t) x = t⁻¹ • ((fderiv ℝ u (A x)).comp A.toContinuousLinearMap) := by
  exact (((hu.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).const_mul t⁻¹).fderiv

lemma tangentHeight_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x y : Space n) :
    tangentHeight (normalizedFunction u A t) x y = t⁻¹ * tangentHeight u (A x) (A y) := by
  simp only [tangentHeight,fderiv_normalizedFunction hu,normalizedFunction,
    smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    map_sub,smul_eq_mul]
  ring

lemma sectionBalance_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {ρ : ℝ} (hbal : SectionBalance univ u ρ) (A : Space n ≃L[ℝ] Space n)
    {t : ℝ} (ht : 0 < t) : SectionBalance univ (normalizedFunction u A t) ρ := by
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hpv := posDef_hessian_normalizedFunction hu hp A ht
  have hcv := euclideanGraphComplete_entire hu
  have hcvv := euclideanGraphComplete_entire hv
  intro x hx s hs y hy
  rw [closure_tangentSection isOpen_univ convex_univ hv.contDiffOn (fun z _ => hpv z) hcvv hx hs] at hy ⊢
  refine ⟨mem_univ _,?_⟩
  have H := (sectionBalance_reflection isOpen_univ convex_univ hu.contDiffOn (fun z _ => hp z)
    hcv hbal (mem_univ (A x)) (mem_univ (A y))).2
  have HH : tangentHeight v x (x-ρ • (y-x)) ≤ tangentHeight v x y := by
    dsimp only [v]
    rw [tangentHeight_normalizedFunction hu,tangentHeight_normalizedFunction hu]
    simp only [map_sub,map_smul]
    exact mul_le_mul_of_nonneg_left H (inv_nonneg.mpr ht.le)
  exact HH.trans hy.2

end LinearNormalizationCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SectionNormalizationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SectionNormalizationFamily
open scoped Pointwise
open Filter
open scoped Topology

/-- The actual uniform, zero-preserving section normalizations in rigidity.tex.
The radius is fixed before height; the maps are produced from the compact
convex sections and their genuine balance inclusion. -/
theorem centered_section_normalization_family {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : ℝ, 0 < t → ∃ A : Space n ≃L[ℝ] Space n,
      Metric.ball 0 1 ⊆ tangentSection univ (normalizedFunction u A t) 0 1 ∧
      tangentSection univ (normalizedFunction u A t) 0 1 ⊆ Metric.ball 0 R := by
  let C := ρ⁻¹
  have hC : 1 ≤ C := (one_le_inv₀ hρ).mpr hρ1
  have hCp : 0 < C+1 := by linarith
  let R : ℝ := 2*(n:ℝ)*(C+1)+1
  have hR : 1 ≤ R := by
    have H : 0 ≤ 2*(n:ℝ)*(C+1) := by positivity
    dsimp [R]
    linarith
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hu.contDiffOn
    (fun x _ => (hp x).posSemidef)
  have hc := euclideanGraphComplete_entire hu
  have hg (x : Space n) : tangentHeight u 0 x = u x := by simp [tangentHeight,hzero,hdzero]
  refine ⟨R,hR,?_⟩
  intro t ht
  let K := closure (tangentSection univ u 0 t)
  have hKeq : K = {x | u x ≤ t} := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    simp only [mem_univ,true_and,hg]
  have hK : IsCompact K := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    exact isCompact_tangent_sublevel isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) t
  have hKcv : Convex ℝ K := by
    rw [hKeq]
    simpa only [mem_univ,true_and] using hcv.convex_le t
  have hK0 : (0:Space n) ∈ K := by rw [hKeq]; simpa only [mem_ofPred_eq,hzero] using ht.le
  have hKi : (interior K).Nonempty := by
    refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hopen : IsOpen {x | u x < t} := isOpen_lt hu.continuous continuous_const
    have hn := hopen.mem_nhds (show (0:Space n) ∈ {x | u x < t} by
      simpa only [mem_ofPred_eq,hzero] using ht)
    apply mem_of_superset hn
    intro x hx
    rw [hKeq]
    exact (show u x < t from hx).le
  have hKb : -K ⊆ C • K := by
    intro z hz
    have hz' : -z ∈ K := by simpa using hz
    have H := hbal 0 (mem_univ _) t ht (-z) hz'
    have Hz : ρ • z ∈ K := by simpa only [zero_sub,sub_zero,smul_neg,neg_neg] using H
    exact Set.mem_smul_set.mpr ⟨ρ • z,Hz,by simp [C,smul_smul,hρ.ne']⟩
  obtain ⟨L,hLin,hLout⟩ := centered_body_normalization hn hK hKcv hKi hK0 hC hKb
  let s : ℝ := (C+1)⁻¹
  have hs : 0 < s := inv_pos.mpr hCp
  let S : Space n ≃L[ℝ] Space n := (LinearEquiv.smulOfNeZero ℝ (Space n) s hs.ne').toContinuousLinearEquiv
  let A := S.trans L.symm
  have hLA (y : Space n) : L (A y) = s • y := by simp [A,S]
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hv0 : v 0=0 := by simp [v,normalizedFunction,hzero]
  have hdv0 : fderiv ℝ v 0=0 := by simp [v,fderiv_normalizedFunction hu,hdzero]
  have hgv (y : Space n) : tangentHeight v 0 y = v y := by simp [tangentHeight,hv0,hdv0]
  refine ⟨A,?_,?_⟩
  · intro y hy
    have hyn : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
    have hzin : L ((2:ℝ) • A y) ∈ Metric.closedBall (0:Space n) (2/(C+1)) := by
      rw [Metric.mem_closedBall,dist_zero_right,map_smul,hLA,smul_smul,norm_smul,
        Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) hs)]
      calc
        _ ≤ (2*s)*1 := mul_le_mul_of_nonneg_left hyn (by positivity)
        _ = 2/(C+1) := by simp [s,div_eq_mul_inv]
    obtain ⟨z,hz,hze⟩ := hLin hzin
    have hzk : (2:ℝ) • A y ∈ K := L.injective hze ▸ hz
    have hzu : u ((2:ℝ) • A y) ≤ t := by rwa [hKeq] at hzk
    have hconv := hcv.2 (mem_univ 0) (mem_univ ((2:ℝ) • A y))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
    have huAy : u (A y) ≤ t/2 := by
      simp only [smul_zero,zero_add,smul_smul,show (1:ℝ)/2*2=1 by norm_num,one_smul,
        hzero,smul_eq_mul,mul_zero,zero_add] at hconv
      linarith
    refine ⟨mem_univ y,?_⟩
    change tangentHeight v 0 y < 1
    rw [hgv]
    change t⁻¹*u (A y)<1
    have H := mul_le_mul_of_nonneg_left huAy (inv_nonneg.mpr ht.le)
    have He : t⁻¹*(t/2)=(1:ℝ)/2 := by field_simp
    rw [He] at H
    linarith
  · intro y hy
    have hyv : v y < 1 := by
      have H : tangentHeight v 0 y < 1 := hy.2
      rwa [hgv] at H
    have hyu : u (A y)<t := by
      change t⁻¹*u (A y)<1 at hyv
      rw [mul_comm,← div_eq_mul_inv] at hyv
      exact (div_lt_iff₀ ht).mp hyv |>.trans_eq (one_mul t)
    have hyK : A y ∈ K := by rw [hKeq]; exact hyu.le
    have HL := hLout ⟨A y,hyK,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,hLA,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at HL
    have HLy : ‖y‖ ≤ 2*(n:ℝ)*(C+1) := by
      have H := mul_le_mul_of_nonneg_right HL hCp.le
      have He : s*‖y‖*(C+1)=‖y‖ := by dsimp [s]; field_simp
      rwa [He] at H
    rw [Metric.mem_ball,dist_zero_right]
    dsimp [R]
    linarith

end SectionNormalizationFamily


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearizedNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearizedNormalization

lemma inverseHessianTrace_eq_matrixTrace {n : ℕ} {u s : Space n → ℝ}
    (hs : ContDiff ℝ ∞ s) (x : Space n) :
    inverseHessianTrace u s x = ((hessian u x)⁻¹*hessian s x).trace := by
  symm
  exact matrix_trace_pair _ _ (hessian_isSymm hs.contDiffAt)

lemma contDiff_comp_cle {n : ℕ} {s : Space n → ℝ} (hs : ContDiff ℝ ∞ s)
    (A : Space n ≃L[ℝ] Space n) : ContDiff ℝ ∞ (fun x => s (A x)) :=
  hs.comp A.contDiff

lemma hessian_comp_cle {n : ℕ} {s : Space n → ℝ} (hs : ContDiff ℝ ∞ s)
    (A : Space n ≃L[ℝ] Space n) (x : Space n) :
    hessian (fun y => s (A y)) x = (cleMatrix A).transpose*hessian s (A x)*cleMatrix A := by
  have H := hessian_comp_affine isOpen_univ hs.contDiffOn (cleMatrix A) 0 (x := x) (mem_univ _)
  simpa only [affineBaseMap,cleMatrix_apply,ContinuousLinearEquiv.coe_coe,add_zero] using H

lemma inverseHessianTrace_normalized_comp {n : ℕ} {u s : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hs : ContDiff ℝ ∞ s) (hp : ∀ x, (hessian u x).PosDef)
    (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    inverseHessianTrace (normalizedFunction u A t) (fun y => s (A y)) x =
      t*inverseHessianTrace u s (A x) := by
  rw [inverseHessianTrace_eq_matrixTrace (contDiff_comp_cle hs A),
    inverseHessianTrace_eq_matrixTrace hs,hessian_normalizedFunction hu,hessian_comp_cle hs]
  have H := trace_inverse_congruence (hp (A x)) (cleMatrix_det_ne_zero A) (inv_pos.mpr ht)
    (hessian s (A x)) 1
  simpa only [one_smul,inv_inv,mul_one] using H

/-- The previously produced normalizations can put any finite collection
of fixed original points in the same small inner ball. -/
theorem centered_normalization_at_points {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ P : Finset (Space n),
      ∃ t : ℝ, 0 < t ∧ ∃ A : Space n ≃L[ℝ] Space n,
        BalancedNormalized ρ R (normalizedFunction u A t) ∧
        ∀ x ∈ P, A.symm x ∈ Metric.ball (0:Space n) (1/64:ℝ) := by
  obtain ⟨R,hR,H⟩ := centered_section_normalization_family hn hu hp hzero hdzero hρ hρ1 hbal
  refine ⟨R,hR,?_⟩
  intro P
  let t : ℝ := 1 + ∑ x ∈ P, |u ((64*R) • x)|
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A,hin,hout⟩ := H t ht
  have hv0 : normalizedFunction u A t 0=0 := by simp [normalizedFunction,hzero]
  have hdz : fderiv ℝ (normalizedFunction u A t) 0=0 := by
    rw [fderiv_normalizedFunction hu]
    simp only [map_zero,hdzero,ContinuousLinearMap.zero_comp,smul_zero]
  refine ⟨t,ht,A,⟨contDiff_normalizedFunction hu A t,posDef_hessian_normalizedFunction hu hp A ht,
    affineMaximalOn_normalizedFunction hu hp hm A ht,hv0,hdz,
    sectionBalance_normalizedFunction hu hp hbal A ht,hin,hout⟩,?_⟩
  intro x hx
  have hxu : u ((64*R) • x) < t := by
    have HH := Finset.single_le_sum (fun point _ => abs_nonneg (u ((64*R) • point))) hx
    dsimp [t]
    linarith [le_abs_self (u ((64*R) • x))]
  have hsec : (64*R) • (A.symm x) ∈ tangentSection univ (normalizedFunction u A t) 0 1 := by
    refine ⟨mem_univ _,?_⟩
    rw [tangentHeight_normalizedFunction hu]
    simp only [map_zero,map_smul,ContinuousLinearEquiv.apply_symm_apply,tangentHeight,hzero,hdzero,
      sub_zero,zero_apply,smul_zero]
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_lt_one ht).mpr hxu
  have hnorm := hout hsec
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0 < 64*R by linarith)] at hnorm
  rw [Metric.mem_ball,dist_zero_right]
  have hRp : 0 < R := by linarith
  nlinarith

end LinearizedNormalization


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BoundedHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section BoundedHarmonic

/-- Bounded harmonic Liouville for the genuine inverse-Hessian operator of
an entire balanced affine-maximal graph. No CG/TW theorem is assumed. -/
theorem centered_balanced_bounded_harmonic_constant {n : ℕ} (hn : 1 ≤ n)
    {u F : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ)
    (hF : ContDiff ℝ ∞ F) (hFb : BddBelow (range F)) (hFa : BddAbove (range F))
    (hLF : ∀ x, inverseHessianTrace u F x=0) : ∀ x y, F x=F y := by
  classical
  let m := sInf (range F)
  let M := sSup (range F)
  have hbounds (x : Space n) : m ≤ F x ∧ F x ≤ M :=
    ⟨csInf_le hFb ⟨x,rfl⟩,le_csSup hFa ⟨x,rfl⟩⟩
  have hne : (range F).Nonempty := ⟨F 0,⟨0,rfl⟩⟩
  have hMm : m ≤ M := (hbounds 0).1.trans (hbounds 0).2
  suffices he : M=m by intro x y; linarith [(hbounds x).1,(hbounds x).2,(hbounds y).1,(hbounds y).2]
  by_contra hneM
  have hd : 0 < M-m := sub_pos.mpr (lt_of_le_of_ne hMm (Ne.symm hneM))
  obtain ⟨R,hR,Hnorm⟩ := centered_normalization_at_points hn hu hp hm hzero hdzero hρ hρ1 hbal
  obtain ⟨ε,hε,Hε⟩ := normalized_harmonic_no_two_extremes hn hρ hρ1 hR hd
  obtain ⟨fa,⟨a,rfl⟩,ha⟩ := exists_lt_of_csInf_lt hne (show m < m + ε by linarith)
  obtain ⟨fb,⟨b,rfl⟩,hb⟩ := exists_lt_of_lt_csSup hne (show M - ε < M by linarith)
  obtain ⟨t,ht,A,hv,Hpts⟩ := Hnorm {a,b}
  let G := fun x => F (A x)-m
  have hG : ContDiff ℝ ∞ G := (contDiff_comp_cle hF A).sub contDiff_const
  have hGr (x : Space n) : 0 ≤ G x ∧ G x ≤ M-m := by
    dsimp [G]
    constructor <;> linarith [(hbounds (A x)).1,(hbounds (A x)).2]
  have hLG (x : Space n) : inverseHessianTrace (normalizedFunction u A t) G x=0 := by
    rw [show G=(fun y => F (A y)-m) from rfl,inverseHessianTrace_sub_constant,
      inverseHessianTrace_normalized_comp hu hF hp A ht,hLF,mul_zero]
  exact Hε (normalizedFunction u A t) hv G hG hGr hLG
    (A.symm a) (Hpts a (by simp)) (A.symm b) (Hpts b (by simp))
    (by simp only [G,ContinuousLinearEquiv.apply_symm_apply]; constructor <;> linarith)

end BoundedHarmonic


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GlobalDetRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GlobalDetRatio

lemma det_hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    (hessian (normalizedFunction u A t) x).det =
      (t⁻¹)^n * (cleMatrix A).det^2 * (hessian u (A x)).det := by
  rw [hessian_normalizedFunction hu,det_affine_congruence]

/-- Genuine global determinant-ratio bounds follow from the uniform balanced
section normalizations. This is a consequence of the original PDE, rather
than a global determinant assumption. It does not imply individual Hessian
bounds. -/
theorem centered_balanced_global_det_ratio {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hu0 : u 0=0) (hdu0 : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Space n,
      c * (hessian u 0).det ≤ (hessian u x).det ∧
      (hessian u x).det ≤ C * (hessian u 0).det := by
  obtain ⟨R,hR,Hfam⟩ := centered_section_normalization_family hn hu hp hu0 hdu0 hρ hρ1 hbal
  obtain ⟨c,C,hc,hC,Hb⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  refine ⟨c/C,C/c,div_pos hc hC,div_pos hC hc,?_⟩
  intro x
  let t := max 1 (u ((16*R) • x))+1
  have ht : 0 < t := by dsimp [t]; have := le_max_left 1 (u ((16*R) • x)); linarith
  have htx : u ((16*R) • x)<t := by
    dsimp [t]
    have := le_max_right 1 (u ((16*R) • x))
    linarith
  obtain ⟨A,hin,hout⟩ := Hfam t ht
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hpv := posDef_hessian_normalizedFunction hu hp A ht
  have hvm := affineMaximalOn_normalizedFunction hu hp hm A ht
  have hv0 : v 0=0 := by simp [v,normalizedFunction,hu0]
  have hdv0 : fderiv ℝ v 0=0 := by simp [v,fderiv_normalizedFunction hu,hdu0]
  have hbalv := sectionBalance_normalizedFunction hu hp hbal A ht
  have hysection : (16*R) • A.symm x ∈ tangentSection univ v 0 1 := by
    refine ⟨mem_univ _,?_⟩
    simp only [tangentHeight,hv0,hdv0,sub_zero,zero_apply]
    change t⁻¹*u (A ((16*R) • A.symm x)) < 1
    rw [map_smul,A.apply_symm_apply,mul_comm,← div_eq_mul_inv]
    exact (div_lt_one ht).mpr htx
  have hyr := mem_ball_zero_iff.mp (hout hysection)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 16*R)] at hyr
  have hy : A.symm x ∈ Metric.ball (0:Space n) (1/8:ℝ) := by
    rw [mem_ball_zero_iff]
    nlinarith
  have H := Hb v hv hpv hvm hv0 hdv0 hbalv hin hout
  have H0 := H 0 (by simp : (0:Space n) ∈ Metric.ball 0 (1/8:ℝ))
  have Hx := H (A.symm x) hy
  dsimp only [v] at H0 Hx
  rw [det_hessian_normalizedFunction hu, map_zero] at H0
  rw [det_hessian_normalizedFunction hu, A.apply_symm_apply] at Hx
  let q := (t⁻¹)^n * (cleMatrix A).det^2
  have hq : 0 < q := mul_pos (pow_pos (inv_pos.mpr ht) _) (sq_pos_of_ne_zero (cleMatrix_det_ne_zero A))
  change c ≤ q*(hessian u 0).det ∧ q*(hessian u 0).det ≤ C at H0
  change c ≤ q*(hessian u x).det ∧ q*(hessian u x).det ≤ C at Hx
  constructor
  · apply (mul_le_mul_iff_right₀ hq).mp
    have hh := mul_le_mul_of_nonneg_left H0.2 (div_nonneg hc.le hC.le)
    have he : (c/C)*C=c := div_mul_cancel₀ c hC.ne'
    rw [he] at hh
    calc
      q * ((c/C)*(hessian u 0).det) = (c/C)*(q*(hessian u 0).det) := by ring
      _ ≤ c := hh
      _ ≤ q*(hessian u x).det := Hx.1
  · apply (mul_le_mul_iff_right₀ hq).mp
    have hh := mul_le_mul_of_nonneg_left H0.1 (div_nonneg hC.le hc.le)
    have he : (C/c)*c=C := div_mul_cancel₀ C hc.ne'
    rw [he] at hh
    calc
      q*(hessian u x).det ≤ C := Hx.2
      _ ≤ (C/c)*(q*(hessian u 0).det) := hh
      _ = q*((C/c)*(hessian u 0).det) := by ring

end GlobalDetRatio


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireGlobalDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGlobalDet

lemma sectionBalance_tangentShift {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) {ρ : ℝ} (hbal : SectionBalance univ u ρ)
    (a : Space n) (h : ℝ) : SectionBalance univ (tangentShift u a h) ρ := by
  have he (x : Space n) (t : ℝ) : tangentSection univ (tangentShift u a h) x t = tangentSection univ u x t := by
    ext y
    simp only [tangentSection,mem_ofPred_eq,tangentHeight_tangentShift (hu.differentiable (by simp))]
  intro x hx t ht y hy
  rw [he] at hy ⊢
  exact hbal x hx t ht y hy

/-- Once genuine balance is produced, the whole Hessian determinant is
bounded above and below by positive constants. The proof uses only that
balance and the original affine maximal equation. -/
theorem balanced_global_det_bounds {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c ≤ (hessian u x).det ∧ (hessian u x).det ≤ C := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  obtain ⟨c,C,hc,hC,H⟩ := centered_balanced_global_det_ratio hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0)
  refine ⟨c*(hessian u 0).det,C*(hessian u 0).det,mul_pos hc (hp 0).det_pos,mul_pos hC (hp 0).det_pos,?_⟩
  intro x
  simpa only [hh] using H x

end EntireGlobalDet



end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConstantDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantDetProducer

 theorem balanced_bounded_harmonic_constant {n : ℕ} (hn : 1 ≤ n)
    {u F : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ)
    (hF : ContDiff ℝ ∞ F) (hFb : BddBelow (range F)) (hFa : BddAbove (range F))
    (hLF : ∀ x, inverseHessianTrace u F x=0) : ∀ x y, F x=F y := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  apply centered_balanced_bounded_harmonic_constant hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0) hF hFb hFa
  intro x
  simpa only [inverseHessianTrace,hh] using hLF x

/-- Constant determinant is *produced* by the original equation and actual
balanced normalization family, rather than inserted as a hypothesis. -/
theorem balanced_affineMaximal_constant_det_oai {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∀ x y, (hessian u x).det=(hessian u y).det := by
  obtain ⟨c,C,hc,hC,Hb⟩ := balanced_global_det_bounds hn hu hp hm hρ hρ1 hbal
  have hw : ContDiff ℝ ∞ (affineWeight u) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact contDiffAt_affineWeight hu.contDiffAt (hp x)
  have hβ : -(((n:ℝ)+1)/((n:ℝ)+2))<0 := neg_neg_of_pos (div_pos (by positivity) (by positivity))
  have hwbelow : BddBelow (range (affineWeight u)) := by
    refine ⟨(C:ℝ)^(-(((n:ℝ)+1)/((n:ℝ)+2))),?_⟩
    rintro y ⟨x,rfl⟩
    exact Real.rpow_le_rpow_of_nonpos (hp x).det_pos (Hb x).2 hβ.le
  have hwupper : BddAbove (range (affineWeight u)) := by
    refine ⟨(c:ℝ)^(-(((n:ℝ)+1)/((n:ℝ)+2))),?_⟩
    rintro y ⟨x,rfl⟩
    exact Real.rpow_le_rpow_of_nonpos hc (Hb x).1 hβ.le
  have H := balanced_bounded_harmonic_constant hn hu hp hm hρ hρ1 hbal hw hwbelow hwupper
    (fun x => affineMaximal_inverseHessianTrace_zero hm (mem_univ x) (hp x))
  intro x y
  exact (Real.rpow_left_inj (hp x).det_pos.le (hp y).det_pos.le hβ.ne).mp (H x y)

end ConstantDetProducer



end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.balanced_affineMaximal_constant_det_oai := @OAI.AffineBernstein.balanced_affineMaximal_constant_det_oai
