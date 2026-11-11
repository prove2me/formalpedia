-- Prove2me | solution 1 for OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:34:22.800283+00:00
-- url     : https://prove2.me/submissions/95be0283-d57e-4d41-907b-e3fd9cf2c8df

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000
import Theorems.Thm_OAI_SharpIntegralFillings_IntegerChart_exists_scalar_straightened_charts
import Theorems.Thm_OAI_SharpIntegralFillings_IntegerChart_hilbert_mass_measure_le

section
-- module Solutions.OAIQ219_IF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Basic
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings

attribute [local instance] Classical.propDecidable

universe u

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

lemma mass_nonneg {k : ℕ} (T : Functional X k) : 0 ≤ mass T := by
  apply Real.sInf_nonneg
  rintro r ⟨μ, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

@[simp] lemma mass_zero (k : ℕ) : mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  apply le_antisymm
  · have h : Controls (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) (0 : Measure X) := by
      intro b π hb hπ
      simp
    simpa using mass_le_measure (μ := (0 : Measure X)) inferInstance h
  · exact mass_nonneg _

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]

lemma IsMetricCurrent.mass_bound_uniform [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ)) * M) * mass T := by
  obtain ⟨μ, hfin, hcontrol, heq⟩ := hT.exists_controls_mass_eq
  let := hfin
  have hint : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hint (integrable_const M) hM
  calc |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hcontrol hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ * M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = ((∏ i, (K i : ℝ)) * M) * mass T := by rw [heq]; ring

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_DenseTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma summable_actions_of_summable_masses [CompactSpace X]
    {k : ℕ} {Ts : ℕ → Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j))
    (hsum : Summable fun j => mass (Ts j)) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) : Summable fun j => Ts j b π := by
  choose K hK using h.2
  obtain ⟨M, hM⟩ := h.1.2
  apply (hsum.mul_left ((∏ i, (K i : ℝ)) * M)).of_norm_bounded
  intro j
  exact (hTs j).mass_bound_uniform h.1 K hK hM

end Foundations

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
lemma abs_det_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le
    (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)))
  rw [Orientation.volumeForm_robust _ b rfl, Module.Basis.det_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have heq : b.toBasis.toMatrix (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) = A.transpose := by
    ext i j
    simp [b, Module.Basis.toMatrix_apply]
  rw [heq, Matrix.det_transpose]

lemma row_norm_le_of_dot_bound {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_one_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ 1 := by
  apply (abs_det_le_prod_row_norm A).trans
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => row_norm_le_of_dot_bound _ (h i))

lemma dot_mulVec_sqrt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    v ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]

lemma abs_det_le_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ 1 := by
    apply abs_det_le_one_of_dot_bound
    intro i v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ 1*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = Real.sqrt P.det := by rw [one_mul,hQdet]

lemma row_norm_le_of_dot_bound_const {n : ℕ} (a : Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ K := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_pow_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ K^n := by
  apply (abs_det_le_prod_row_norm A).trans
  calc
    _ ≤ ∏ _i : Fin n, K := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => row_norm_le_of_dot_bound_const _ hK (h i))
    _ = K^n := by simp

lemma sqrt_det_le_pow_of_quadratic_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    Real.sqrt P.det ≤ K^n := by
  have hdet : (CFC.sqrt P).det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  rw [←hdet]
  have hdnonneg : 0 ≤ (CFC.sqrt P).det := by rw [hdet]; exact Real.sqrt_nonneg _
  rw [←abs_of_nonneg hdnonneg]
  apply abs_det_le_pow_of_dot_bound _ hK
  intro i v
  have hn : ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
    rw [dot_mulVec_sqrt P hP]
    have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
        ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq
          (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
    rw [heq, Real.sqrt_sq (norm_nonneg _)]
  apply le_trans _ (h v)
  rw [←hn]
  exact PiLp.norm_apply_le (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Polarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace SharpIntegralFillings
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma exists_bilinForm_of_parallelogram (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ B : LinearMap.BilinForm ℝ E, B.IsSymm ∧ B.toQuadraticMap.PosDef ∧
      (∀ v, B v v = (p v)^2) ∧
      ∀ u v, B u v = ((p (u+v))^2-(p (u-v))^2)/4 := by
  let : Norm E := ⟨p⟩
  let core : NormedSpace.Core ℝ E :=
    { norm_nonneg := fun v => apply_nonneg p v
      norm_smul := fun c v => map_smul_eq_mul p c v
      norm_triangle := fun x y => map_add_le_add p x y
      norm_eq_zero_iff := hp }
  let : NormedAddCommGroup E := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ E := NormedSpace.ofCore core
  have hparanorm : ∀ u v : E,
      ‖u+v‖*‖u+v‖+‖u-v‖*‖u-v‖ = 2*(‖u‖*‖u‖+‖v‖*‖v‖) := by
    intro u v
    change p (u+v)*p (u+v)+p (u-v)*p (u-v) = 2*(p u*p u+p v*p v)
    nlinarith [hpara u v]
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hparanorm
  refine ⟨innerₗ E,?_,?_,?_,?_⟩
  · exact ⟨fun u v => (real_inner_comm u v).symm⟩
  · intro v hv
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr hv
  · intro v
    change inner ℝ v v = (p v)^2
    exact real_inner_self_eq_norm_sq v
  · intro u v
    change inner ℝ u v = ((p (u+v))^2-(p (u-v))^2)/4
    have H := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) u v
    change inner ℝ u v = (p (u+v)*p (u+v)-p (u-v)*p (u-v))/4 at H
    simpa only [pow_two] using H

lemma polarizationMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    (polarizationMatrix p b).PosDef := by
  obtain ⟨B,hB,hpos,_,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b B hB).1 hpos

lemma polarizationMatrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : E) :
    (b.repr v) ⬝ᵥ (polarizationMatrix p b).mulVec (b.repr v) = (p v)^2 := by
  obtain ⟨B,_,_,hdiag,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  rw [←hdiag v]
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v v).symm

lemma measurable_polarizationMatrix {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] (p : A → Seminorm ℝ E) (b : ι → E)
    (hp : ∀ v, Measurable (fun x => p x v)) :
    ∀ i j, Measurable (fun x => polarizationMatrix (p x) b i j) := by
  intro i j
  exact ((hp _).pow_const 2 |>.sub ((hp _).pow_const 2)).div_const 4
end SharpIntegralFillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_CurveSpeed
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}

lemma coordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (distanceCoordinate f q) := by
  change LipschitzWith K (fun t : ℝ => dist (f t) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma coordinate_deriv_bound (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ K := by
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (coordinate_lipschitz hf q)

lemma coordinate_deriv_le_speed (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ metricSpeed f t :=
  le_ciSup ⟨(K : ℝ), by rintro v ⟨r, rfl⟩; exact coordinate_deriv_bound hf r t⟩ q

lemma metricSpeed_nonneg (hf : LipschitzWith K f) (t : ℝ) : 0 ≤ metricSpeed f t :=
  (abs_nonneg _).trans (coordinate_deriv_le_speed hf 0 t)

lemma metricSpeed_le (hf : LipschitzWith K f) (t : ℝ) : metricSpeed f t ≤ K :=
  ciSup_le (fun q => coordinate_deriv_bound hf q t)

lemma measurable_metricSpeed (f : ℝ → X) : Measurable (metricSpeed f) :=
  Measurable.iSup (fun q => (measurable_deriv (distanceCoordinate f q)).abs)

lemma locallyIntegrable_metricSpeed (hf : LipschitzWith K f) :
    LocallyIntegrable (metricSpeed f) volume := by
  apply (memLp_top_of_bound (measurable_metricSpeed f).aestronglyMeasurable (K : ℝ) ?_).locallyIntegrable le_top
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg hf t)]
    exact metricSpeed_le hf t

lemma intervalIntegrable_metricSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    IntervalIntegrable (metricSpeed f) volume s t :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_metricSpeed hf).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

lemma coordinate_difference_bound (hf : LipschitzWith K f) (q : ℕ) {s t : ℝ} (hst : s ≤ t) :
    |distanceCoordinate f q t - distanceCoordinate f q s| ≤ ∫ x in s..t, metricSpeed f x := by
  have hac := (coordinate_lipschitz hf q).lipschitzOnWith.absolutelyContinuousOnInterval (a := s) (b := t)
  rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hst).trans
  apply intervalIntegral.integral_mono_on hst hac.intervalIntegrable_deriv.norm
    (intervalIntegrable_metricSpeed hf s t)
  intro x hx
  exact coordinate_deriv_le_speed hf q x

lemma distance_le_integral_speed (hf : LipschitzWith K f) {s t : ℝ} (hst : s ≤ t) :
    dist (f t) (f s) ≤ ∫ x in s..t, metricSpeed f x := by
  have hc : Continuous (fun y : X => |dist (f t) y - dist (f s) y|) :=
    ((continuous_const.dist continuous_id).sub (continuous_const.dist continuous_id)).abs
  have h := (denseRange_denseSeq X).induction_on
    (p := fun y : X => |dist (f t) y - dist (f s) y| ≤
      ∫ x in s..t, metricSpeed f x) (f s) (isClosed_le hc continuous_const)
      (fun q => coordinate_difference_bound hf q hst)
  simpa using h

lemma distance_le_integratedSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    dist (f t) (f s) ≤ |integratedSpeed f t - integratedSpeed f s| := by
  have hi (a b : ℝ) := intervalIntegrable_metricSpeed hf a b
  have hd (a b : ℝ) : integratedSpeed f b - integratedSpeed f a =
      ∫ x in a..b, metricSpeed f x := by
    exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  rcases le_total s t with hst | hts
  · rw [hd s t, abs_of_nonneg (intervalIntegral.integral_nonneg hst
      (fun x hx => metricSpeed_nonneg hf x))]
    exact distance_le_integral_speed hf hst
  · rw [abs_sub_comm, hd t s, abs_of_nonneg (intervalIntegral.integral_nonneg hts
      (fun x hx => metricSpeed_nonneg hf x)), dist_comm]
    exact distance_le_integral_speed hf hts

lemma abs_slope_tendsto {g : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt g d x) :
    Tendsto (fun t => |g t-g x|/|t-x|) (𝓝[≠] x) (𝓝 |d|) := by
  simpa only [slope, norm_smul, norm_inv, Real.norm_eq_abs, vsub_eq_sub, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope.norm

theorem ae_hasMetricDerivAt (hf : LipschitzWith K f) :
    ∀ᵐ x, HasMetricDerivAt f (metricSpeed f x) x := by
  have hcoords : ∀ᵐ x, ∀ q : ℕ, DifferentiableAt ℝ (distanceCoordinate f q) x := by
    rw [ae_all_iff]
    intro q
    exact (coordinate_lipschitz hf q).ae_differentiableAt_real
  have hint := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_metricSpeed hf)
  filter_upwards [hcoords, hint] with x hx hI
  have hg := abs_slope_tendsto (hI 0)
  rw [abs_of_nonneg (metricSpeed_nonneg hf x)] at hg
  change Tendsto (fun t => |integratedSpeed f t-integratedSpeed f x|/|t-x|)
    (𝓝[≠] x) (𝓝 (metricSpeed f x)) at hg
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hb : BddAbove (range (fun q : ℕ => |deriv (distanceCoordinate f q) x|)) :=
      ⟨(K : ℝ), by rintro v ⟨q, rfl⟩; exact coordinate_deriv_bound hf q x⟩
    obtain ⟨q, hq⟩ := (lt_ciSup_iff hb).mp hc
    have hd := abs_slope_tendsto (hx q).hasDerivAt
    filter_upwards [hd.eventually (eventually_gt_nhds hq)] with t ht
    exact ht.trans_le (div_le_div_of_nonneg_right
      (abs_dist_sub_le (f t) (f x) (denseSeq X q)) (abs_nonneg _))
  · intro c hc
    filter_upwards [hg.eventually (eventually_lt_nhds hc)] with t ht
    exact (div_le_div_of_nonneg_right (distance_le_integratedSpeed hf x t) (abs_nonneg _)).trans_lt ht

end SharpIntegralFillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Directional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]

lemma signedDistance_zero (c : ℝ → X) : signedDistance c 0 = 0 := by
  simp [signedDistance]

lemma signedDistance_div (c : ℝ → X) (t : ℝ) :
    signedDistance c t / t = dist (c t) (c 0) / |t| := by
  rcases le_total 0 t with ht | ht
  · simp [signedDistance, ht, abs_of_nonneg ht]
  · by_cases h0 : t = 0
    · simp [h0]
    · simp [signedDistance, not_le.mpr (lt_of_le_of_ne ht h0), abs_of_nonpos ht, neg_div, div_neg]

lemma hasDerivAt_signedDistance_iff (c : ℝ → X) (d : ℝ) :
    HasDerivAt (signedDistance c) d 0 ↔
      Tendsto (fun t => dist (c t) (c 0) / |t|) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, signedDistance_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul,
    signedDistance_div]

lemma continuous_signedDistance {A : Type*} [TopologicalSpace A] {c : A → ℝ → X}
    (hc : Continuous c.uncurry) : Continuous (fun p : A × ℝ => signedDistance (c p.1) p.2) := by
  have hd : Continuous (fun p : A × ℝ => dist (c p.1 p.2) (c p.1 0)) :=
    hc.dist (hc.comp (continuous_fst.prodMk continuous_const))
  exact hd.if_le hd.neg continuous_const continuous_snd (by
    rintro ⟨x,t⟩ (h : 0 = t)
    simp [← h])

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
lemma scalarCoordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (scalarCoordinate f q) := by
  change LipschitzWith K (fun x : E => dist (f x) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using
    (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma measurable_lineSpeed (hf : Continuous f) (v : E) : Measurable (lineSpeed f v) := by
  apply Measurable.iSup
  intro q
  exact (measurable_lineDeriv (hf.dist continuous_const)).abs

omit [MeasurableSpace E] [BorelSpace E] in
lemma deriv_coordinate_line (p v : E) (s : ℝ) (q : ℕ) :
    deriv (MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q) s =
      lineDeriv ℝ (scalarCoordinate f q) (p+s • v) v := by
  rw [lineDeriv]
  have he : (fun t : ℝ => scalarCoordinate f q (p+s • v+t • v)) =
      (fun t : ℝ => MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q (s+t)) := by
    ext t
    simp [scalarCoordinate, MetricDifferentiationDense.distanceCoordinate, add_smul, add_assoc]
  rw [he]
  simpa using (deriv_comp_const_add (f := MetricDifferentiationDense.distanceCoordinate
    (fun t => f (p+t • v)) q) s 0).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma lineSpeed_eq_curveSpeed (p v : E) (s : ℝ) :
    lineSpeed f v (p+s • v) = MetricDifferentiationDense.metricSpeed (fun t => f (p+t • v)) s := by
  simp only [lineSpeed, MetricDifferentiationDense.metricSpeed, deriv_coordinate_line]

lemma measurableSet_hasMetricDirectionalDeriv (hf : Continuous f) (v : E) :
    MeasurableSet {x | Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x))} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hD := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hder := measurable_deriv_with_param (f := fun x t => signedDistance (c x) t)
    (continuous_signedDistance hc)
  have hm := (measurable_prodMk_right (y := (0 : ℝ)) hD).inter
    (measurableSet_eq_fun (hder.comp (measurable_prodMk_right (y := (0 : ℝ)))) (measurable_lineSpeed hf v))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro ht
    have hd := (hasDerivAt_signedDistance_iff (c x) (lineSpeed f v x)).mpr (by simpa [c] using ht)
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · rintro ⟨hd, he⟩
    rw [← he]
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

lemma tendsto_add_zero_punctured (s : ℝ) :
    Tendsto (fun t : ℝ => s+t) (𝓝[≠] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝 0) (𝓝 s)).add tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

theorem ae_hasMetricDirectionalDeriv [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x)) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  apply ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
    (measurableSet_hasMetricDirectionalDeriv hf.continuous v)
  intro p
  have hcurve := hf.comp ((LipschitzWith.const p).add L.lipschitz)
  filter_upwards [MetricDifferentiationDense.ae_hasMetricDerivAt hcurve] with s hs
  change Tendsto (fun t : ℝ => dist (f (p+s • v+t • v)) (f (p+s • v)) / |t|)
    (𝓝[≠] 0) (𝓝 (lineSpeed f v (p+s • v)))
  rw [lineSpeed_eq_curveSpeed]
  have hh := hs.comp (tendsto_add_zero_punctured s)
  simpa only [Function.comp_def, L, MetricDifferentiationDense.HasMetricDerivAt,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    add_smul, add_assoc, add_sub_cancel_left] using hh

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Seminorm
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma coordinateSeminorm_le (hf : LipschitzWith K f) (x : E) (q : ℕ) :
    coordinateSeminorm f x q ≤ K • normSeminorm ℝ E := by
  intro v
  change ‖fderiv ℝ (scalarCoordinate f q) x v‖ ≤ (K : ℝ) * ‖v‖
  exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ (scalarCoordinate_lipschitz hf q)) (norm_nonneg _))

lemma bddAbove_coordinateSeminorm (hf : LipschitzWith K f) (x : E) :
    BddAbove (range (coordinateSeminorm f x)) :=
  ⟨K • normSeminorm ℝ E, by rintro p ⟨q,rfl⟩; exact coordinateSeminorm_le hf x q⟩

lemma metricSeminorm_apply (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v = ⨆ q : ℕ, |fderiv ℝ (scalarCoordinate f q) x v| := by
  rw [metricSeminorm, Seminorm.iSup_apply (bddAbove_coordinateSeminorm hf x)]
  rfl

lemma metricSeminorm_le (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v ≤ (K : ℝ) * ‖v‖ :=
  (ciSup_le (fun q => coordinateSeminorm_le hf x q) :
    metricSeminorm f x ≤ K • normSeminorm ℝ E) v

lemma metricSeminorm_lipschitz (hf : LipschitzWith K f) (x : E) :
    LipschitzWith K (metricSeminorm f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
  exact ((metricSeminorm f x).norm_sub_map_le_sub v w).trans (metricSeminorm_le hf x (v-w))

lemma lineSpeed_eq_metricSeminorm (hf : LipschitzWith K f) {x : E}
    (hx : ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x) (v : E) :
    lineSpeed f v x = metricSeminorm f x v := by
  rw [metricSeminorm_apply hf]
  simp only [lineSpeed, (hx _).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ae_dense_directionalSeminorm (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (metricSeminorm f x (denseSeq E j))) := by
  have hcoord : ∀ᵐ x ∂μ, ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x := by
    rw [ae_all_iff]
    exact fun q => (scalarCoordinate_lipschitz hf q).ae_differentiableAt
  have hdir : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (lineSpeed f (denseSeq E j) x)) := by
    rw [ae_all_iff]
    exact fun j => ae_hasMetricDirectionalDeriv μ hf _
  filter_upwards [hcoord, hdir] with x hx hd j
  simpa only [lineSpeed_eq_metricSeminorm hf hx] using hd j

end SharpIntegralFillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric

lemma uniformly_tendsto_of_lipschitz {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {s : Set A} (hs : IsCompact s)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) l (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ x ∈ s, dist (f j x) (g x) < ε := by
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, ht, hcov⟩ := hs.finite_cover_balls hδ
  have hev : ∀ᶠ j in l, ∀ y ∈ t, dist (f j y) (g y) < ε/2 := by
    rw [ht.eventually_all]
    exact fun y hy => (Metric.tendsto_nhds.mp (hlim y (hts hy))) (ε/2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < δ := by
    rcases mem_iUnion.mp (hcov hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hball⟩
    exact ⟨y, hyt, hball⟩
  have hdr : (K : ℝ) * dist x y < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hxy (show 0 < (K : ℝ)+1 by positivity)
    have heq : ((K : ℝ)+1)*δ = ε/4 := by dsimp [δ]; field_simp
    rw [heq] at hm
    exact lt_of_le_of_lt (by nlinarith [dist_nonneg (x := x) (y := y)]) hm
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j y) + dist (f j y) (g y) + dist (g y) (g x) :=
        (dist_triangle _ (g y) _).trans (add_le_add (dist_triangle _ (f j y) _) le_rfl)
    _ < ε/4 + ε/2 + ε/4 := by
      apply add_lt_add
      · exact add_lt_add (((hf j).dist_le_mul x y).trans_lt hdr) (hj y hy)
      · rw [dist_comm]
        exact (hg.dist_le_mul x y).trans_lt hdr
    _ = ε := by ring
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Centered
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}

lemma metricQuotient_lipschitz (hf : LipschitzWith K f) (x : E) (t : ℝ) :
    LipschitzWith K (metricQuotient f x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  by_cases ht : t = 0
  · simp only [metricQuotient, ht, abs_zero, div_zero, dist_self]
    positivity
  have ht' : 0 < |t| := abs_pos.mpr ht
  simp only [metricQuotient, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  calc |dist (f (x+t • v)) (f x) - dist (f (x+t • w)) (f x)|/|t| ≤
        dist (f (x+t • v)) (f (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _) ht'.le
    _ ≤ ((K : ℝ) * dist (x+t • v) (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (hf.dist_le_mul _ _) ht'.le
    _ = (K : ℝ) * dist v w := by
      rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, dist_eq_norm]
      field_simp

lemma hasCenteredMetricDifferential_of_dense_directions [FiniteDimensional ℝ E]
    (hf : LipschitzWith K f) (x : E) (p : Seminorm ℝ E)
    (hp : LipschitzWith K p) {ι : Type*} {D : ι → E} (hD : DenseRange D)
    (hdir : ∀ j, Tendsto (fun t => metricQuotient f x t (D j)) (𝓝[≠] 0) (𝓝 (p (D j)))) :
    HasCenteredMetricDifferential f p x := by
  have hall (v : E) : Tendsto (fun t => metricQuotient f x t v) (𝓝[≠] 0) (𝓝 (p v)) :=
    tendsto_of_lipschitz_dense (metricQuotient_lipschitz hf x) hp hD hdir v
  apply IsLittleO.of_bound
  intro ε hε
  have hU := uniformly_tendsto_of_lipschitz (metricQuotient_lipschitz hf x) hp
    (isCompact_sphere (0 : E) 1) (fun v _ => hall v) hε
  obtain ⟨δ, hδ, hUδ⟩ := Metric.mem_nhdsWithin_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  let r : ℝ := ‖y-x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let v : E := r⁻¹ • (y-x)
  have hv : v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hrv : r • v = y-x := by dsimp [v]; exact smul_inv_smul₀ hr.ne' _
  have hry : x+r • v = y := by rw [hrv]; abel
  have hrδ : r ∈ ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · change |r-0| < δ
      rw [sub_zero, abs_of_pos hr]
      simpa only [mem_ball, dist_eq_norm, r] using hy
    · exact hr.ne'
  have hh := hUδ hrδ v hv
  change dist (dist (f (x+r • v)) (f x)/|r|) (p v) < ε at hh
  rw [hry, abs_of_pos hr, Real.dist_eq] at hh
  have hpv : p (y-x) = r * p v := by
    rw [← hrv, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hpv, Real.norm_eq_abs]
  change |dist (f y) (f x)-r*p v| ≤ ε*r
  have heq : dist (f y) (f x)-r*p v = r*(dist (f y) (f x)/r-p v) := by field_simp
  rw [heq, abs_mul, abs_of_pos hr]
  exact (mul_lt_mul_of_pos_left hh hr).le.trans_eq (mul_comm r ε)

variable [SeparableSpace X] [Nonempty X] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem ae_hasCenteredMetricDifferential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, HasCenteredMetricDifferential f (metricSeminorm f x) x := by
  filter_upwards [ae_dense_directionalSeminorm μ hf] with x hx
  exact hasCenteredMetricDifferential_of_dense_directions hf x _ (metricSeminorm_lipschitz hf x)
    (denseRange_denseSeq E) hx

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ErrorModulus
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
omit [FiniteDimensional ℝ E] in
lemma measurable_metricSeminorm_apply (hf : LipschitzWith K f) (v : E) :
    Measurable (fun x => metricSeminorm f x v) := by
  simp only [metricSeminorm_apply hf]
  exact Measurable.iSup (fun q => (measurable_fderiv_apply_const ℝ (scalarCoordinate f q) v).abs)

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_nonneg (r : ℝ) (q : ℕ) (x : E) :
    0 ≤ metricErrorTerm f r q x := by
  dsimp [metricErrorTerm]
  split_ifs
  · positivity
  · rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_le (hf : LipschitzWith K f) (r : ℝ) (q : ℕ) (x : E) :
    metricErrorTerm f r q x ≤ 2*(K : ℝ) := by
  dsimp [metricErrorTerm]
  split_ifs with h
  · apply (div_le_iff₀ h.1).mpr
    have hd : dist (f (x+denseSeq E q)) (f x) ≤ (K : ℝ)*‖denseSeq E q‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le_mul (x+denseSeq E q) x
    have hp := metricSeminorm_le hf x (denseSeq E q)
    have hp0 := apply_nonneg (metricSeminorm f x) (denseSeq E q)
    have hd0 := dist_nonneg (x := f (x+denseSeq E q)) (y := f x)
    rw [abs_le]
    constructor <;> nlinarith
  · positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma bddAbove_metricErrorTerm (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    BddAbove (range (fun q => metricErrorTerm f r q x)) :=
  ⟨2*(K : ℝ), by rintro _ ⟨q,rfl⟩; exact metricErrorTerm_le hf r q x⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_nonneg (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    0 ≤ metricErrorModulus f r x :=
  (metricErrorTerm_nonneg r 0 x).trans (le_ciSup (bddAbove_metricErrorTerm hf r x) 0)

lemma measurable_metricErrorModulus (hf : LipschitzWith K f) (r : ℝ) :
    Measurable (metricErrorModulus f r) := by
  change Measurable (fun x => ⨆ q : ℕ, metricErrorTerm f r q x)
  apply Measurable.iSup
  intro q
  change Measurable (fun x => metricErrorTerm f r q x)
  unfold metricErrorTerm
  split_ifs
  · exact (((hf.continuous.comp (continuous_id.add continuous_const)).dist hf.continuous).measurable.sub
      (measurable_metricSeminorm_apply hf _)).abs.div_const _
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le_of_bound (_hf : LipschitzWith K f) {r ε : ℝ} {x : E}
    (hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ ≤ r → |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ ε*‖v‖) :
    metricErrorModulus f r x ≤ ε := by
  apply ciSup_le
  intro q
  dsimp [metricErrorTerm]
  split_ifs with h
  · exact (div_le_iff₀ h.1).mpr (H _ h.2)
  · exact hε

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_tendsto_zero (hf : LipschitzWith K f) {x : E}
    (hx : HasCenteredMetricDifferential f (metricSeminorm f x) x)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (metricErrorModulus_nonneg hf _ _))
  · intro ε hε
    have hxε := hx.bound (half_pos hε)
    obtain ⟨δ,hδ,hδx⟩ := Metric.mem_nhds_iff.mp hxε
    have hδr := (tendsto_order.1 hr).2 δ hδ
    filter_upwards [hδr] with n hn
    apply lt_of_le_of_lt (metricErrorModulus_le_of_bound hf (half_pos hε).le ?_)
      (half_lt_self hε)
    intro v hv
    have hvδ : x+v ∈ ball x δ := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hv.trans_lt hn
    simpa only [mem_ofPred_eq, add_sub_cancel_left, Real.norm_eq_abs] using hδx hvδ

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_bound (hf : LipschitzWith K f) {r : ℝ} (x v : E)
    (hv : ‖v‖ < r) :
    |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ metricErrorModulus f r x * ‖v‖ := by
  let A : Set E := {w | |dist (f (x+w)) (f x)-metricSeminorm f x w| ≤
    metricErrorModulus f r x * ‖w‖}
  have hA : IsClosed A := isClosed_le
    (((hf.continuous.comp (continuous_const.add continuous_id)).dist continuous_const).sub
      (metricSeminorm_lipschitz hf x).continuous).abs
    (continuous_const.mul continuous_norm)
  have hsub : ball (0 : E) r ∩ range (denseSeq E) ⊆ A := by
    rintro w ⟨hq,⟨q,rfl⟩⟩
    by_cases hw : denseSeq E q = 0
    · simp [A,hw]
    have hqw : 0 < ‖denseSeq E q‖ := norm_pos_iff.mpr hw
    have hqr : ‖denseSeq E q‖ ≤ r := (by simpa only [mem_ball, dist_zero_right] using hq :
      ‖denseSeq E q‖ < r).le
    have hle := le_ciSup (bddAbove_metricErrorTerm hf r x) q
    rw [metricErrorTerm, ite_eq_left ⟨hqw,hqr⟩] at hle
    exact (div_le_iff₀ hqw).mp hle
  have hvcl := (denseRange_denseSeq E).open_subset_closure_inter isOpen_ball
    (by simpa only [mem_ball, dist_zero_right] using hv : v ∈ ball (0 : E) r)
  exact hA.closure_subset_iff.mpr hsub hvcl

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_TwoPoint
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seminorm_sub_bound_of_sphere {p q : Seminorm ℝ E} {ε : ℝ} (_hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ = 1 → |p v-q v| ≤ ε) (v : E) :
    |p v-q v| ≤ ε*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,hv0.ne']
  have he : ‖v‖ • u = v := by simp [u,hv0.ne']
  have hpv : p v = ‖v‖ * p u := by
    calc p v = p (‖v‖ • u) := congrArg p he.symm
      _ = ‖v‖ * p u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  have hqv : q v = ‖v‖ * q u := by
    calc q v = q (‖v‖ • u) := congrArg q he.symm
      _ = ‖v‖ * q u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  calc |p v-q v| = ‖v‖ * |p u-q u| := by
        rw [hpv,hqv,←mul_sub,abs_mul,abs_of_pos hv0]
    _ ≤ ‖v‖*ε := mul_le_mul_of_nonneg_left (H u hu) hv0.le
    _ = ε*‖v‖ := mul_comm _ _

variable [FiniteDimensional ℝ E]
lemma eventually_seminorm_bound_of_dense
    {ι κ : Type*} {l : Filter ι} {p : ι → Seminorm ℝ E} {q : Seminorm ℝ E}
    {K : ℝ≥0} (hp : ∀ i, LipschitzWith K (p i)) (hq : LipschitzWith K q)
    {D : κ → E} (hD : DenseRange D)
    (hc : ∀ j, Tendsto (fun i => p i (D j)) l (𝓝 (q (D j))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ v : E, |p i v-q v| ≤ ε*‖v‖ := by
  have hlim := tendsto_of_lipschitz_dense hp hq hD hc
  have h := uniformly_tendsto_of_lipschitz hp hq (isCompact_sphere (0 : E) 1)
    (fun v _ => hlim v) hε
  filter_upwards [h] with i hi v
  apply seminorm_sub_bound_of_sphere hε.le _ v
  intro w hw
  exact (hi w (by simpa only [mem_sphere,dist_zero_right] using hw)).le

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma hasTwoPointMetricDifferential_of_uniformModulus
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s) :
    HasTwoPointMetricDifferential f (metricSeminorm f x) s x := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨N,hN⟩ := (eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) (ε/2) (half_pos hε)))
  have hNN (y : E) (hy : y ∈ s) : metricErrorModulus f (r N) y < ε/2 := by
    have h := hN N le_rfl y hy
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using h
  have hfst : Tendsto (fun q : E × E => q.1) (𝓝[s ×ˢ s] (x,x)) (𝓝[s] x) :=
    continuous_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hq => hq.1)
  have hnear : ∀ᶠ q : E × E in 𝓝[s ×ˢ s] (x,x), ‖q.2-q.1‖ < r N := by
    have ht : Tendsto (fun q : E × E => ‖q.2-q.1‖) (𝓝[s ×ˢ s] (x,x)) (𝓝 0) := by
      simpa using ((continuous_snd.sub continuous_fst).norm.continuousWithinAt.tendsto (s := s ×ˢ s) (x := (x,x)))
    exact (tendsto_order.1 ht).2 _ (hr N)
  filter_upwards [hfst.eventually hp,hnear,self_mem_nhdsWithin] with q hqp hqr hqs
  have he₁ := metricErrorModulus_bound hf q.1 (q.2-q.1) hqr
  have he₂ := hqp (q.2-q.1)
  have hm := hNN q.1 hqs.1
  have ht : ‖q.2-q.1‖ ≤ ‖q.1-x‖+‖q.2-x‖ := by
    calc ‖q.2-q.1‖ = ‖(q.2-x)-(q.1-x)‖ := by congr 1; abel
      _ ≤ ‖q.2-x‖+‖q.1-x‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have he : |dist (f q.1) (f q.2)-metricSeminorm f x (q.1-q.2)| ≤
      ε*(‖q.1-x‖+‖q.2-x‖) := by
    have hpneg : metricSeminorm f x (q.1-q.2) = metricSeminorm f x (q.2-q.1) := by
      rw [←neg_sub q.2 q.1,map_neg_eq_map]
    rw [hpneg,dist_comm]
    calc |dist (f q.2) (f q.1)-metricSeminorm f x (q.2-q.1)| ≤
          |dist (f q.2) (f q.1)-metricSeminorm f q.1 (q.2-q.1)| +
            |metricSeminorm f q.1 (q.2-q.1)-metricSeminorm f x (q.2-q.1)| := abs_sub_le _ _ _
      _ ≤ metricErrorModulus f (r N) q.1 * ‖q.2-q.1‖ + ε/2*‖q.2-q.1‖ := by
        apply add_le_add _ he₂
        simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
      _ ≤ ε*‖q.2-q.1‖ := by nlinarith [norm_nonneg (q.2-q.1)]
      _ ≤ ε*(‖q.1-x‖+‖q.2-x‖) := mul_le_mul_of_nonneg_left ht hε.le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using he

end SharpIntegralFillings.MetricDifferentiation

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_LargePieces
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SharpIntegralFillings
lemma exists_closed_large_continuousOn
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {f : A → B} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set A, IsClosed K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := countableBasis B
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  have H (i : I) : ∃ U F : Set A,
      f ⁻¹' (i : Set B) ⊆ U ∧ F ⊆ f ⁻¹' (i : Set B) ∧
      IsOpen U ∧ IsClosed F ∧ μ (U \ F) < δ i := by
    let S := f ⁻¹' (i : Set B)
    have hS : MeasurableSet S := hf (isOpen_of_mem_countableBasis i.property).measurableSet
    have hδi : δ i / 2 ≠ 0 := (ENNReal.half_pos (hδ i).ne').ne'
    obtain ⟨U,hSU,hU,_,hμU⟩ := hS.exists_isOpen_sdiff_lt (measure_ne_top μ S) hδi
    obtain ⟨F,hFS,hF,hμF⟩ := hS.exists_isClosed_sdiff_lt (measure_ne_top μ S) hδi
    refine ⟨U,F,hSU,hFS,hU,hF,?_⟩
    calc μ (U \ F) ≤ μ ((U \ S) ∪ (S \ F)) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ S
          · exact Or.inr ⟨hxs,hx.2⟩
          · exact Or.inl ⟨hx.1,hxs⟩
      _ ≤ μ (U \ S) + μ (S \ F) := measure_union_le _ _
      _ < δ i / 2 + δ i / 2 := ENNReal.add_lt_add hμU hμF
      _ = δ i := ENNReal.add_halves _
  choose U F hSU hFS hU hF hμ using H
  let K : Set A := (⋃ i : I, U i \ F i)ᶜ
  refine ⟨K, (isOpen_iUnion (fun i => (hU i).sdiff (hF i))).isClosed_compl, ?_, ?_⟩
  · calc μ Kᶜ = μ (⋃ i : I, U i \ F i) := by simp [K]
      _ ≤ ∑' i : I, μ (U i \ F i) := measure_iUnion_le _
      _ ≤ ∑' i : I, δ i := ENNReal.tsum_le_tsum (fun i => (hμ i).le)
      _ < ε := hδsum
  · apply (isBasis_countableBasis B).continuousOn_iff.mpr
    intro V hV
    let i : I := ⟨V,hV⟩
    refine ⟨U i,hU i,?_⟩
    ext x
    constructor
    · rintro ⟨hx,hxK⟩
      exact ⟨hSU i hx,hxK⟩
    · rintro ⟨hxU,hxK⟩
      have hxF : x ∈ F i := by
        by_contra h
        exact hxK (mem_iUnion.mpr ⟨i,hxU,h⟩)
      exact ⟨hFS i hxF,hxK⟩

end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric

lemma exists_large_continuousOn_uniformly
    {A B : Type*} [TopologicalSpace A] [PseudoMetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A)
    {s : Set A} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {f : A → B} (hf : Measurable f) {u : ℕ → A → ℝ}
    (hu : ∀ n, Measurable (u n))
    (hc : ∀ᵐ x ∂μ.restrict s, Tendsto (fun n => u n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ContinuousOn f t ∧ TendstoUniformlyOn u (fun _ => 0) atTop t := by
  let ν := μ.restrict s
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hsf.lt_top⟩
  obtain ⟨K,hK,hμK,hcf⟩ := exists_closed_large_continuousOn ν hf
    (show ENNReal.ofReal (ε/2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hε)).ne')
  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc
    (half_pos hε)
  let t := s ∩ (K \ e)
  refine ⟨t,inter_subset_left,hs.inter (hK.measurableSet.diff he),?_,
    hcf.mono (fun _ h => h.2.1),hue.mono (fun _ h => h.2.2)⟩
  calc μ (s \ t) = ν (Kᶜ ∪ e) := by
        rw [Measure.restrict_apply (hK.measurableSet.compl.union he)]
        congr 1
        ext x
        simp only [t,Set.mem_sdiff,mem_inter_iff,mem_union,mem_compl_iff]
        tauto
    _ ≤ ν Kᶜ + ν e := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hμK.le hμe
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_large_twoPointMetricDifferential
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ x ∈ t, HasTwoPointMetricDifferential f (metricSeminorm f x) t x := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  obtain ⟨t,hts,ht,hμt,hct,htu⟩ := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x j => metricSeminorm f x (denseSeq E j)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun n => measurable_metricErrorModulus hf (r n)) hc hε
  refine ⟨t,hts,ht,hμt,?_⟩
  intro x hx
  apply hasTwoPointMetricDifferential_of_uniformModulus hf _ hr htu
  intro j
  exact (continuousOn_pi.1 hct j) x hx

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma tangentConeAt_pi_eq_univ_of_density_one {ι : Type*} [Fintype ι]
    (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ {f : ι → E | ∀ i, f i ∈ s} (fun _ => x) = univ := by
  classical
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ i, (s ∩ ({x} + r • closedBall (z i) (ε / 2))).Nonempty := by
    rw [eventually_all]
    intro i
    exact Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _
      measurableSet_closedBall (measure_closedBall_pos μ (z i) (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : ι → E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, hr₁, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  have H (i : ι) : ∃ a ∈ closedBall (z i) (ε / 2), x + r • a ∈ s := by
    obtain ⟨y, hys, hy⟩ := hr₁ i
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    simpa only [h, add_neg_cancel_left] using hys
  choose a ha has using H
  have haz : a ∈ closedBall z (ε / 2) := by
    rw [mem_closedBall, dist_pi_le_iff (half_pos hε).le]
    exact ha
  refine ⟨a, ?_, ?_⟩
  · have hra : r • a ∈ U ∩ ((fun _ : ι => x) + ·) ⁻¹' {f | ∀ i, f i ∈ s} := by
      exact ⟨hrU (smul_mem_smul_set haz), has⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ (ne_of_gt hr) a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using haz) (half_lt_self hε)

omit [MeasurableSpace E] [BorelSpace E] in

lemma seminorm_continuous_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  classical
  let b := Module.finBasis ℝ E
  have hsum (I : Finset (Fin (Module.finrank ℝ E)))
      (q : Fin (Module.finrank ℝ E) → E) :
      p (∑ i ∈ I, q i) ≤ ∑ i ∈ I, p (q i) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hb (v : E) : p v ≤ ∑ i, ‖b.repr v i‖ * p (b i) := by
    convert hsum Finset.univ (fun i => b.repr v i • b i) using 1
    · rw [b.sum_repr]
    · simp only [map_smul_eq_mul]
  have hcont : Continuous (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp b.continuous_coe_repr).norm.mul_const _
  apply Seminorm.continuous_of_continuousAt_zero
  have hc : Tendsto (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  simpa [ContinuousAt] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun v => apply_nonneg p v) hb

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Comparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
universe u

theorem IsCAT0.exists_squared_distance_convex
    {X : Type u} [MetricSpace X] (hX : IsCAT0 X) :
    ∃ segment : X → X → ℝ → X,
      (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
      ∀ o y x t, t ∈ Icc (0 : ℝ) 1 →
        dist (segment o y t) x ^ 2 ≤
          (1 - t) * dist o x ^ 2 + t * dist y x ^ 2 -
            t * (1 - t) * dist o y ^ 2 := by
  obtain ⟨s, hs, _, hc⟩ := hX
  refine ⟨s, hs, ?_⟩
  intro o y x t ht
  have h := hc o y x t 1 ht (by simp)
  rw [(hs o x).2] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem IsCAT0.quadrilateral {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  obtain ⟨s, _, hs⟩ := hX.exists_squared_distance_convex
  have hb := hs a c b (1 / 2) (by norm_num)
  have hd := hs a c d (1 / 2) (by norm_num)
  have ht := dist_triangle b (s a c (1 / 2)) d
  have ht' : dist b d ^ 2 ≤
      (dist b (s a c (1 / 2)) + dist (s a c (1 / 2)) d) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr ht
  have hm := sq_nonneg (dist b (s a c (1 / 2)) - dist (s a c (1 / 2)) d)
  rw [dist_comm c b] at hb
  rw [dist_comm a d] at hd
  rw [dist_comm b (s a c (1 / 2))] at ht' hm
  nlinarith

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Parallelogram
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
section MetricDifferential
variable {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in

lemma HasTwoPointMetricDifferential.scaled_pair_limit
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x u v : E}
    (h : HasTwoPointMetricDifferential f p s x)
    {c : ℕ → ℝ} {d e : ℕ → E}
    (hc : Tendsto (fun j => ‖c j‖) atTop atTop)
    (hd : ∀ᶠ j in atTop, x + d j ∈ s) (he : ∀ᶠ j in atTop, x + e j ∈ s)
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 u))
    (hce : Tendsto (fun j => c j • e j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖ * dist (f (x + d j)) (f (x + e j)))
      atTop (𝓝 (p (u - v))) := by
  have hp := seminorm_continuous_finiteDimensional p
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have he₀ := tangentConeAt.lim_zero atTop hc hce
  have hpair : Tendsto (fun j => (x + d j, x + e j)) atTop (𝓝[s ×ˢ s] (x,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add hd₀).prodMk_nhds (tendsto_const_nhds.add he₀)
    · filter_upwards [hd, he] with j hj hj'
      exact ⟨hj, hj'⟩
  have hsmall := h.comp_tendsto hpair
  have hmul := hsmall.mul_isBigO (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => (‖(x + d j) - x‖ + ‖(x + e j) - x‖) * ‖c j‖)
      atTop (𝓝 (‖u‖ + ‖v‖)) := by
    simpa only [norm_smul, add_sub_cancel_left, add_mul, mul_comm] using hcd.norm.add hce.norm
  have hzero := hmul.tendsto_zero_of_tendsto hnorm
  have hdiff := hp.tendsto (u - v) |>.comp (hcd.sub hce)
  have hsum := hzero.add hdiff
  convert hsum using 1
  · ext j
    simp only [Function.comp_apply, add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul]
    ring
  · simp

lemma HasTwoPointMetricDifferential.distance_bound
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) (w : E) :
    A * ‖w‖ ≤ B * p w := by
  let z : Fin 2 → E := ![w, 0]
  have hz : z ∈ tangentConeAt ℝ {f : Fin 2 → E | ∀ i, f i ∈ s} (fun _ => x) := by
    rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
    exact mem_univ z
  obtain ⟨c, d, hc, hd, hcd⟩ :=
    mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
  have hcd₀ := tendsto_pi_nhds.mp hcd 0
  have hcd₁ := tendsto_pi_nhds.mp hcd 1
  have hl := h.scaled_pair_limit hc (hd.mono fun _ hj => hj 0)
    (hd.mono fun _ hj => hj 1) hcd₀ hcd₁
  have hl' : Tendsto (fun j => ‖c j‖ * dist (f (x + d j 0)) (f (x + d j 1)))
      atTop (𝓝 (p w)) := by simpa [z] using hl
  have hr : Tendsto (fun j => ‖c j‖ * dist (x + d j 0) (x + d j 1))
      atTop (𝓝 ‖w‖) := by
    simpa only [Pi.smul_apply, dist_eq_norm, add_sub_add_left_eq_sub, ← norm_smul, smul_sub,
      z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
      using (hcd₀.sub hcd₁).norm
  apply le_of_tendsto_of_tendsto (hr.const_mul A) (hl'.const_mul B)
  filter_upwards [hd] with j hj
  have H := mul_le_mul_of_nonneg_left
    (hAB (x + d j 0) (hj 0) (x + d j 1) (hj 1)) (norm_nonneg (c j))
  simpa only [mul_left_comm] using H

end MetricDifferential
end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {X : Type*} [MetricSpace X]

lemma HasTwoPointMetricDifferential.parallelogram_of_quadrilateralOn
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (u v : E) :
    p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2 := by
  have hle (u v : E) : p (u+v)^2+p (u-v)^2 ≤ 2*p u^2+2*p v^2 := by
    let z : Fin 4 → E := ![0,u,u+v,v]
    have hz : z ∈ tangentConeAt ℝ {f : Fin 4 → E | ∀ i, f i ∈ s} (fun _ => x) := by
      rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
      exact mem_univ z
    obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
    have hl (i j : Fin 4) :
        Tendsto (fun k => ‖c k‖*dist (f (x+d k i)) (f (x+d k j))) atTop (𝓝 (p (z i-z j))) := by
      apply h.scaled_pair_limit hc
      · filter_upwards [hd] with k hk
        exact hk i
      · filter_upwards [hd] with k hk
        exact hk j
      · exact tendsto_pi_nhds.mp hcd i
      · exact tendsto_pi_nhds.mp hcd j
    have hquad : ∀ᶠ k in atTop,
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 3)))^2 ≤
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 1)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 2)) (f (x+d k 3)))^2 +
        (‖c k‖*dist (f (x+d k 3)) (f (x+d k 0)))^2 := by
      filter_upwards [hd] with k hk
      have H := hQ _ (hk 0) _ (hk 1) _ (hk 2) _ (hk 3)
      simpa only [Pi.add_apply,mul_add,mul_pow] using mul_le_mul_of_nonneg_left H (sq_nonneg ‖c k‖)
    have H := le_of_tendsto_of_tendsto
      (((hl 0 2).pow 2).add ((hl 1 3).pow 2))
      (((((hl 0 1).pow 2).add ((hl 1 2).pow 2)).add ((hl 2 3).pow 2)).add ((hl 3 0).pow 2)) hquad
    have hneg : p (-u+-v) = p (u+v) := by rw [←neg_add,map_neg_eq_map]
    simpa [z,map_neg_eq_map,hneg,two_mul,add_assoc,add_left_comm,add_comm] using H
  have hf := hle u v
  have hr := hle (u+v) (u-v)
  have he₁ : (u+v)+(u-v) = (2 : ℝ) • u := by module
  have he₂ : (u+v)-(u-v) = (2 : ℝ) • v := by module
  rw [he₁,he₂,map_smul_eq_mul,map_smul_eq_mul] at hr
  norm_num at hr
  linarith
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_HilbertCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
lemma ae_restrict_of_arbitrarily_large_pieces
    {A : Type*} [MeasurableSpace A] (μ : Measure A) {s : Set A} (hs : MeasurableSet s)
    {P : A → Prop}
    (H : ∀ ε : ℝ, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ᵐ x ∂μ.restrict t, P x) :
    ∀ᵐ x ∂μ.restrict s, P x := by
  apply (ae_restrict_iff' hs).2
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t,_,ht,htμ,hP⟩ := H ε hε
  have hnull : μ {x | ¬(x ∈ t → P x)} = 0 := ae_iff.1 ((ae_restrict_iff' ht).1 hP)
  calc μ {x | ¬(x ∈ s → P x)} ≤ μ ((s \ t) ∪ {x | ¬(x ∈ t → P x)}) := by
        apply measure_mono
        intro x hx
        simp only [mem_ofPred_eq, Classical.not_imp] at hx
        by_cases hxt : x ∈ t
        · exact Or.inr (by simpa only [mem_ofPred_eq, Classical.not_imp] using And.intro hxt hx.2)
        · exact Or.inl ⟨hx.1,hxt⟩
    _ ≤ μ (s \ t) + μ {x | ¬(x ∈ t → P x)} := measure_union_le _ _
    _ ≤ 0+(ε : ENNReal) := by simpa only [hnull,add_zero,zero_add,ENNReal.ofReal_coe_nnreal] using htμ
end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_parallelogram_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2) :
    ∀ᵐ x ∂μ.restrict s, ∀ u v : E,
      metricSeminorm f x (u+v)^2+metricSeminorm f x (u-v)^2 =
        2*metricSeminorm f x u^2+2*metricSeminorm f x v^2 := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd u v
  exact (hD x hx).parallelogram_of_quadrilateralOn μ
    (fun a ha b hb c hc d hd => hQ a (hts ha) b (hts hb) c (hts hc) d (hts hd)) hxd u v
end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_distance_bound_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) :
    ∀ᵐ x ∂μ.restrict s, ∀ w : E, A * ‖w‖ ≤ B * metricSeminorm f x w := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd w
  exact (hD x hx).distance_bound μ hxd
    (fun a ha b hb => hAB a (hts ha) b (hts hb)) w
end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_chart_differential
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ p : E → Seminorm ℝ E,
      (∀ v, Measurable (fun x => p x v)) ∧
      (∀ x, LipschitzWith K (p x)) ∧
      ∀ᵐ x ∂μ.restrict s, (∀ hx : x ∈ s,
        HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
        (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p x v) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  have hJG : ∀ a ∈ s, ∀ b ∈ s, (1 : ℝ)*dist a b ≤ (J : ℝ)*dist (G a) (G b) := by
    intro a ha b hb
    have hh := hJ.le_mul_dist ⟨a,ha⟩ ⟨b,hb⟩
    change dist a b ≤ (J : ℝ)*dist (f ⟨a,ha⟩) (f ⟨b,hb⟩) at hh
    simpa only [←hdist,one_mul] using hh
  refine ⟨metricSeminorm G,fun v => measurable_metricSeminorm_apply hG v,
    fun x => metricSeminorm_lipschitz hG x,?_⟩
  have hdiff := (ae_hasCenteredMetricDifferential μ hG).filter_mono
    (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))
  filter_upwards [hdiff, ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
    ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hdx hpx hjx
  refine ⟨?_,hpx,by simpa only [one_mul] using hjx⟩
  intro hx
  have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hx⟩ : s)) (𝓝 x) :=
    continuous_subtype_val.tendsto _
  have hr := hdx.comp_tendsto hc
  change (fun y : s => dist (G (y : E)) (G ((⟨x,hx⟩ : s) : E)) -
    metricSeminorm G x ((y : E)-x)) =o[𝓝 (⟨x,hx⟩ : s)] (fun y : s => (y : E)-x) at hr
  have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hx⟩) := hdist y ⟨x,hx⟩
  simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ScalarBound
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma scalar_derivative_bound_of_metric_differential
    {s : Set E} {x : E} {F r : E → ℝ} {p : Seminorm ℝ E} {ℓ : E →L[ℝ] ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hF : HasFDerivWithinAt F ℓ s x)
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {K : ℝ} (hbound : ∀ y ∈ s, |F y-F x| ≤ K*r y) (v : E) :
    |ℓ v| ≤ K*p v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hl : Tendsto (fun j => ‖c j‖ * |F (x+d j)-F x|) atTop (𝓝 |ℓ v|) := by
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_mul] using (hF.lim hd₀ hd hcd).norm
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  apply le_of_tendsto_of_tendsto hl (hlim.const_mul K)
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [mul_left_comm] using hh

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.scalar_bound
    {s : Set E} {f : s → X} {p : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun t => μ (s ∩ closedBall (x : E) t) / μ (closedBall (x : E) t))
      (𝓝[>] 0) (𝓝 1))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F : E → ℝ} (hF : ∀ y : s, F y = u (f y))
    {ℓ : E →L[ℝ] ℝ} (hD : HasFDerivWithinAt F ℓ s x) (v : E) :
    |ℓ v| ≤ (K : ℝ)*p v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property, Asymptotics.isLittleO_map]
    change (fun y : s => dist (f y) (f x)-p ((y : E)-(x : E))) =o[𝓝 x]
      (fun y : s => (y : E)-(x : E)) at h
    convert h using 1
    · ext y
      simp only [Function.comp_apply,r,dite_eq_left y.property,Subtype.coe_eta]
    · rfl
  apply scalar_derivative_bound_of_metric_differential μ hx hD hr (v := v)
  intro y hy
  have hh := hu.dist_le_mul (f ⟨y,hy⟩) (f x)
  rw [Real.dist_eq, ←hF ⟨y,hy⟩, ←hF x] at hh
  simpa only [r,dite_eq_left hy] using hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scalarOn_lipschitzOn {s : Set E} {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith J f) {u : X → ℝ} (hu : LipschitzWith K u) :
    LipschitzOnWith (K*J) (scalarOn f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simpa only [scalarOn,dite_eq_left ha,dite_eq_left hb,Function.comp_apply,Subtype.dist_eq] using
    (hu.comp hf).dist_le_mul ⟨a,ha⟩ ⟨b,hb⟩

lemma ae_scalarOn_derivative_bound {s : Set E} (hs : MeasurableSet s) {f : s → X}
    {J : ℝ≥0} (hf : LipschitzWith J f) {p : E → Seminorm ℝ E}
    (hd : ∀ᵐ x ∂μ.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ x ∂μ.restrict s, ∀ v,
      |fderivWithin ℝ (scalarOn f u) s x v| ≤ (K : ℝ)*p x v := by
  obtain ⟨F,hF,heq⟩ := (scalarOn_lipschitzOn hf hu).extend_real
  have haediff := hF.ae_differentiableAt (μ := μ)
  filter_upwards [hd,ae_restrict_mem hs,Besicovitch.ae_tendsto_measure_inter_div μ s,
    haediff.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxs hxd hFx
  have hD : HasFDerivWithinAt (scalarOn f u) (fderivWithin ℝ (scalarOn f u) s x) s x := by
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact hFx.differentiableWithinAt.congr heq (heq hxs)
  intro v
  apply (hx hxs).scalar_bound μ hxd hu _ hD v
  intro y
  simp only [scalarOn,dite_eq_left y.property,Subtype.coe_eta]
end SharpIntegralFillings.MetricDifferentiation

open Set MeasureTheory
open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ExactMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings.MetricDifferentiation
open MeasureTheory Set Metric Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

lemma chart_matrix_determinant_bound {n : ℕ}
    {s : Set (Euc n)} (hs : MeasurableSet s) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (p : Euc n → Seminorm ℝ (Euc n))
    (hpm : ∀ v, Measurable (fun x => p x v))
    (hpLip : ∀ x, LipschitzWith K (p x))
    (hae : ∀ᵐ x ∂volume.restrict s,
      (∀ hx : x ∈ s, HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
      (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
      (∀ v, ‖v‖ ≤ (J : ℝ)*p x v)) :
    let P := fun x => polarizationMatrix (p x) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (∀ i j, Measurable (fun x => P x i j)) ∧
    (∀ᵐ x ∂volume.restrict s, (P x).PosDef) ∧
    (∀ᵐ x ∂volume.restrict s, Real.sqrt (P x).det ≤ (K : ℝ)^n) ∧
    ∀ π : Fin n → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ x ∂volume.restrict s,
        |(Matrix.of fun i j =>
          fderivWithin ℝ (scalarOn f (π i)) s x (EuclideanSpace.single j 1)).det| ≤
              Real.sqrt (P x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hzero : ∀ᵐ x ∂volume.restrict s, ∀ v, p x v = 0 ↔ v = 0 := by
    filter_upwards [hae] with x hx v
    constructor
    · intro hv
      have hn := hx.2.2 v
      rw [hv,mul_zero] at hn
      exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg v))
    · rintro rfl
      exact map_zero (p x)
  refine ⟨measurable_polarizationMatrix p b hpm,?_,?_,?_⟩
  · filter_upwards [hae,hzero] with x hx hz
    exact polarizationMatrix_posDef b (p x) hz hx.2.1
  · filter_upwards [hae,hzero] with x hx hz
    apply sqrt_det_le_pow_of_quadratic_bound _
      (polarizationMatrix_posDef b (p x) hz hx.2.1).posSemidef K.coe_nonneg
    intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hrepr : b.repr w = v := by ext j; simp [b,w]
    have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
      simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
    rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
    simpa only [dist_zero_right,map_zero,Real.norm_eq_abs, abs_of_nonneg (apply_nonneg (p x) w)] using (hpLip x).dist_le_mul w 0
  intro π hπ
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := hae.mono fun x hx => hx.1
  have hrows : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ p x v := by
    rw [eventually_all]
    intro i
    simpa only [NNReal.coe_one,one_mul] using ae_scalarOn_derivative_bound volume hs hf hdiff (hπ i)
  filter_upwards [hae,hzero,hrows] with x hx hz hrow
  apply abs_det_le_sqrt_det_of_posDef _ _ (polarizationMatrix_posDef b (p x) hz hx.2.1)
  intro i v
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by
    ext j
    simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
  convert hrow i w using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = w := by
    convert b.sum_repr w using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.of_apply, dotProduct, mul_comm]
end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings
open MeasureTheory Set Filter

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

theorem exists_exact_quadratic_mass (hX : IsCAT0 X) (hC : IsMetricCurrent C.action) :
    ∃ P : Euc k → Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, Measurable (fun z => P z i j)) ∧
      (∀ᵐ z ∂volume.restrict C.domain, (P z).PosDef) ∧
      Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
        (volume.restrict C.domain) ∧
      IsFiniteMeasure (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      Controls C.action (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      (∀ (ν : Measure X), IsFiniteMeasure ν → Controls C.action ν →
        C.majorantMeasure (fun z => Real.sqrt (P z).det) ≤ ν) ∧
      ∃ p : Euc k → Seminorm ℝ (Euc k),
        P = (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) ∧
        (∀ v, Measurable (fun z => p z v)) ∧
        ∀ᵐ z ∂volume.restrict C.domain,
          (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
            C.domain C.param (p z) ⟨z,hz⟩) ∧
          (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
          (∀ v, p z v = 0 ↔ v = 0) := by
  obtain ⟨K,L,hK,hL⟩ := C.bilipschitz
  obtain ⟨p,hpm,hpLip,hae⟩ := MetricDifferentiation.exists_hilbertian_chart_differential
    volume C.borel C.bounded.measure_lt_top.ne hK hL
    (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d))
  let P := fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  obtain ⟨hPm,hP,hJ,hdet⟩ := MetricDifferentiation.chart_matrix_determinant_bound
    C.borel hK p hpm hpLip hae
  have hJm : Measurable (fun z => Real.sqrt (P z).det) := by
    apply Measurable.sqrt
    simp only [Matrix.det_apply']
    fun_prop
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
      (volume.restrict C.domain) := by
    apply (C.integrable.abs.mul_const ((K : ℝ)^k)).mono'
      (C.integrable.abs.aestronglyMeasurable.mul hJm.aestronglyMeasurable)
    filter_upwards [hJ] with z hz
    change ‖|(C.multiplicity z : ℝ)| * Real.sqrt (P z).det‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  refine ⟨P,hPm,hP,hρ,densityPush_finite _ _ hρ,?_,?_,p,rfl,hpm,?_⟩
  · apply C.majorant_controls hρ (Eventually.of_forall fun z => Real.sqrt_nonneg _)
    exact hdet
  · intro ν hνfin hν
    let := hνfin
    apply C.hilbert_mass_measure_le hX hC hν p
    filter_upwards [hae] with z hz
    refine ⟨hz.1,?_,hz.2.1⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _
  · filter_upwards [hae] with z hz
    refine ⟨hz.1,hz.2.1,?_⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_JacobianBound
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
open Matrix
open scoped MatrixOrder

lemma abs_det_le_prod_mul_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ K i * Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ (∏ i, K i) * Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ ∏ i, K i := by
    apply (abs_det_le_prod_row_norm _).trans
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i _
    apply row_norm_le_of_dot_bound_const _ (hK i)
    intro v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ (∏ i, K i)*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = (∏ i, K i) * Real.sqrt P.det := by rw [hQdet]

end SharpIntegralFillings

namespace SharpIntegralFillings.IntegerChart
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_jacobian_bound_quadratic
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0) (hπ : ∀ i, LipschitzWith (K i) (π i)) :
    ∀ᵐ z ∂volume.restrict C.domain,
      |C.jacobian π z| ≤ (∏ i, (K i : ℝ)) *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hrows : ∀ᵐ z ∂volume.restrict C.domain, ∀ i v,
      |fderivWithin ℝ (C.scalar (π i)) C.domain z v| ≤ K i * p z v := by
    rw [eventually_all]
    intro i
    exact MetricDifferentiation.ae_scalarOn_derivative_bound volume C.borel hL
      (hp.mono fun z hz => hz.1) (hπ i)
  filter_upwards [hp,hrows] with z hz hrow
  apply abs_det_le_prod_mul_sqrt_det_of_posDef _ _
    (polarizationMatrix_posDef b (p z) hz.2.2 hz.2.1) _ (fun i => (K i).coe_nonneg)
  intro i v
  let w : Euc k := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by ext j; simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p z) b).mulVec v = (p z w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p z) hz.2.2 hz.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p z) w)]
  convert hrow i w using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = w := by
    convert b.sum_repr w using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul,smul_eq_mul,dotProduct,mul_comm]

end SharpIntegralFillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakCompactness
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IsMetricCurrent.first_difference_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (π : Fin k → X → ℝ) (K : ℝ≥0) (hπ : ∀ i, LipschitzWith K (π i))
    (ε : ℝ≥0) (hε : ∀ x, |b x - c x| ≤ ε) :
    |T b π - T c π| ≤ (K : ℝ) ^ k * ε * mass T := by
  have hsub : BoundedLip (fun x => b x - c x) := by
    simpa [sub_eq_add_neg] using hb.add (hc.const_mul (-1))
  have heq : T (fun x => b x - c x) π = T b π - T c π := by
    simpa [sub_eq_add_neg] using hT.linearFirst b c π 1 (-1) hb hc (fun i => ⟨K, hπ i⟩)
  rw [← heq]
  simpa using hT.mass_bound_uniform hsub (fun _ => K) hπ hε

omit [MeasurableSpace X] [BorelSpace X] in
lemma TestClass.boundedLip {d K : ℕ} (p : TestClass (X := X) d K) :
    BoundedLip (p.val.1 : X → ℝ) :=
  ⟨⟨K, p.property.1⟩, K, fun x => (p.val.1.norm_coe_le_norm x).trans p.property.2.1⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma admissible_mem_testClass {d : ℕ} {b : X → ℝ} {π : Fin d → X → ℝ}
    (h : Admissible b π) :
    ∃ (K : ℕ) (p : TestClass (X := X) d K),
      (p.val.1 : X → ℝ) = b ∧ (fun i => (p.val.2 i : X → ℝ)) = π := by
  obtain ⟨⟨Kb, hb⟩, B, hB⟩ := h.1
  choose Ks hKs using h.2
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let L : ℝ≥0 := max Kb (max Bn (Finset.univ.sup Ks))
  obtain ⟨K, hK⟩ := exists_nat_gt L
  have hbK : Kb ≤ (K : ℝ≥0) := (le_max_left _ _).trans hK.le
  have hBK : Bn ≤ (K : ℝ≥0) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hK.le
  have hπK (i : Fin d) : Ks i ≤ (K : ℝ≥0) :=
    ((Finset.le_sup (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hK.le
  let p : C(X, ℝ) × (Fin d → C(X, ℝ)) :=
    (⟨b, hb.continuous⟩, fun i => ⟨π i, (hKs i).continuous⟩)
  refine ⟨K, ⟨p, ⟨hb.weaken hbK, ?_, fun i => (hKs i).weaken (hπK i)⟩⟩, rfl, rfl⟩
  apply (p.1.norm_le (by positivity)).mpr
  intro x
  exact (hB x).trans ((le_max_left B 0).trans hBK)

end Foundations

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_CountableTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma IsMetricCurrent.testClass_continuous {d : ℕ} {T : Functional X d}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (d := d) (K := K) T) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hcoord : Tendsto (fun n => T p.val.1 (fun i => (ps n).val.2 i)) atTop
      (𝓝 (T p.val.1 (fun i => p.val.2 i))) := by
    apply hT.sequentialContinuity _ _ _ p.boundedLip
    · intro i
      exact ⟨K,fun n => (ps n).property.2.2 i⟩
    · intro i x
      have hc : Continuous (fun q : TestClass (X := X) d K => q.val.2 i x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
  have hd : Tendsto (fun n => dist (ps n) p) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hp
  have hbnd (n : ℕ) :
      dist (T p.val.1 (fun i => (ps n).val.2 i))
        (T (ps n).val.1 (fun i => (ps n).val.2 i)) ≤
      ((K:ℝ)^d * mass T) * dist (ps n) p := by
    have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip (ps n).boundedLip
      (fun i => (ps n).val.2 i) K (ps n).property.2.2 (nndist (ps n) p) (fun x => ?_)
    · simpa only [Real.dist_eq,NNReal.coe_natCast,coe_nndist,mul_assoc,mul_comm,mul_left_comm]
        using hh
    · have h := (ContinuousMap.dist_apply_le_dist (f := (ps n).val.1) (g := p.val.1) x).trans
        (le_max_left (dist (ps n).val.1 p.val.1) (dist (ps n).val.2 p.val.2))
      change dist ((ps n).val.1 x) (p.val.1 x) ≤ dist (ps n) p at h
      simpa only [coe_nndist,Real.dist_eq,abs_sub_comm] using h
  apply tendsto_of_tendsto_of_dist hcoord
  exact squeeze_zero (fun n => dist_nonneg) hbnd (by simpa using hd.const_mul ((K:ℝ)^d * mass T))

end SharpIntegralFillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_MassTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma TestClass.continuous_integral_abs (d K : ℕ) (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (fun p : TestClass (X := X) d K => ∫ x, |p.val.1 x| ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => (K:ℝ))
  · intro p
    exact p.val.1.continuous.abs.measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_abs] using (p.val.1.norm_coe_le_norm x).trans p.property.2.1
  · exact integrable_const _
  · exact Eventually.of_forall fun x => by fun_prop

theorem exists_countable_mass_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, BoundedLip (b K j) ∧ ∀ i, LipschitzWith 1 (π K j i)) ∧
      ∀ T : Functional X d, IsMetricCurrent T →
        ∀ μ : Measure X, IsFiniteMeasure μ →
          (∀ K j, |T (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ) → Controls T μ := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (UnitTestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.val.1,fun K j i => (p K j).val.val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).val.boundedLip,(p K j).property⟩
  · intro T hT μ hμ he b π hb hπ
    let := hμ
    obtain ⟨K,q,hbq,hπq⟩ := admissible_mem_testClass (show Admissible b π from ⟨hb,fun i => ⟨1,hπ i⟩⟩)
    let q' : UnitTestClass (X := X) d K := ⟨q,by
      intro i
      have hi : (q.val.2 i : X → ℝ) = π i := congrFun hπq i
      simpa only [hi] using hπ i⟩
    have hh : |TestClass.eval T q'.val| ≤ ∫ x, |q'.val.val.1 x| ∂μ := by
      apply (hp K).induction_on (p := fun r : UnitTestClass (X := X) d K =>
        |TestClass.eval T r.val| ≤ ∫ x, |r.val.val.1 x| ∂μ) q'
      · apply isClosed_le
        · exact ((IsMetricCurrent.testClass_continuous hT K).comp continuous_subtype_val).abs
        · exact (TestClass.continuous_integral_abs d K μ).comp continuous_subtype_val
      · intro j
        exact he K j
    simpa only [q',TestClass.eval,hbq,hπq] using hh

theorem ae_controls_of_testwise_bound {A : Type*} [MeasurableSpace A] (ν : Measure A)
    {d : ℕ} {T : A → Functional X d} {μ : A → Measure X}
    (hT : ∀ᵐ a ∂ν, IsMetricCurrent (T a))
    (hμ : ∀ᵐ a ∂ν, IsFiniteMeasure (μ a))
    (hb : ∀ b π, BoundedLip b → (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ a ∂ν, |T a b π| ≤ ∫ x, |b x| ∂μ a) :
    ∀ᵐ a ∂ν, Controls (T a) (μ a) := by
  obtain ⟨b,π,ht,hd⟩ := exists_countable_mass_tests (X := X) d
  have hc : ∀ᵐ a ∂ν, ∀ K j, |T a (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ a :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => hb _ _ (ht K j).1 (ht K j).2
  filter_upwards [hT,hμ,hc] with a hta hma hca
  exact hd _ hta _ hma hca

end SharpIntegralFillings.Foundations
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_EuclideanSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Prism

lemma split_measurePreserving (k : ℕ) : MeasurePreserving (split k) := by
  have h := (MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ))
    (PiLp.volume_preserving_toLp (Fin k))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (k+1) => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (k+1))))
  convert h using 1
  · funext z
    apply Prod.ext
    · rfl
    · ext j
      simp [Function.comp_def,MeasurableEquiv.piFinSuccAbove_apply,Fin.tail]
  · rfl

lemma split_symm_measurePreserving (k : ℕ) : MeasurePreserving (split k).symm := by
  exact MeasurePreserving.symm (split k).toHomeomorph.toMeasurableEquiv
    (split_measurePreserving k)

lemma integral_split (k : ℕ) (f : Euc (k+1) → ℝ) :
    ∫ z, f z = ∫ p : ℝ × Euc k, f ((split k).symm p) := by
  exact ((split_symm_measurePreserving k).integral_comp (split k).symm.toHomeomorph.measurableEmbedding f).symm

lemma split_single_succ (k : ℕ) (j : Fin k) :
    split k (EuclideanSpace.single j.succ 1) = (0,EuclideanSpace.single j 1) := by
  ext <;> simp

end SharpIntegralFillings.Prism

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateChart
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_integrable_coordinateMultiplicity : ∀ᵐ t : ℝ,
    Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator (fun z => (C.multiplicity z:ℝ))) :=
    (integrable_indicator_iff C.borel).mpr C.integrable
  have hip : Integrable (fun p : ℝ × Euc k =>
      C.domain.indicator (fun z => (C.multiplicity z:ℝ)) ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  have heq : (C.coordinateDomain t).indicator (fun z => (C.multiplicity (coordinateLayer k t z):ℝ)) =
      fun z => C.domain.indicator (fun w => (C.multiplicity w:ℝ)) ((Prism.split k).symm (t,z)) := by
    funext z
    change (C.coordinateDomain t).indicator _ z = C.domain.indicator _ (coordinateLayer k t z)
    by_cases hz : coordinateLayer k t z ∈ C.domain
    · rw [indicator_of_mem (show z ∈ C.coordinateDomain t from hz),indicator_of_mem hz]
    · rw [indicator_of_notMem (show z ∉ C.coordinateDomain t from hz),indicator_of_notMem hz]
  rw [heq]
  exact ht

end SharpIntegralFillings.IntegerChart

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateDerivative
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_scalar_eq (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) (f : X → ℝ)
    {z : Euc k} (hz : z ∈ C.coordinateDomain t) :
    (C.coordinateSlice t ht).scalar f z = C.scalar f (coordinateLayer k t z) := by
  rw [(C.coordinateSlice t ht).scalar_eq hz,C.scalar_eq hz]
  rfl

lemma coordinateSlice_fderiv (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) {f : X → ℝ} {F : Euc (k+1) → ℝ}
    (heq : EqOn F (C.scalar f) C.domain) {z : Euc k}
    (hz : z ∈ C.coordinateDomain t) (hF : DifferentiableAt ℝ F (coordinateLayer k t z))
    (hu : UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z))
    (hv : UniqueDiffWithinAt ℝ (C.coordinateDomain t) z) (j : Fin k) :
    (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
      (EuclideanSpace.single j 1) =
    (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
      (EuclideanSpace.single j.succ 1) := by
  have hFC : fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z) =
      fderiv ℝ F (coordinateLayer k t z) :=
    (hF.hasFDerivAt.hasFDerivWithinAt.congr (fun w hw => (heq hw).symm) (heq hz).symm).fderivWithin hu
  let L : Euc k →L[ℝ] Euc (k+1) :=
    (Prism.split k).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Euc k))
  have hl : HasFDerivAt (coordinateLayer k t) L z := by
    exact (Prism.split k).symm.hasFDerivAt.comp z
      ((hasFDerivAt_const (𝕜 := ℝ) t z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have hFS : fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z =
      (fderiv ℝ F (coordinateLayer k t z)).comp L := by
    apply HasFDerivWithinAt.fderivWithin _ hv
    apply (hF.hasFDerivAt.comp z hl).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.coordinateSlice_scalar_eq t ht f hw]
      exact (heq hw).symm
    · rw [C.coordinateSlice_scalar_eq t ht f hz]
      exact (heq hz).symm
  rw [hFC,hFS,ContinuousLinearMap.comp_apply]
  have hb : L (EuclideanSpace.single j 1) = EuclideanSpace.single j.succ 1 := by
    apply (Prism.split k).injective
    change Prism.split k ((Prism.split k).symm (0,EuclideanSpace.single j 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,Prism.split_single_succ]
  rw [hb]

lemma ae_coordinateSlice_fderiv {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨F,hF,heq⟩ := (C.scalar_lipschitzOn hL hf).extend_real
  have hfull : ∀ᵐ w : Euc (k+1), w ∈ C.domain →
      DifferentiableAt ℝ F w ∧ UniqueDiffWithinAt ℝ C.domain w := by
    filter_upwards [hF.ae_differentiableAt (μ := volume),
      (ae_restrict_iff' C.borel).mp (ae_uniqueDiffWithinAt volume C.domain)] with w hw hu
    exact fun hm => ⟨hw,hu hm⟩
  have hp := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hfull
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with t ht
  intro hi
  have ht' : ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      DifferentiableAt ℝ F (coordinateLayer k t z) ∧
      UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z) :=
    (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht
  filter_upwards [ht',ae_restrict_mem (C.measurableSet_coordinateDomain t),
    ae_uniqueDiffWithinAt volume (C.coordinateDomain t)] with z hz hm hu
  exact fun j => C.coordinateSlice_fderiv t hi (fun w hw => (heq hw).symm) hm hz.1 hz.2 hu j

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_coordinateSliceTotal_eq : ∀ᵐ t : ℝ,
    ∃ ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)),
      C.coordinateSliceTotal t = C.coordinateSlice t ht := by
  filter_upwards [C.ae_integrable_coordinateMultiplicity] with t ht
  exact ⟨ht,dite_eq_left ht⟩

end SharpIntegralFillings.IntegerChart
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateIntegral
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_coordinateSlice_jacobian (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      (C.coordinateSlice t ht).jacobian π z = C.coordinateMinor π (coordinateLayer k t z) := by
  have hall : ∀ i, ∀ᵐ t : ℝ, ∀ ht, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar (π i)) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar (π i)) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    exact C.ae_coordinateSlice_fderiv hK
  filter_upwards [ae_all_iff.mpr hall] with t ht
  intro hi
  filter_upwards [ae_all_iff.mpr (fun i => ht i hi)] with z hz
  apply congrArg Matrix.det
  ext i j
  exact hz i j

lemma ae_coordinate_minor_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (π : Fin k → X → ℝ) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Matrix.vecCons u π) z = C.coordinateMinor π z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel] with z hz hm
  have hd : fderivWithin ℝ (C.scalar u) C.domain z =
      (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap := by
    apply HasFDerivWithinAt.fderivWithin _ hz
    apply (((ContinuousLinearMap.fst ℝ ℝ (Euc k)).hasFDerivAt).comp z
      (Prism.split k).hasFDerivAt).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.scalar_eq hw,hu w hw]
      rfl
    · rw [C.scalar_eq hm,hu z hm]
      rfl
  let A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ := Matrix.of fun i j =>
    (fderivWithin ℝ (C.scalar (Matrix.vecCons u π i)) C.domain z) (EuclideanSpace.single j 1)
  have ha0 : ∀ j, A 0 j = if j=0 then 1 else 0 := by
    intro j
    dsimp only [A,Matrix.of_apply,Matrix.cons_val_zero]
    rw [hd]
    cases j using Fin.cases with
    | zero => simp [ContinuousLinearMap.comp_apply]
    | succ j => simp [ContinuousLinearMap.comp_apply]
  change A.det = _
  rw [Matrix.det_succ_row_zero]
  simp only [ha0,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,
    Fin.val_zero,pow_zero,one_mul]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply,Fin.succAbove_zero,A,Matrix.of_apply,Matrix.cons_val_succ]

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinate_indicator (g : Euc (k+1) → ℝ) (t : ℝ) :
    (fun z => C.domain.indicator g ((Prism.split k).symm (t,z))) =
      (C.coordinateDomain t).indicator (fun z => g (coordinateLayer k t z)) := by
  funext z
  change C.domain.indicator g (coordinateLayer k t z) = _
  by_cases hz : coordinateLayer k t z ∈ C.domain
  · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ C.coordinateDomain t from hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ C.coordinateDomain t from hz)]

lemma coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∫ w in C.domain, g w = ∫ t : ℝ, ∫ z in C.coordinateDomain t,
      g (coordinateLayer k t z) := by
  rw [←integral_indicator C.borel,Prism.integral_split]
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  change (∫ p : ℝ × Euc k, C.domain.indicator g ((Prism.split k).symm p) ∂volume.prod volume) = _
  rw [integral_prod _ hip]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    Integrable (fun t : ℝ => ∫ z in C.coordinateDomain t, g (coordinateLayer k t z)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  convert hip.integral_prod_left using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinateMinor {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun w => (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w)
      (volume.restrict C.domain) := by
  have ha : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i
  apply (C.integrable_action_integrand h.1 ha).congr
  filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
  rw [hz]

lemma ae_coordinateSliceTotal_action {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action b π =
      ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) := by
  filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_coordinateSlice_jacobian π h.2] with t ht hj
  obtain ⟨hi,heq⟩ := ht
  rw [heq,action,ite_eq_left h]
  apply integral_congr_ae
  filter_upwards [hj hi,ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz hm
  change (C.multiplicity (coordinateLayer k t z):ℝ)*
    (C.coordinateSlice t hi).scalar b z*(C.coordinateSlice t hi).jacobian π z = _
  rw [C.coordinateSlice_scalar_eq t hi b hm,hz]

theorem coordinateSlice_action_integral {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    C.action b (Matrix.vecCons u π) = ∫ t : ℝ, (C.coordinateSliceTotal t).action b π := by
  have ha : Admissible b (Matrix.vecCons u π) := ⟨h.1,fun i => by
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i⟩
  rw [action,ite_eq_left ha]
  calc
    _ = ∫ w in C.domain, (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w := by
      apply integral_congr_ae
      filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
      rw [hz]
    _ = ∫ t : ℝ, ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) :=
      C.coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)
    _ = _ := integral_congr_ae (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

lemma coordinateSlice_action_integrable {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun t : ℝ => (C.coordinateSliceTotal t).action b π) :=
  (C.integrable_coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)).congr
    (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

end SharpIntegralFillings.IntegerChart
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_CoordinateCoarea
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
lemma majorant_test_bound {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hb : BoundedLip b)
    (hπ : ∀ i, LipschitzWith 1 (π i))
    (hdet : ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    |C.action b π| ≤ ∫ x, |b x| ∂C.majorantMeasure J := by
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring
end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_integrable_coordinate {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∀ᵐ t : ℝ, Integrable (fun z => g (coordinateLayer k t z))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  simpa only [C.coordinate_indicator g t] using ht

lemma ae_coordinate_of_ae {p : Euc (k+1) → Prop}
    (hp : ∀ᵐ w ∂volume.restrict C.domain, p w) :
    ∀ᵐ t : ℝ, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), p (coordinateLayer k t z) := by
  have hf := (ae_restrict_iff' C.borel).mp hp
  have hm := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hf
  filter_upwards [Measure.ae_ae_of_ae_prod hm] with t ht
  exact (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem coordinate_coarea_majorant {J : Euc (k+1) → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z:ℝ)| * J z) (volume.restrict C.domain))
    (hJ : ∀ z, 0 ≤ J z)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤ J z) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = ∫ z in C.domain, |(C.multiplicity z:ℝ)| * J z := by
  let G : ℝ → ℝ := fun t => ∫ z in C.coordinateDomain t,
    |(C.multiplicity (coordinateLayer k t z):ℝ)| * J (coordinateLayer k t z)
  let μ : ℝ → Measure X := fun t => (C.coordinateSliceTotal t).majorantMeasure
    (fun z => J (coordinateLayer k t z))
  have hsliceρ : ∀ᵐ t : ℝ,
      Integrable (fun z => |((C.coordinateSliceTotal t).multiplicity z:ℝ)| *
        J (coordinateLayer k t z)) (volume.restrict (C.coordinateSliceTotal t).domain) := by
    filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_integrable_coordinate hρ] with t ht hρt
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    exact hρt
  have hfin : ∀ᵐ t : ℝ, IsFiniteMeasure (μ t) := by
    filter_upwards [hsliceρ] with t ht
    exact densityPush_finite _ _ ht
  have hcontrols : ∀ᵐ t : ℝ, Controls (C.coordinateSliceTotal t).action (μ t) := by
    apply Foundations.ae_controls_of_testwise_bound volume
      (Eventually.of_forall fun t => (C.coordinateSliceTotal t).action_isMetricCurrent) hfin
    intro b π hb hπ
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,
      C.ae_coordinateSlice_jacobian π (fun i => ⟨1,hπ i⟩),
      C.ae_coordinate_of_ae (hdet π hπ)] with t hρt ht hj hdt
    apply (C.coordinateSliceTotal t).majorant_test_bound hρt
      (Eventually.of_forall fun z => hJ (coordinateLayer k t z)) b π hb hπ
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    filter_upwards [hj hi,hdt] with z hz hd
    rw [hz]
    exact hd
  have hm : ∀ᵐ t : ℝ, (μ t).real univ = G t := by
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,hfin] with t hρt ht hμt
    let := hμt
    calc
      (μ t).real univ = ∫ x, (1:ℝ) ∂μ t := by simp
      _ = ∫ z in (C.coordinateSliceTotal t).domain,
          |((C.coordinateSliceTotal t).multiplicity z:ℝ)| * J (coordinateLayer k t z) := by
        rw [show μ t = (C.coordinateSliceTotal t).majorantMeasure
          (fun z => J (coordinateLayer k t z)) from rfl,majorantMeasure,
          integral_densityPush _ (C.coordinateSliceTotal t).measurable_paramExtended hρt
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (hJ _)) continuous_const]
        simp only [mul_one]
      _ = G t := by
        obtain ⟨hi,heq⟩ := ht
        rw [heq]
        rfl
  refine ⟨G,C.integrable_coordinate_setIntegral hρ,fun t =>
    integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (hJ _)),?_,?_⟩
  · filter_upwards [hcontrols,hfin,hm] with t hct hft hmt
    rw [←hmt]
    exact mass_le_measure hft hct
  · exact (C.coordinate_setIntegral hρ).symm

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem sharp_coordinate_coarea_majorant (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = K * mass C.action := by
  obtain ⟨P,hPm,hP,hρ,hfin,hctrl,hle,p,hpP,hpm,hp⟩ :=
    C.exists_exact_quadratic_mass hX C.action_isMetricCurrent
  let μ := C.majorantMeasure (fun z => Real.sqrt (P z).det)
  let : IsFiniteMeasure μ := hfin
  have hμmass : mass C.action = μ.real univ := by
    apply le_antisymm (mass_le_measure hfin hctrl)
    obtain ⟨ν,hνfin,hν,hνmass⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
    let := hνfin
    rw [hνmass]
    exact ENNReal.toReal_mono (measure_ne_top ν univ) (hle ν hνfin hν univ)
  have hm : mass C.action = ∫ z in C.domain,
      |(C.multiplicity z:ℝ)| * Real.sqrt (P z).det := by
    rw [hμmass]
    calc
      μ.real univ = ∫ x, (1:ℝ) ∂μ := by simp
      _ = _ := by
        rw [show μ = C.majorantMeasure (fun z => Real.sqrt (P z).det) from rfl,
          majorantMeasure,integral_densityPush _ C.measurable_paramExtended hρ
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
            continuous_const]
        simp only [mul_one]
  have hρK : Integrable (fun z => |(C.multiplicity z:ℝ)| *
      ((K:ℝ) * Real.sqrt (P z).det)) (volume.restrict C.domain) := by
    convert hρ.const_mul (K:ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    ring
  have hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤
        (K:ℝ) * Real.sqrt (P z).det := by
    intro π hπ
    have hh := C.ae_jacobian_bound_quadratic p hp (Matrix.vecCons u π)
      (Matrix.vecCons K (fun _ => 1)) (fun i => by
        cases i using Fin.cases with
        | zero => exact hK
        | succ i => exact hπ i)
    filter_upwards [hh,C.ae_coordinate_minor_eq hu π] with z hz heq
    rw [heq] at hz
    simpa only [hpP,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      NNReal.coe_one,Finset.prod_const_one,mul_one] using hz
  obtain ⟨G,hG,hG0,hGm,hGI⟩ := C.coordinate_coarea_majorant hρK
    (fun z => mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)) hdet
  refine ⟨G,hG,hG0,hGm,?_⟩
  rw [hGI,hm,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

end SharpIntegralFillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ComponentMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma finite_sum_measure_of_summable_total {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hs : Summable (fun i => (μ i).real univ)) : IsFiniteMeasure (Measure.sum μ) := by
  constructor
  have heq : (Measure.sum μ) univ = ENNReal.ofReal (∑' i, (μ i).real univ) := by
    rw [Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.ofReal_tsum_of_nonneg (fun i => measureReal_nonneg) hs]
    congr 1
    funext i
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ i) univ)).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

lemma controls_sum (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (BorelCoefficients.integrable_boundedLip _ hb).abs
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbi.summable_integral
  have hsa : Summable (fun i => S i b π) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hμ i b π hb hπ)
  rw [hT b π,integral_sum_measure hbi]
  calc
    |∑' i, S i b π| ≤ ∑' i, |S i b π| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => S i b π) hsa.norm)
    _ ≤ ∑' i, ∫ x, |b x| ∂μ i := hsa.abs.tsum_le_tsum (fun i => hμ i b π hb hπ) hs

end SumControls

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Summation
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

lemma summable_actions_all {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i)))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases hab : Admissible b π
  · exact summable_actions_of_summable_masses hT hS hab
  · simp only [fun i => (hT i).offDomain b π hab,summable_zero]

theorem isMetricCurrent_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_actions_all hT hS
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [fun i => (hT i).offDomain b π hab,tsum_zero]
  · intro b c π a d hb hc hπ
    simp only [fun i => (hT i).linearFirst b c π a d hb hc hπ]
    rw [((hs b π).mul_left a).tsum_add ((hs c π).mul_left d)]
    simp only [tsum_mul_left]
  · intro b π j f a c hab hf
    simp only [fun i => (hT i).linearCoord b π j f a c hab hf]
    rw [((hs b π).mul_left a).tsum_add ((hs b (Function.update π j f)).mul_left c)]
    simp only [tsum_mul_left]
  · intro b π πs hb hπs hlim
    choose K hK using hπs
    obtain ⟨M,hM⟩ := hb.2
    apply tendsto_tsum_of_dominated_convergence
      (hS.mul_left ((∏ j, (K j : ℝ)) * M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i => (hT i).mass_bound_uniform hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
    let : ∀ i, IsFiniteMeasure (μ i) := hfin
    have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
    let := finite_sum_measure_of_summable_total μ hm
    exact ⟨Measure.sum μ,inferInstance,controls_sum hμ (fun _ _ => rfl)⟩

lemma mass_tsum_le {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    mass (fun b π => ∑' i, T i b π) ≤ ∑' i, mass (T i) := by
  choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
  let := finite_sum_measure_of_summable_total μ hm
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (Measure.sum μ)) (controls_sum hμ (fun _ _ => rfl))).trans_eq
  rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_toReal_eq]
  · exact tsum_congr (fun i => (heq i).symm)
  · intro i
    exact measure_ne_top _ _

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_ScalarCoarea
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_u_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (t : ℝ) (hi : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)))
    (z : (C.coordinateSlice t hi).domain) : u ((C.coordinateSlice t hi).param z) = t := by
  have h := hu (coordinateLayer k t z) z.property
  change u ((C.coordinateSlice t hi).param z) = _ at h
  simpa only [coordinateLayer,ContinuousLinearEquiv.apply_symm_apply] using h

lemma ae_coordinateSliceTotal_weighted {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π)
    (φ : ℝ → ℝ) (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action (fun x => φ (u x)*b x) π =
      φ t * (C.coordinateSliceTotal t).action b π := by
  filter_upwards [C.ae_coordinateSliceTotal_eq] with t ht
  obtain ⟨hi,heq⟩ := ht
  rw [heq]
  have hab : Admissible (fun x => φ (u x)*b x) π := ⟨hφ.mul h.1,h.2⟩
  rw [action,ite_eq_left hab,action,ite_eq_left h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz
  rw [(C.coordinateSlice t hi).scalar_eq hz,(C.coordinateSlice t hi).scalar_eq hz,
    C.coordinateSlice_u_eq hu t hi ⟨z,hz⟩]
  ring

end SharpIntegralFillings.IntegerChart
namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinateSliceTotal_image_subset (t : ℝ) :
    (C.coordinateSliceTotal t).image ⊆ C.image := by
  classical
  unfold coordinateSliceTotal
  split_ifs with hi
  · rintro x ⟨z,rfl⟩
    exact ⟨⟨coordinateLayer k t z,z.property⟩,rfl⟩
  · rintro x ⟨z,_⟩
    exact False.elim z.property

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem exists_scalar_coarea_oai (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass C.action ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        C.action b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨D,hDd,_hDsub,hDu,hDm,hDI,hDact⟩ := C.exists_scalar_straightened_charts hK
  choose G hG hG0 hGm hGI using fun i => (D i).sharp_coordinate_coarea_majorant hX hK (hDu i)
  let Q i t := (D i).coordinateSliceTotal t
  let S : ℝ → Functional X k := fun t b π => ∑' i, (Q i t).action b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    simp_rw [hGI]
    exact hDm.mul_left (K:ℝ)
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t).action) := by
    filter_upwards [hGa,ae_all_iff.mpr hGm] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) hm
  have hQd (t : ℝ) : Pairwise (fun i j => Disjoint (Q i t).image (Q j t).image) := by
    intro i j hij
    exact (hDd hij).mono ((D i).coordinateSliceTotal_image_subset t)
      ((D j).coordinateSliceTotal_image_subset t)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hGm] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (Q i t).action_isMetricCurrent) hqt,
      ⟨fun i => Q i t,hQd t,fun i => (Q i t).action_isMetricCurrent,hqt,fun _ _ => rfl⟩,?_⟩
    exact (mass_tsum_le (fun i => (Q i t).action_isMetricCurrent) hqt).trans
      (hqt.tsum_le_tsum hmt hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    simp_rw [hGI]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hDI K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => (Q i t).action b π) :=
      (D i).coordinateSlice_action_integrable hK (hDu i) hab
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖(Q i t).action b π‖ ≤ A * G i t := by
      filter_upwards [hGm i] with t ht
      rw [Real.norm_eq_abs]
      exact ((Q i t).action_isMetricCurrent.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖(Q i t).action b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [show C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π)
      from hDact b π hab]
    simp_rw [fun i => (D i).coordinateSlice_action_integral hK (hDu i) hab]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i =>
      (D i).ae_coordinateSliceTotal_weighted (hDu i) hab φ hφ)] with t ht
    change (∑' i, (Q i t).action (fun x => φ (u x)*b x) π) = φ t * ∑' i, (Q i t).action b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end SharpIntegralFillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea_oai.{u_1} := @OAI.SharpIntegralFillings.IntegerChart.exists_scalar_coarea_oai.{u_1}
