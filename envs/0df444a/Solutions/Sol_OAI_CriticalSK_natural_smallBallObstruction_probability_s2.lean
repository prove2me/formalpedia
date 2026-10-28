-- Prove2me | solution 1 for OAI.CriticalSK.natural_smallBallObstruction_probability_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:03:56.874243+00:00
-- url     : https://prove2.me/submissions/b858a41d-a3af-42fb-94b6-036924d2bf4b

import Mathlib
import Definitions.Def_CriticalSKMixing
import Definitions.Def_OAIQ074C000
import Theorems.Thm_OAI_CriticalSK_goe_spectral_bad_probability_s2
import Theorems.Thm_OAI_CriticalSK_spectralGood_natural_sphere_bounds_s2
import Theorems.Thm_OAI_CriticalSK_spectralGood_orientation_variance_s2

section
-- module Solutions.OAIQ074_CM.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
-- module Solutions.OAIQ074_CM.CriticalSK_SphereGeometry
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

lemma orthogonalIsometry_continuous :
    Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι => orthogonalIsometry p.1 p.2) := by
  change Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι =>
    WithLp.toLp 2 (fun i => ∑ j, (p.1 : Matrix ι ι ℝ) i j * p.2 j))
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hU : Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι =>
      (p.1 : Matrix ι ι ℝ)) := continuous_subtype_val.comp continuous_fst
  exact ((continuous_apply j).comp ((continuous_apply i).comp hU)).mul
    ((PiLp.continuous_apply 2 _ j).comp continuous_snd)

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

lemma orthogonal_transitive {x y : EuclideanSpace ℝ ι} (hxy : ‖x‖ = ‖y‖) :
    ∃ U : Matrix.orthogonalGroup ι ℝ, orthogonalIsometry U x = y := by
  refine ⟨matrixOfIsometry (Submodule.reflection (ℝ ∙ (x-y))ᗮ), ?_⟩
  rw [orthogonalIsometry_matrixOfIsometry]
  exact Submodule.reflection_sub hxy

end


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sphereMap_continuous (U : E ≃ₗᵢ[ℝ] E) : Continuous (sphereMap U) := by
  exact (U.continuous.comp continuous_subtype_val).subtype_mk _

lemma sphereMap_symm (U : E ≃ₗᵢ[ℝ] E) (u : sphere (0:E) 1) :
    sphereMap U (sphereMap U.symm u) = u := by
  apply Subtype.ext
  exact U.apply_symm_apply u.val

lemma sphereMap_cone_preimage (U : E ≃ₗᵢ[ℝ] E) (A : Set (sphere (0:E) 1)) :
    Ioo (0:ℝ) 1 • (Subtype.val '' (sphereMap U ⁻¹' A)) =
      U ⁻¹' (Ioo (0:ℝ) 1 • (Subtype.val '' A)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, U u.val, ⟨sphereMap U u, hu, rfl⟩, (U.map_smul r u.val).symm⟩
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, hy⟩
    refine ⟨r, hr, U.symm u.val, ⟨sphereMap U.symm u, ?_, rfl⟩, ?_⟩
    · change sphereMap U (sphereMap U.symm u) ∈ A
      rwa [sphereMap_symm]
    · apply U.injective
      rw [U.map_smul, U.apply_symm_apply]
      exact hy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereMap_preserving (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereMap U) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  constructor
  · exact (sphereMap_continuous U).measurable
  · ext A hA
    rw [Measure.map_apply (sphereMap_continuous U).measurable hA,
      Measure.toSphere_apply' _ ((sphereMap_continuous U).measurable hA),
      Measure.toSphere_apply' _ hA, sphereMap_cone_preimage,
      U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding]

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orthogonalSphere_continuous :
    Continuous (fun p : Matrix.orthogonalGroup ι ℝ × unitSphere ι => orthogonalSphere p.1 p.2) := by
  exact (orthogonalIsometry_continuous.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd))).subtype_mk _

lemma orthogonalSphere_mul (U V : Matrix.orthogonalGroup ι ℝ) (u : unitSphere ι) :
    orthogonalSphere (U*V) u = orthogonalSphere U (orthogonalSphere V u) := by
  apply Subtype.ext
  exact orthogonalIsometry_mul U V u.val

lemma orthogonalSphere_transitive (u w : unitSphere ι) :
    ∃ U : Matrix.orthogonalGroup ι ℝ, orthogonalSphere U u = w := by
  obtain ⟨U,hU⟩ := orthogonal_transitive
    ((mem_sphere_zero_iff_norm.mp u.property).trans (mem_sphere_zero_iff_norm.mp w.property).symm)
  exact ⟨U, Subtype.ext hU⟩

lemma orthogonalSphere_integral (U : Matrix.orthogonalGroup ι ℝ) (f : unitSphere ι → ℝ) :
    (∫ u, f (orthogonalSphere U u) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) =
      ∫ u, f u ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  apply (sphereMap_preserving (orthogonalIsometry U)).integral_comp
  apply (sphereMap_continuous (orthogonalIsometry U)).measurableEmbedding
  intro u w h
  apply Subtype.ext
  exact (orthogonalIsometry U).injective (congrArg Subtype.val h)

lemma orthogonal_orbit_integral_eq (f : unitSphere ι → ℝ) (u w : unitSphere ι) :
    (∫ U, f (orthogonalSphere U u) ∂orthogonalHaar ι) =
      ∫ U, f (orthogonalSphere U w) ∂orthogonalHaar ι := by
  obtain ⟨V,hV⟩ := orthogonalSphere_transitive u w
  rw [← hV]
  simp_rw [← orthogonalSphere_mul]
  exact (integral_mul_right_eq_self (fun U => f (orthogonalSphere U u)) V).symm

variable [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereArea_pos : 0 < sphereArea (ι := ι) := by
  exact ENNReal.toReal_pos ((measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne')
    (measure_ne_top _ _)

lemma orthogonal_first_moment (f : unitSphere ι → ℝ) (hf : Continuous f) (u : unitSphere ι) :
    (∫ U, f (orthogonalSphere U u) ∂orthogonalHaar ι) = sphereAverage f := by
  let σ := (volume : Measure (EuclideanSpace ℝ ι)).toSphere
  let J := fun w : unitSphere ι => ∫ U, f (orthogonalSphere U w) ∂orthogonalHaar ι
  have hc : Continuous (fun p : Matrix.orthogonalGroup ι ℝ × unitSphere ι =>
      f (orthogonalSphere p.1 p.2)) := hf.comp orthogonalSphere_continuous
  have hi : Integrable (fun p : Matrix.orthogonalGroup ι ℝ × unitSphere ι =>
      f (orthogonalSphere p.1 p.2)) ((orthogonalHaar ι).prod σ) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  have he : sphereArea (ι := ι) * J u = ∫ w, f w ∂σ := by
    calc
      _ = ∫ _w : unitSphere ι, J u ∂σ := by
        rw [integral_const, smul_eq_mul]
        rfl
      _ = ∫ w : unitSphere ι, J w ∂σ := integral_congr_ae
        (Filter.Eventually.of_forall (fun w => orthogonal_orbit_integral_eq f u w))
      _ = ∫ U, ∫ w : unitSphere ι, f (orthogonalSphere U w) ∂σ ∂orthogonalHaar ι :=
        (integral_integral_swap hi).symm
      _ = ∫ _U : Matrix.orthogonalGroup ι ℝ, ∫ w : unitSphere ι, f w ∂σ ∂orthogonalHaar ι := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun U => orthogonalSphere_integral U f)
      _ = _ := by simp
  exact (eq_div_iff (ne_of_gt (sphereArea_pos (ι := ι)))).mpr (by simpa only [mul_comm] using he)

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereUniform_integral (f : unitSphere ι → ℝ) :
    (∫ u, f u ∂sphereUniform) = sphereAverage f := by
  rw [sphereUniform, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  exact inv_mul_eq_div _ _

lemma orthogonal_sphere_preserving (u : unitSphere ι) :
    MeasurePreserving (fun U => orthogonalSphere U u) (orthogonalHaar ι) sphereUniform := by
  have hc : Continuous (fun U : Matrix.orthogonalGroup ι ℝ => orthogonalSphere U u) := by
    apply Continuous.subtype_mk
    exact orthogonalIsometry_fixed_continuous u.val
  refine ⟨hc.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    sphereUniform_integral]
  exact orthogonal_first_moment f f.continuous u

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma diagonalEnergy_continuous (lam : ι → ℝ) : Continuous (diagonalEnergy lam) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((PiLp.continuous_apply 2 _ i).pow 2)

lemma orthogonalHaar_integrable {f : Matrix.orthogonalGroup ι ℝ → ℝ} (hf : Continuous f) :
    Integrable f (orthogonalHaar ι) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

end


section

lemma cubeVector_norm {n : ℕ} (x : Spin n) : ‖cubeVector x‖ = Real.sqrt n := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg _), EuclideanSpace.real_norm_sq_eq]
  change ∑ i : Fin n, spinValue (x i)^2 = (n : ℝ)
  simp only [spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

end


section

lemma rotatedCubePartition_continuous {n : ℕ} (lam : Fin n → ℝ) (a : ℝ) :
    Continuous (rotatedCubePartition lam a) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  exact (continuous_const.mul ((diagonalEnergy_continuous lam).comp
    (orthogonalIsometry_fixed_continuous (cubeVector x)))).rexp

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SphereSaddle
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma sphereWeight_integrable (lam : ι → ℝ) (a r : ℝ) :
    Integrable (fun u : unitSphere ι => Real.exp (a / 2 * diagonalEnergy lam (r • u.val)))
      (volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  have hc : Continuous (fun u : unitSphere ι => Real.exp (a / 2 * diagonalEnergy lam (r • u.val))) := by
    unfold diagonalEnergy; fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ

lemma sphereWeight_integral_pos (lam : ι → ℝ) (a r : ℝ) :
    0 < ∫ u : unitSphere ι, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  have h := spherePartition_pos lam a r
  exact (div_pos_iff.mp h).elim (fun h => h.1)
    (fun h => False.elim (not_lt_of_ge (sphereArea_pos (ι := ι)).le h.2))

instance sphereTilted_probability (lam : ι → ℝ) (a r : ℝ) :
    IsProbabilityMeasure (sphereTilted lam a r) := by
  constructor
  rw [sphereTilted, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal (sphereWeight_integrable lam a r)
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sphereWeight_integral_pos lam a r)))
    ENNReal.ofReal_ne_top

lemma sphereTilted_apply_real (lam : ι → ℝ) (a r : ℝ) {A : Set (unitSphere ι)} (hA : MeasurableSet A) :
    (sphereTilted lam a r A).toReal =
      (∫ u in A, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) /
      (∫ u : unitSphere ι, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) := by
  rw [sphereTilted, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (sphereWeight_integrable lam a r).integrableOn
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)),
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sphereWeight_integral_pos lam a r).le,
    ENNReal.toReal_ofReal (integral_nonneg (fun u => (Real.exp_pos _).le))]
  ring

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_CubeRestriction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma orthogonal_radial_integral (F : EuclideanSpace ℝ ι → ℝ) (hF : Measurable F)
    {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ ι) (hx : ‖x‖ = r) :
    (∫ U, F (orthogonalIsometry U x) ∂orthogonalHaar ι) =
      sphereAverage (fun u => F (r • u.val)) := by
  have hu : ‖r⁻¹ • x‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hx,inv_mul_cancel₀ hr.ne']
  let u : unitSphere ι := ⟨r⁻¹ • x,mem_sphere_zero_iff_norm.mpr hu⟩
  have he : r • u.val = x := by
    change r • (r⁻¹ • x) = x
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hf : (fun U : Matrix.orthogonalGroup ι ℝ => F (orthogonalIsometry U x)) =
      fun U => F (r • (orthogonalSphere U u).val) := by
    funext U
    rw [← he,(orthogonalIsometry U).map_smul]
    rfl
  rw [hf,← sphereUniform_integral,← (orthogonal_sphere_preserving u).map_eq]
  exact (integral_map (orthogonal_sphere_preserving u).measurable.aemeasurable
    (hF.comp (show Measurable (fun v : unitSphere ι => r • v.val) by fun_prop)).aestronglyMeasurable).symm

omit [DecidableEq ι] in
lemma sphereRestricted_as_tilted (lam : ι → ℝ) (a r b : ℝ) (i : ι) :
    sphereAverage (fun u => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      spherePartition lam a r * (sphereTilted lam a r).real
        {u : unitSphere ι | |(r • u.val) i| ≤ b} := by
  have hA : MeasurableSet {u : unitSphere ι | |(r • u.val) i| ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.real,sphereTilted_apply_real lam a r hA,← integral_indicator hA]
  unfold spherePartition sphereAverage
  have hZ := (sphereWeight_integral_pos lam a r).ne'
  have he : (fun u : unitSphere ι => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      {u : unitSphere ι | |(r • u.val) i| ≤ b}.indicator
        (fun u => Real.exp (a/2*diagonalEnergy lam (r • u.val))) := rfl
  rw [he]
  simp only [div_mul_eq_mul_div] at hZ ⊢
  field_simp [hZ]

end

lemma rotatedCubeRestricted_measurable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeRestricted lam a b i) := by
  unfold rotatedCubeRestricted
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  have hc := orthogonalIsometry_fixed_continuous (cubeVector x)
  apply Measurable.ite (measurableSet_le ((EuclideanSpace.proj i).continuous.comp hc).abs.measurable measurable_const)
  · exact ((continuous_const.mul ((diagonalEnergy_continuous lam).comp hc)).rexp).measurable
  · exact measurable_const

lemma rotatedCubeRestricted_nonneg {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeRestricted lam a b i U := by
  unfold rotatedCubeRestricted
  positivity

lemma rotatedCubeRestricted_le {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeRestricted lam a b i U ≤ rotatedCubePartition lam a U := by
  unfold rotatedCubeRestricted rotatedCubePartition
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma rotatedCubeRestricted_integrable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeRestricted lam a b i) (orthogonalHaar (Fin n)) := by
  apply (orthogonalHaar_integrable (rotatedCubePartition_continuous lam a)).mono'
    (rotatedCubeRestricted_measurable lam a b i).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeRestricted_nonneg lam a b i U)]
    exact rotatedCubeRestricted_le lam a b i U)

lemma rotatedCubeRestricted_first_moment {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    (∫ U, rotatedCubeRestricted lam a b i U ∂orthogonalHaar (Fin n)) =
      spherePartition lam a (Real.sqrt n)*(sphereTilted lam a (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    if |x i| ≤ b then Real.exp (a/2*diagonalEnergy lam x) else 0
  have hF : Measurable F := Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    (continuous_const.mul (diagonalEnergy_continuous lam)).rexp.measurable measurable_const
  have hint (x : Spin n) : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => F (orthogonalIsometry U (cubeVector x)))
      (orthogonalHaar (Fin n)) := by
    have hc := orthogonalIsometry_fixed_continuous (cubeVector x)
    apply (orthogonalHaar_integrable (((continuous_const (y := a/2)).mul ((diagonalEnergy_continuous lam).comp hc)).rexp)).mono'
      (hF.comp hc.measurable).aestronglyMeasurable
    filter_upwards [] with U
    dsimp only [F,Function.comp_apply,Pi.mul_apply]
    split_ifs
    · simp only [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le,le_refl]
    · simpa only [norm_zero] using (Real.exp_pos (a/2*diagonalEnergy lam (orthogonalIsometry U (cubeVector x)))).le
  have he (x : Spin n) : (∫ U, F (orthogonalIsometry U (cubeVector x)) ∂orthogonalHaar (Fin n)) =
      spherePartition lam a (Real.sqrt n)*(sphereTilted lam a (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
    rw [orthogonal_radial_integral F hF (Real.sqrt_pos.mpr (by exact_mod_cast hn)) _ (cubeVector_norm x)]
    exact sphereRestricted_as_tilted lam a (Real.sqrt n) b i
  unfold rotatedCubeRestricted
  change (∫ U, (Fintype.card (Spin n):ℝ)⁻¹*∑ x : Spin n, F (orthogonalIsometry U (cubeVector x))
    ∂orthogonalHaar (Fin n)) = _
  rw [integral_const_mul,integral_finsetSum _ (fun x _ => hint x)]
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0),one_mul]

lemma divided_mass_variance_bound {A Z S : ℝ} (hA : 0 ≤ A) (hAZ : A ≤ Z)
    (hZ : 0 < Z) (hS : 0 < S) : A/Z ≤ 2*A/S+4*(Z/S-1)^2 := by
  by_cases hz : S/2 ≤ Z
  · have hh : A/Z ≤ 2*A/S := by
      rw [div_le_div_iff₀ hZ hS]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hz)]
    linarith [sq_nonneg (Z/S-1)]
  · have hratio : A/Z ≤ 1 := (div_le_one hZ).mpr hAZ
    have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 2*A/S := by positivity
    linarith

lemma integral_dominates_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {f : Ω → ℝ}
    (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (he : ∀ x ∈ E, 1 ≤ f x) :
    μ.real E ≤ ∫ x, f x ∂μ := by
  apply (measureReal_mono (show E ⊆ {x | 1 ≤ f x} from he)).trans
  simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf) hi 1

lemma rotatedCubePartition_pos {n : ℕ} (lam : Fin n → ℝ) (a : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 < rotatedCubePartition lam a U := by
  unfold rotatedCubePartition
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma rotatedCubeSmallBall_measurable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeSmallBall lam b i) :=
  (rotatedCubeRestricted_measurable lam 1 b i).div (rotatedCubePartition_continuous lam 1).measurable

lemma rotatedCubeSmallBall_nonneg {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeSmallBall lam b i U :=
  div_nonneg (rotatedCubeRestricted_nonneg lam 1 b i U) (rotatedCubePartition_pos lam 1 U).le

lemma rotatedCubeSmallBall_le_one {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeSmallBall lam b i U ≤ 1 :=
  (div_le_one (rotatedCubePartition_pos lam 1 U)).mpr (rotatedCubeRestricted_le lam 1 b i U)

lemma rotatedCubeSmallBall_integrable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeSmallBall lam b i) (orthogonalHaar (Fin n)) := by
  apply (integrable_const (1:ℝ)).mono' (rotatedCubeSmallBall_measurable lam b i).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeSmallBall_nonneg lam b i U)]
  exact rotatedCubeSmallBall_le_one lam b i U

lemma rotatedCubeSmallBall_expectation {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    (∫ U, rotatedCubeSmallBall lam b i U ∂orthogonalHaar (Fin n)) ≤
      2*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b}+
      4*(∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt n)-1)^2
        ∂orthogonalHaar (Fin n)) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let S := spherePartition lam 1 (Real.sqrt n)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hA := (rotatedCubeRestricted_integrable lam 1 b i).const_mul 2
  have hV : Integrable (fun U => (rotatedCubePartition lam 1 U / S - 1)^2) (orthogonalHaar (Fin n)) := orthogonalHaar_integrable (((rotatedCubePartition_continuous lam 1).div_const S).sub continuous_const |>.pow 2)
  have hh := integral_mono (rotatedCubeSmallBall_integrable lam b i) ((hA.div_const S).add (hV.const_mul 4))
    (fun U => divided_mass_variance_bound (rotatedCubeRestricted_nonneg lam 1 b i U)
      (rotatedCubeRestricted_le lam 1 b i U) (rotatedCubePartition_pos lam 1 U) hS)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hA.div_const S) (hV.const_mul 4),integral_div,integral_const_mul,integral_const_mul,
    rotatedCubeRestricted_first_moment hn,show spherePartition lam 1 (Real.sqrt n) = S from rfl] at hh
  have heq : 2*(S*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b})/S =
      2*(sphereTilted lam 1 (Real.sqrt n)).real {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b} := by
    field_simp
  rw [heq] at hh
  exact hh

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma covariance_inner_stdGaussian (v w : E) :
    cov[fun x => inner ℝ v x, fun x => inner ℝ w x; stdGaussian E] = inner ℝ v w := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

lemma inner_stdGaussian_law (v : E) :
    (stdGaussian E).map (fun x => inner ℝ v x) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have hG : HasGaussianLaw (fun x : E => inner ℝ v x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ v)
  rw [hG.map_eq_gaussianReal]
  congr 1
  · exact integral_strongDual_stdGaussian (innerSL ℝ v)
  · rw [← covariance_self (by fun_prop), covariance_inner_stdGaussian, real_inner_self_eq_norm_sq]

lemma gaussian_orthogonal_independent {κ : Type*} [Fintype κ] (v : κ → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) = 0)) :
    iIndepFun (fun i x => inner ℝ (v i) x) (stdGaussian E) := by
  have hG : HasGaussianLaw (fun x : E => fun i => inner ℝ (v i) x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi (fun i => innerSL ℝ (v i)))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [covariance_inner_stdGaussian]
  exact hv hij

variable {ι : Type*} [Fintype ι]

lemma conjugateGaussianMatrix_preserves (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U) =
      stdGaussian (GaussianMatrix ι) :=
  stdGaussian_map _

lemma euclidean_isometry_apply_eq_sum
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) (i : ι) :
    U v i = ∑ j, v j * U (EuclideanSpace.basisFun ι ℝ j) i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v, map_sum]
  simp

lemma conjugateGaussianMatrix_apply
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i j : ι) :
    conjugateGaussianMatrix U A i j =
      ∑ k, ∑ l, U (EuclideanSpace.basisFun ι ℝ k) i * A k l *
        U (EuclideanSpace.basisFun ι ℝ l) j := by
  simp only [conjugateGaussianMatrix, LinearIsometryEquiv.trans_apply,
    transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma conjugateGaussianMatrix_transpose
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (transposeGaussianMatrix A) =
      transposeGaussianMatrix (conjugateGaussianMatrix U A) := by
  ext i j
  simp only [conjugateGaussianMatrix_apply, transposeGaussianMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma symmetrizeGaussianMatrix_continuous (s : ℝ) :
    Continuous (symmetrizeGaussianMatrix (ι := ι) s) := by
  unfold symmetrizeGaussianMatrix
  fun_prop

lemma conjugate_symmetrize (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (symmetrizeGaussianMatrix s A) =
      symmetrizeGaussianMatrix s (conjugateGaussianMatrix U A) := by
  simp only [symmetrizeGaussianMatrix, map_smul, map_add,
    conjugateGaussianMatrix_transpose]

lemma goeLaw_conjugate (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (goeLaw ι s).map (conjugateGaussianMatrix U) = goeLaw ι s := by
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, conjugate_symmetrize]
  calc
    _ = ((stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U)).map
        (symmetrizeGaussianMatrix s) :=
      (Measure.map_map (symmetrizeGaussianMatrix_continuous s).measurable
        (conjugateGaussianMatrix U).continuous.measurable).symm
    _ = _ := by rw [conjugateGaussianMatrix_preserves]

lemma conjugateGaussianMatrix_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    Measurable (fun p : Ω × GaussianMatrix ι => conjugateGaussianMatrix (U p.1) p.2) := by
  have hc (k i : ι) : Measurable (fun ω => U ω (EuclideanSpace.basisFun ι ℝ k) i) :=
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).comp
      (hU.comp (measurable_id.prodMk measurable_const))
  change Measurable (fun p : Ω × GaussianMatrix ι => WithLp.toLp 2
    (fun i => WithLp.toLp 2 (fun j => conjugateGaussianMatrix (U p.1) p.2 i j)))
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  simp only [conjugateGaussianMatrix_apply]
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact ((hc k i).comp measurable_fst |>.mul
    ((by fun_prop : Measurable (fun A : GaussianMatrix ι => A k l)).comp measurable_snd)).mul
      ((hc l j).comp measurable_fst)

lemma random_goe_conjugation_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (s : ℝ)
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × GaussianMatrix ι =>
      (p.1, conjugateGaussianMatrix (U p.1) p.2))
      (μ.prod (goeLaw ι s)) (μ.prod (goeLaw ι s)) := by
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  exact (MeasurePreserving.id μ).skew_product
    (g := fun ω A => conjugateGaussianMatrix (U ω) A)
    (conjugateGaussianMatrix_measurable U hU)
    (Filter.Eventually.of_forall (fun ω => goeLaw_conjugate s (U ω)))

lemma goeEntryVector_inner (s : ℝ) (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (goeEntryVector s i j) A = symmetrizeGaussianMatrix s A i j := by
  simp [goeEntryVector, symmetrizeGaussianMatrix, inner_smul_left, inner_add_left]

lemma goe_entry_variance [DecidableEq ι] (s : ℝ) (i j : ι) :
    ‖goeEntryVector s i j‖ ^ 2 = if i = j then 4 * s ^ 2 else 2 * s ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  by_cases hij : i = j
  · subst j
    simp only [and_self, ite_true]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, and_self, ite_true, ite_false]
    ring

lemma goe_entry_law [DecidableEq ι] (s : ℝ) (i j : ι) :
    (goeLaw ι s).map (fun A => A i j) =
      gaussianReal 0 (if i = j then (4 * s ^ 2).toNNReal else (2 * s ^ 2).toNNReal) := by
  classical
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, ← goeEntryVector_inner]
  rw [inner_stdGaussian_law, goe_entry_variance]
  split_ifs <;> rfl

variable [LinearOrder ι]

lemma goeEntryVector_orthogonal (s : ℝ) :
    Pairwise (fun p q : UpperEntry ι =>
      inner ℝ (goeEntryVector s p.1.1 p.1.2) (goeEntryVector s q.1.1 q.1.2) = 0) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ hpq
  have h1 : ¬(i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hpq rfl
  have h2 : ¬(i = l ∧ j = k) := by
    intro hs
    have he : i = j := le_antisymm hij (by simpa only [hs.1, hs.2] using hkl)
    apply hpq
    apply Subtype.ext
    exact Prod.ext (he.trans hs.2) (he.symm.trans hs.1)
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  simp only [h1, h2, ite_false, add_zero, mul_zero,
    show ¬(j = k ∧ i = l) from fun h => h2 ⟨h.2, h.1⟩,
    show ¬(j = l ∧ i = k) from fun h => h1 ⟨h.2, h.1⟩]

lemma goe_entries_independent (s : ℝ) :
    iIndepFun (fun p : UpperEntry ι => fun A : GaussianMatrix ι => A p.1.1 p.1.2)
      (goeLaw ι s) := by
  have h := gaussian_orthogonal_independent
    (fun p : UpperEntry ι => goeEntryVector s p.1.1 p.1.2) (goeEntryVector_orthogonal s)
  simp only [goeEntryVector_inner] at h
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => by fun_prop)).2
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  have hh := h.map_fun_eq_pi_map (fun _ => by fun_prop)
  simp only [Function.comp_def] at *
  rw [hh]
  congr 1
  ext p : 1
  exact (Measure.map_map (g := fun A : GaussianMatrix ι => A p.1.1 p.1.2) (by fun_prop)
    (symmetrizeGaussianMatrix_continuous s).measurable).symm

end

section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma goe_symmetric_ae (s : ℝ) : ∀ᵐ A ∂goeLaw ι s, ∀ i j, A i j = A j i := by
  rw [goeLaw]
  apply (ae_map_iff (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable (by measurability)).2
  filter_upwards [] with A i j
  simp only [symmetrizeGaussianMatrix, PiLp.smul_apply, PiLp.add_apply,
    transposeGaussianMatrix_apply, smul_eq_mul]
  ring

end Upper

open scoped BigOperators

instance goeLaw_probability {ι : Type*} [Fintype ι] (s : ℝ) :
    IsProbabilityMeasure (goeLaw ι s) :=
  (Measure.isProbabilityMeasure_map_iff
    (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance

end

section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma matrixOfGaussian_conjugate (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) :
    matrixOfGaussian (conjugateGaussianMatrix U A) =
      orthoMatrix U * matrixOfGaussian A * (orthoMatrix U).transpose := by
  ext i j
  simp only [matrixOfGaussian, conjugateGaussianMatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, orthoMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma conjugate_symmetric (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, conjugateGaussianMatrix U A i j = conjugateGaussianMatrix U A j i := by
  have hT : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have h := conjugateGaussianMatrix_transpose U A
  rw [hT] at h
  intro i j
  exact congrArg (fun B : GaussianMatrix ι => B i j) h

end

open scoped BigOperators

@[fun_prop] lemma firstColumn_measurable (n : ℕ) : Measurable (firstColumn (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  fun_prop [firstColumn]

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_MinMax
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_finrank {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) :
    finrank ℝ (basisSpan b s) = s.card := by
  have hli : LinearIndependent ℝ (fun i : s => b i) :=
    b.orthonormal.linearIndependent.comp (fun i : s => (i : Fin n)) Subtype.val_injective
  rw [basisSpan, finrank_span_eq_card hli, Fintype.card_coe]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_repr_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s)
    (i : Fin n) (hi : i ∉ s) : b.repr x i = 0 := by
  have hmem : x ∈ Submodule.span ℝ (b.toBasis '' (s : Set (Fin n))) := by
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp [Set.mem_range, Set.mem_image]
  have hs := b.toBasis.repr_support_subset_of_mem_span _ hmem
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hz
    exact hi (hs (Finsupp.mem_support_iff.mpr hz))
  simpa only [b.coe_toBasis_repr_apply] using hz

lemma basisSpan_intersection_unit {n : ℕ}
    (b c : OrthonormalBasis (Fin n) ℝ E) (s t : Finset (Fin n))
    (hcard : n < s.card + t.card) :
    ∃ x : E, ‖x‖ = 1 ∧ x ∈ basisSpan b s ∧ x ∈ basisSpan c t := by
  have hn : finrank ℝ E = n := by
    rw [finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hnot : ¬ Disjoint (basisSpan b s) (basisSpan c t) := by
    intro hd
    have h := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [basisSpan_finrank, basisSpan_finrank, hn] at h
    omega
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxs, hxt, hx⟩ := hnot
  refine ⟨‖x‖⁻¹ • x, ?_, (basisSpan b s).smul_mem _ hxs, (basisSpan c t).smul_mem _ hxt⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

omit [FiniteDimensional ℝ E] in
lemma basis_sum_squares {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simp only [b.repr_apply_apply]
  exact b.sum_sq_inner_right x

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, a i ≤ r) : basisQuadratic b a x ≤ r := by
  calc
    _ ≤ ∑ i, r * (b.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]
    _ = r := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_ge {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, r ≤ a i) : r ≤ basisQuadratic b a x := by
  calc
    _ = ∑ i, r * (b.repr x i) ^ 2 := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]

lemma basis_minmax_upper {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → basisQuadratic a α x ≤ f (basisQuadratic b β x))
    (i : Fin n) : α i ≤ f (β i) := by
  have hcard : n < (Finset.Iic i).card + (Finset.Ici i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Iic i) (Finset.Ici i) hcard
  have hlow : α i ≤ basisQuadratic a α x :=
    basisQuadratic_ge a α (Finset.Iic i) hxa hx
      (fun j hj => hα (Finset.mem_Iic.mp hj))
  have hupp : basisQuadratic b β x ≤ β i :=
    basisQuadratic_le b β (Finset.Ici i) hxb hx
      (fun j hj => hβ (Finset.mem_Ici.mp hj))
  exact hlow.trans ((hform x hx).trans (hf (hqS x hx) (hβS i) hupp))

lemma basis_minmax_lower {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → f (basisQuadratic b β x) ≤ basisQuadratic a α x)
    (i : Fin n) : f (β i) ≤ α i := by
  have hcard : n < (Finset.Ici i).card + (Finset.Iic i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Ici i) (Finset.Iic i) hcard
  have hupp : basisQuadratic a α x ≤ α i :=
    basisQuadratic_le a α (Finset.Ici i) hxa hx
      (fun j hj => hα (Finset.mem_Ici.mp hj))
  have hlow : β i ≤ basisQuadratic b β x :=
    basisQuadratic_ge b β (Finset.Iic i) hxb hx
      (fun j hj => hβ (Finset.mem_Iic.mp hj))
  exact (hf (hβS i) (hqS x hx) hlow).trans ((hform x hx).trans hupp)

lemma eigenbasisQuadratic_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    basisQuadratic (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x = inner ℝ x (T x) := by
  rw [basisQuadratic, ← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) x, ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

lemma eigenvalue_form_comparison {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) {S : Set ℝ} {Φ : ℝ → ℝ}
    (hplus : MonotoneOn (fun e => e + Φ e) S)
    (hminus : MonotoneOn (fun e => e - Φ e) S)
    (hBS : ∀ i, hB.eigenvalues hn i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → inner ℝ x (B x) ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 →
      |inner ℝ x (A x) - inner ℝ x (B x)| ≤ Φ (inner ℝ x (B x)))
    (i : Fin n) : |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ Φ (hB.eigenvalues hn i) := by
  have hu := basis_minmax_upper (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hplus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).2
      linarith) i
  have hl := basis_minmax_lower (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hminus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).1
      linarith) i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_TriNoise
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

lemma dyadic_cube_scale (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ∧
    ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ≤ 8 * N := by
  have he : ((2 : ℝ)^Nat.clog 8 N) ^ 3 = (8 : ℝ)^Nat.clog 8 N := by
    rw [← pow_mul, mul_comm (Nat.clog 8 N) 3, pow_mul]
    norm_num
  rw [he]
  constructor
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 8) N
  · by_cases hn : N = 1
    · subst N
      norm_num [Nat.clog_one_right]
    · have hn' : 1 < N := by omega
      have hi := Nat.pow_pred_clog_lt_self (by decide : 1 < 8) hn'
      have hj := Nat.clog_pos (by decide : 1 < 8) hn'
      have hid : Nat.clog 8 N = (Nat.clog 8 N).pred + 1 := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj).symm
      rw [hid, pow_succ]
      have hi' : (8 : ℝ)^(Nat.clog 8 N).pred < N := by exact_mod_cast hi
      linarith

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_Resolvent
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

namespace CriticalSK


open MeasureTheory Set



open MeasureTheory Set

lemma formA_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ formA n h := by unfold formA; positivity

lemma formB_nonneg (n : ℕ) : 0 ≤ formB n := by unfold formB; positivity

lemma formC_nonneg (n : ℕ) : 0 ≤ formC n := by unfold formC; positivity

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GOESpectrum
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
namespace CriticalSK

open scoped InnerProductSpace

lemma symmetric_eigenvalue_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A-B‖ := by
  refine eigenvalue_form_comparison hA hB hn (S := Set.univ) (Φ := fun _ => ‖A-B‖)
    (by intro a ha b hb hab; dsimp; linarith) (by intro a ha b hb hab; dsimp; linarith)
    (fun _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) ?_ i
  intro x hx
  calc
    _ = |inner ℝ x ((A-B) x)| := by rw [_root_.sub_apply,inner_sub_right]; rfl
    _ ≤ ‖x‖*‖(A-B) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖A-B‖*‖x‖) := mul_le_mul_of_nonneg_left ((A-B).le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [hx]; ring

lemma finite_real_linear_continuous {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : D →ₗ[ℝ] F) : Continuous T :=
  T.continuous_of_finiteDimensional

lemma gaussianMatrixCLM_continuous (n : ℕ) : Continuous (gaussianMatrixCLM (n := n)) := by
  change Continuous (gaussianMatrixToCLM n)
  exact finite_real_linear_continuous (gaussianMatrixToCLM n)

lemma symmetrize_half_eq {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    symmetrizeGaussianMatrix (1/2:ℝ) A = A := by
  ext i j
  rw [symmetrize_half_entry,hA j i]
  ring

lemma matrixOrderedEigenvalues_eq {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues A = (gaussianMatrixCLM_symmetric A hA).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := by
  unfold matrixOrderedEigenvalues
  congr 2
  exact congrArg gaussianMatrixCLM (symmetrize_half_eq A hA)

lemma matrixOrderedEigenvalues_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun A : GaussianMatrix (Fin n) => matrixOrderedEigenvalues A i) := by
  let F := fun A : GaussianMatrix (Fin n) => gaussianMatrixCLM (symmetrizeGaussianMatrix (1/2:ℝ) A)
  have hc : Continuous F := (gaussianMatrixCLM_continuous n).comp (symmetrizeGaussianMatrix_continuous _)
  rw [continuous_iff_continuousAt]
  intro A
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have hh := symmetric_eigenvalue_norm_bound (F B) (F A)
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric B))
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)) (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) i
  exact (show dist (matrixOrderedEigenvalues B i) (matrixOrderedEigenvalues A i) ≤ dist (F B) (F A) by
    simpa only [dist_eq_norm,Real.norm_eq_abs,matrixOrderedEigenvalues] using hh).trans_lt (h hB)

lemma orthoMatrix_transpose {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (orthoMatrix U).transpose = orthoMatrix U.symm := by
  ext i j
  have hh := U.inner_map_eq_flip (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa only [EuclideanSpace.inner_basisFun_real,EuclideanSpace.basisFun_inner,
    orthoMatrix,Matrix.transpose_apply] using hh

lemma orthoMatrix_toLpLin {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.toLpLin 2 2 (orthoMatrix U) = U.toLinearEquiv.toLinearMap := by
  ext x i
  change (∑ j, U (EuclideanSpace.basisFun (Fin n) ℝ j) i * x j) = U x i
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma gaussianMatrixCLM_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    (gaussianMatrixCLM (conjugateGaussianMatrix U A)).toLinearMap =
      U.toLinearEquiv.conj (gaussianMatrixCLM A).toLinearMap := by
  change Matrix.toLpLin 2 2 (matrixOfGaussian (conjugateGaussianMatrix U A)) = _
  rw [matrixOfGaussian_conjugate,Matrix.toLpLin_mul_same,Matrix.toLpLin_mul_same,
    orthoMatrix_transpose,orthoMatrix_toLpLin,orthoMatrix_toLpLin]
  rfl

lemma goeScale_square (n : ℕ) : 2*(goeScale n)^2 = (n+1:ℝ)⁻¹ := by
  have hn : (0:ℝ) < n+1 := by positivity
  unfold goeScale
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  field_simp

lemma matrixOrderedEigenvalues_measurable (n : ℕ) :
    Measurable (matrixOrderedEigenvalues (n := n)) :=
  Measurable.of_eval (fun i => (matrixOrderedEigenvalues_continuous i).measurable)

lemma spectralGood_measurable (n : ℕ) (h s : ℝ) : MeasurableSet (spectralGood n h s) := by
  simp only [spectralGood,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le ((measurable_pi_apply i).sub_const _).abs measurable_const

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_DisorderTransfer
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

lemma symmetric_sum_upper {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i)+2*∑ e : Edge n, f e.val.1 e.val.2 := by
  classical
  have hu : (∑ e : Edge n, f e.val.1 e.val.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Fintype.sum_prod_type' (fun i j : Fin n => if i < j then f i j else 0)]
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
      (by intro p; simp) (fun p : Fin n × Fin n => f p.1 p.2)).symm
  rw [hu]
  have hl : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    rw [hf j i]
  have hd : (∑ i, ∑ j, if i = j then f i j else 0) = ∑ i, f i i := by simp
  calc
    _ = (∑ i, ∑ j, if i = j then f i j else 0)+
        (∑ i, ∑ j, if i < j then f i j else 0)+(∑ i, ∑ j, if j < i then f i j else 0) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h,ne_of_lt h,not_lt_of_ge h.le]
      · subst j; simp
      · simp [h,ne_of_gt h,not_lt_of_ge h.le]
    _ = _ := by rw [hd,hl]; ring

lemma matrixEnergy_hamiltonian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (x : Spin n) :
    matrixEnergy A x = hamiltonian (matrixDisorder A) x+(1/2:ℝ)*∑ i, A i i := by
  unfold matrixEnergy
  rw [symmetric_sum_upper _ (by intro i j; rw [hA.apply i j]; ring)]
  have hd : (∑ i, A i i*spinValue (x i)*spinValue (x i)) = ∑ i, A i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc,← pow_two,spinValue_sq,mul_one]
  rw [hd]
  unfold hamiltonian matrixDisorder
  ring

lemma matrixEnergy_inner {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    matrixEnergy A x = (1/2:ℝ)*inner ℝ (cubeVector x) (A.toEuclideanLin (cubeVector x)) := by
  simp only [matrixEnergy,EuclideanSpace.inner_eq_star_dotProduct,Matrix.toLpLin_apply,star_trivial]
  change (1/2:ℝ)*(∑ i, ∑ j, A i j*spinValue (x i)*spinValue (x j)) =
    (1/2:ℝ)*∑ i, (∑ j, A i j*spinValue (x j))*spinValue (x i)
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma gibbs_continuous {n : ℕ} (x : Spin n) : Continuous (fun W : Disorder n => gibbs W x) := by
  apply Continuous.div
  · unfold hamiltonian; fun_prop
  · unfold partition hamiltonian; fun_prop
  · exact fun W => (partition_pos W).ne'

lemma linearSmallBall_continuous {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Continuous (fun W : Disorder n => linearSmallBall W a b) := by
  unfold linearSmallBall
  apply continuous_finsetSum
  intro x _
  split_ifs
  · exact gibbs_continuous x
  · exact continuous_const

lemma smallBallObstruction_closed (n : ℕ) (b δ : ℝ) : IsClosed (smallBallObstruction n b δ) := by
  unfold smallBallObstruction
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (linearSmallBall_continuous _ _)

lemma linearObservable_inner {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (x : Spin n) :
    linearObservable a x = inner ℝ a (cubeVector x) := by
  simp only [linearObservable,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  change a i*spinValue (x i) = spinValue (x i)*a i
  ring

lemma rotatedDirection_norm {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    ‖rotatedDirection U i‖ = 1 := by
  rw [rotatedDirection,LinearIsometryEquiv.norm_map]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i

lemma rotatedDirection_observable {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) (x : Spin n) :
    linearObservable (rotatedDirection U i) x = (orthogonalIsometry U (cubeVector x)) i := by
  rw [linearObservable_inner,← (orthogonalIsometry U).inner_map_map]
  simp only [rotatedDirection,LinearIsometryEquiv.apply_symm_apply,EuclideanSpace.basisFun_inner]

lemma gibbs_exp_shift {n : ℕ} {W : Disorder n} (E : Spin n → ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = E x+c) (x : Spin n) :
    gibbs W x = Real.exp (E x)/(∑ y, Real.exp (E y)) := by
  simp only [gibbs,partition,h,Real.exp_add,← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

lemma rotatedCubeSmallBall_eq {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c)
    (b : ℝ) (i : Fin n) :
    rotatedCubeSmallBall lam b i U = linearSmallBall W (rotatedDirection U i) b := by
  have hg := gibbs_exp_shift _ c h
  unfold rotatedCubeSmallBall rotatedCubeRestricted rotatedCubePartition linearSmallBall
  simp only [one_div,rotatedDirection_observable,hg]
  rw [mul_div_mul_left _ _ (inv_ne_zero (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

lemma smallBallObstruction_rotation {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c)
    (b δ : ℝ) (i : Fin n) (hW : W ∈ smallBallObstruction n b δ) :
    δ ≤ rotatedCubeSmallBall lam b i U := by
  rw [rotatedCubeSmallBall_eq lam U c h]
  exact hW _ (rotatedDirection_norm U i)

lemma orthogonalIsometry_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    orthogonalIsometry (1 : Matrix.orthogonalGroup ι ℝ) x = x := euclideanMatrix_one_apply x

lemma orthogonalIsometry_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.orthogonalGroup ι ℝ) : orthogonalIsometry U⁻¹ = (orthogonalIsometry U).symm := by
  apply LinearIsometryEquiv.ext
  intro x
  apply (orthogonalIsometry U).injective
  rw [LinearIsometryEquiv.apply_symm_apply,← orthogonalIsometry_mul,mul_inv_cancel,orthogonalIsometry_one]

lemma continuous_pair_transform {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X × Y → Z} {g : X → X} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => f (g p.1,p.2)) :=
  hf.comp ((hg.comp continuous_fst).prodMk continuous_snd)

lemma orthogonalIsometry_symm_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι => (orthogonalIsometry p.1).symm p.2) := by
  have h : Continuous (fun p : Matrix.orthogonalGroup ι ℝ × EuclideanSpace ℝ ι =>
      orthogonalIsometry (p.1⁻¹) p.2) :=
    continuous_pair_transform orthogonalIsometry_continuous continuous_inv
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg (fun V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι => V p.2)
    (orthogonalIsometry_inv p.1).symm

lemma gaussian_matrix_energy_eigenbasis {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    ∃ V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, diagonalEnergy (matrixOrderedEigenvalues A) (V x) = inner ℝ x (gaussianMatrixCLM A x) := by
  let hT := gaussianMatrixCLM_symmetric A hA
  let hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  refine ⟨(hT.eigenvectorBasis hn).repr,?_⟩
  intro x
  rw [matrixOrderedEigenvalues_eq A hA]
  exact eigenbasisQuadratic_eq hT hn x

lemma haarConjugate_energy {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : GaussianMatrix (Fin n)) (x : Spin n) :
    matrixEnergy (matrixOfGaussian (haarConjugate U A)) x =
      (1/2:ℝ)*inner ℝ (orthogonalIsometry U (cubeVector x))
        (gaussianMatrixCLM A (orthogonalIsometry U (cubeVector x))) := by
  rw [matrixEnergy_inner]
  have hc := congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => L (cubeVector x))
    (gaussianMatrixCLM_conjugate (orthogonalIsometry U).symm A)
  change gaussianMatrixCLM (haarConjugate U A) (cubeVector x) =
    (orthogonalIsometry U).symm (gaussianMatrixCLM A (orthogonalIsometry U (cubeVector x))) at hc
  change (1/2:ℝ)*inner ℝ (cubeVector x) (gaussianMatrixCLM (haarConjugate U A) (cubeVector x)) = _
  rw [hc,← (orthogonalIsometry U).inner_map_map,LinearIsometryEquiv.apply_symm_apply]

lemma haarConjugate_hamiltonian {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i)
    (V : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hV : ∀ x, diagonalEnergy (matrixOrderedEigenvalues A) (V x) = inner ℝ x (gaussianMatrixCLM A x))
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (x : Spin n) :
    hamiltonian (matrixDisorder (matrixOfGaussian (haarConjugate U A))) x =
      (1/2:ℝ)*diagonalEnergy (matrixOrderedEigenvalues A)
        (orthogonalIsometry (matrixOfIsometry V*U) (cubeVector x))-
        (1/2:ℝ)*∑ i, haarConjugate U A i i := by
  rw [orthogonalIsometry_mul,orthogonalIsometry_matrixOfIsometry,hV,← haarConjugate_energy]
  have hB : (matrixOfGaussian (haarConjugate U A)).IsSymm := by
    ext i j
    exact conjugate_symmetric (orthogonalIsometry U).symm A hA j i
  rw [matrixEnergy_hamiltonian _ hB]
  change _ = _ - (1/2:ℝ)*∑ i, matrixOfGaussian (haarConjugate U A) i i
  ring

lemma goe_haar_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun p : Matrix.orthogonalGroup (Fin n) ℝ × GaussianMatrix (Fin n) => haarConjugate p.1 p.2)
      ((orthogonalHaar (Fin n)).prod (goeLaw (Fin n) s)) (goeLaw (Fin n) s) := by
  exact measurePreserving_snd.comp (random_goe_conjugation_preserving (orthogonalHaar (Fin n)) s
    (fun U => (orthogonalIsometry U).symm) orthogonalIsometry_symm_continuous.measurable)

lemma preserving_product_event_real {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (T : X × Y → Z) (hT : MeasurePreserving T (μ.prod ν) ρ)
    {E : Set Z} (hE : MeasurableSet E) :
    ρ.real E = ∫ y, μ.real {x | T (x,y) ∈ E} ∂ν := by
  let f : Z → ℝ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  let F := fun p : X × Y => f (T p)
  have hF : Measurable F := hf.comp hT.measurable
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable
    filter_upwards [] with p
    simp only [F,f]
    by_cases hp : T p ∈ E <;> simp [hp]
  have he := integral_map (μ := μ.prod ν) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq,integral_indicator_one hE,integral_prod_symm F hi] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with y
  have hs : MeasurableSet {x | T (x,y) ∈ E} :=
    hE.preimage (hT.measurable.comp (measurable_id.prodMk measurable_const))
  exact integral_indicator_one hs

lemma goe_haar_event_identity (n : ℕ) (s : ℝ) {E : Set (GaussianMatrix (Fin n))} (hE : MeasurableSet E) :
    (goeLaw (Fin n) s).real E =
      ∫ A, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ∂goeLaw (Fin n) s :=
  preserving_product_event_real _ _ _ _ (goe_haar_preserving n s) hE

open scoped NNReal

lemma gaussianDisorder_measurable (n : ℕ) : Measurable (gaussianDisorder (n := n)) := by
  apply Measurable.of_eval
  intro e
  change Measurable (fun A : GaussianMatrix (Fin n) => A e.val.1 e.val.2)
  fun_prop

lemma goe_disorder_law (n : ℕ) : (goeLaw (Fin (n+1)) (goeScale n)).map gaussianDisorder = disorderLaw (n+1) := by
  let e : Edge (n+1) → UpperEntry (Fin (n+1)) := fun p => ⟨p.val,p.property.le⟩
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun r : UpperEntry (Fin (n+1)) => r.val) hpq
  have hi := (goe_entries_independent (ι := Fin (n+1)) (goeScale n)).precomp he
  have hm := hi.map_fun_eq_pi_map (fun _ => by fun_prop)
  change (goeLaw (Fin (n+1)) (goeScale n)).map gaussianDisorder = _ at hm
  rw [hm]
  unfold disorderLaw
  congr 1
  funext p
  rw [goe_entry_law,ite_eq_right (ne_of_lt p.property)]
  congr 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity),NNReal.coe_inv,NNReal.coe_natCast,goeScale_square]
  norm_num only [Nat.cast_add,Nat.cast_one]

end

open Set MeasureTheory

lemma haar_smallBallObstruction_bound {n : ℕ} (hn : 0 < n)
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i)
    (b : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    (orthogonalHaar (Fin n)).real {U | gaussianDisorder (haarConjugate U A) ∈ smallBallObstruction n b δ} ≤
      (2*(sphereTilted (matrixOrderedEigenvalues A) 1 (Real.sqrt n)).real
        {u : unitSphere (Fin n) | |(Real.sqrt n • u.val) i| ≤ b}+
        4*(∫ U, (rotatedCubePartition (matrixOrderedEigenvalues A) 1 U /
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n)))/δ := by
  obtain ⟨V,hV⟩ := gaussian_matrix_energy_eigenbasis A hA
  let lam := matrixOrderedEigenvalues A
  let R := matrixOfIsometry V
  have hmeas : Measurable (fun U => rotatedCubeSmallBall lam b i (R*U)) :=
    (rotatedCubeSmallBall_measurable lam b i).comp ((continuous_const.mul continuous_id).measurable)
  have hi : Integrable (fun U => rotatedCubeSmallBall lam b i (R*U)) (orthogonalHaar (Fin n)) := by
    apply (integrable_const (1:ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with U
    rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeSmallBall_nonneg lam b i (R*U))]
    exact rotatedCubeSmallBall_le_one lam b i (R*U)
  have hh := integral_dominates_event (E := {U | gaussianDisorder (haarConjugate U A) ∈ smallBallObstruction n b δ})
    (hi.div_const δ) (fun U => div_nonneg (rotatedCubeSmallBall_nonneg lam b i (R*U)) hδ.le) (fun U hU => by
      apply (le_div_iff₀ hδ).mpr
      rw [one_mul]
      exact smallBallObstruction_rotation lam (R*U) (-(1/2:ℝ)*∑ j, haarConjugate U A j j)
        (fun x => by simpa only [gaussianDisorder,lam,R,sub_eq_add_neg,neg_mul] using haarConjugate_hamiltonian A hA V hV U x) b δ i hU)
  rw [integral_div,integral_mul_left_eq_self] at hh
  exact hh.trans (div_le_div_of_nonneg_right (rotatedCubeSmallBall_expectation hn lam b i) hδ.le)

lemma goe_event_from_orbit_bound {n : ℕ} (s : ℝ) {E G : Set (GaussianMatrix (Fin n))}
    (hE : MeasurableSet E) (hG : MeasurableSet G) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ A ∈ G, (∀ i j, A i j = A j i) →
      (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ≤ C) :
    (goeLaw (Fin n) s).real E ≤ (goeLaw (Fin n) s).real Gᶜ+C := by
  rw [goe_haar_event_identity n s hE]
  have hi : Integrable (fun A => Gᶜ.indicator (1 : GaussianMatrix (Fin n) → ℝ) A+C) (goeLaw (Fin n) s) :=
    ((integrable_const (1:ℝ)).indicator hG.compl).add (integrable_const C)
  have hh := integral_mono_of_nonneg
    (show ∀ᵐ A ∂goeLaw (Fin n) s, 0 ≤ (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} from
      ae_of_all _ (fun _ => measureReal_nonneg)) hi
    (show ∀ᵐ A ∂goeLaw (Fin n) s, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ≤
      Gᶜ.indicator (1 : GaussianMatrix (Fin n) → ℝ) A+C from by
      filter_upwards [goe_symmetric_ae s] with A hA
      by_cases hAG : A ∈ G
      · simpa only [Set.indicator_of_notMem (show A ∉ Gᶜ from not_not.mpr hAG),zero_add] using hbound A hAG hA
      · rw [Set.indicator_of_mem hAG]
        exact (measureReal_le_one).trans (le_add_of_nonneg_right hC))
  change (∫ A, (orthogonalHaar (Fin n)).real {U | haarConjugate U A ∈ E} ∂goeLaw (Fin n) s) ≤
    (∫ A, Gᶜ.indicator (fun _ => (1:ℝ)) A+C ∂goeLaw (Fin n) s) at hh
  rw [integral_add ((integrable_const (1:ℝ)).indicator hG.compl) (integrable_const C),
    integral_indicator_const _ hG.compl,integral_const] at hh
  simpa using hh

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_EdgeAsymptotics
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

namespace CriticalSK


open scoped Topology

lemma edgeLength_pos (n : ℕ) : 0 < edgeLength n := by unfold edgeLength; positivity

lemma edgeLength_cast_pos (n : ℕ) : (0:ℝ) < edgeLength n := by exact_mod_cast edgeLength_pos n

lemma edgeLength_cube (n : ℕ) : (n+1:ℝ) ≤ (edgeLength n:ℝ)^3 ∧
    (edgeLength n:ℝ)^3 ≤ 8*(n+1:ℝ) := by
  simpa only [edgeLength,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using
    dyadic_cube_scale (n+1) (Nat.succ_pos n)

lemma naturalEdgeScale_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalEdgeScale n L := by
  exact div_pos hL (sq_pos_of_pos (edgeLength_cast_pos n))

lemma naturalEdgeScale_base (n : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ naturalEdgeScale n L := by
  simp only [scaleEnergy,scaleRoot,pow_zero,one_div,naturalEdgeScale,edgeLength,Nat.cast_pow,Nat.cast_ofNat]
  rw [inv_pow,← one_div]
  exact div_le_div_of_nonneg_right hL (by positivity)

lemma formA_edgeLength (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    formA n h ≤ formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ) := by
  let D : ℝ := edgeLength n
  have hD : 0 < D := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  have hroot : Real.sqrt (32*(entryVariance n:ℝ)) ≤
      Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ) := by
    have hfrac : 32*(entryVariance n:ℝ) ≤ (512*(48*Real.exp 1+4))/D^3 := by
      change 32*(2*(48*Real.exp 1+4)/(n+1)) ≤ _
      apply (le_div_iff₀ (pow_pos hD 3)).mpr
      calc
        _ = (64*(48*Real.exp 1+4))*D^3/(n+1) := by ring
        _ ≤ (64*(48*Real.exp 1+4))*(8*(n+1))/(n+1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (edgeLength_cube n).2 (by positivity)) hN.le
        _ = 512*(48*Real.exp 1+4) := by field_simp; ring
    calc
      _ ≤ Real.sqrt ((512*(48*Real.exp 1+4))/D^3) := Real.sqrt_le_sqrt hfrac
      _ = _ := by
        rw [Real.sqrt_div (by positivity)]
        have hd : Real.sqrt (D^3) = D^(3/2:ℝ) := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hD.le]
          norm_num
        rw [hd,div_eq_mul_inv,← Real.rpow_neg hD.le]
        congr 2; norm_num
  calc
    _ = 41472*Real.sqrt (32*(entryVariance n:ℝ))*(h+1)*D^(1/4:ℝ) := by
      simp only [formA,D,edgeLength,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 41472*(Real.sqrt (512*(48*Real.exp 1+4))*D^(-3/2:ℝ))*(h+1)*D^(1/4:ℝ) := by
      gcongr
    _ = formConstant*(h+1)*D^(-5/4:ℝ) := by
      rw [formConstant,show (-5/4:ℝ)=(-3/2:ℝ)+(1/4:ℝ) by norm_num,Real.rpow_add hD]
      ring

lemma formA_natural_scale (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    formA n h*(naturalEdgeScale n L)^(-5/8:ℝ) ≤ formConstant*(h+1)*L^(-5/8:ℝ) := by
  have hD := edgeLength_cast_pos n
  calc
    _ ≤ (formConstant*(h+1)*(edgeLength n:ℝ)^(-5/4:ℝ))*(naturalEdgeScale n L)^(-5/8:ℝ) := by
      exact mul_le_mul_of_nonneg_right (formA_edgeLength n hh)
        (Real.rpow_nonneg (naturalEdgeScale_pos n hL).le _)
    _ = _ := by
      rw [naturalEdgeScale,Real.div_rpow hL.le (sq_nonneg _),← Real.rpow_natCast,
        ← Real.rpow_mul hD.le]
      norm_num
      field_simp [Real.rpow_ne_zero hD.le hD.ne']

lemma edgeLength_tendsto : Tendsto (fun n : ℕ => (edgeLength n:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  filter_upwards [hn.eventually_ge_atTop ((max b 0)^3)] with n hn'
  by_contra! hb
  have hp := pow_lt_pow_left₀ (hb.trans_le (le_max_left b 0))
    (edgeLength_cast_pos n).le (by norm_num : 3 ≠ 0)
  linarith [(edgeLength_cube n).1]

lemma edgeLength_sq_div_bound (n : ℕ) :
    (edgeLength n:ℝ)^2/(n+1) ≤ 8/(edgeLength n:ℝ) := by
  have hD := edgeLength_cast_pos n
  have hN : (0:ℝ) < n+1 := by positivity
  rw [div_le_div_iff₀ hN hD]
  nlinarith [(edgeLength_cube n).2]

lemma edgeLength_sq_div_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)^2/(n+1)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) edgeLength_sq_div_bound
  exact edgeLength_tendsto.const_div_atTop 8

lemma edgeLength_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (edgeLength n:ℝ)/Real.sqrt (n+1)) atTop (𝓝 0) := by
  have hh := edgeLength_sq_div_tendsto.sqrt
  simpa only [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (edgeLength_cast_pos _).le,Real.sqrt_zero] using hh

lemma naturalEdgeScale_tendsto (L : ℝ) :
    Tendsto (fun n => naturalEdgeScale n L) atTop (𝓝 0) := by
  exact ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp edgeLength_tendsto).const_div_atTop L

lemma formB_natural_scale_tendsto (L : ℝ) :
    Tendsto (fun n => formB n / naturalEdgeScale n L) atTop (𝓝 0) := by
  have hh := (edgeLength_sq_div_tendsto.const_mul 8).div_const L
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formB,naturalEdgeScale]
    ring_nf; simp only [inv_inv]; ring)

lemma formC_natural_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n => formC n / Real.sqrt (naturalEdgeScale n L)) atTop (𝓝 0) := by
  have hh := (edgeLength_div_sqrt_tendsto.const_mul 16).div_const (Real.sqrt L)
  simpa only [mul_zero,zero_div] using hh.congr (fun n => by
    dsimp only [formC,naturalEdgeScale]
    rw [Real.sqrt_div hL.le,Real.sqrt_sq (edgeLength_cast_pos n).le]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]; ring)

lemma naturalEdgeScale_space (n : ℕ) {L : ℝ} (hL : 0 < L) :
    L*Real.sqrt L/8 ≤ (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ∧
    (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) ≤ L*Real.sqrt L := by
  have hD := edgeLength_cast_pos n
  have he : (n+1:ℝ)*naturalEdgeScale n L*Real.sqrt (naturalEdgeScale n L) =
      (L*Real.sqrt L)*((n+1:ℝ)/(edgeLength n:ℝ)^3) := by
    rw [naturalEdgeScale,Real.sqrt_div hL.le,Real.sqrt_sq hD.le]
    ring
  have hfrac : (1/8:ℝ) ≤ (n+1:ℝ)/(edgeLength n:ℝ)^3 := by
    rw [le_div_iff₀ (pow_pos hD 3)]
    linarith [(edgeLength_cube n).2]
  have hfrac' : (n+1:ℝ)/(edgeLength n:ℝ)^3 ≤ 1 := by
    rw [div_le_one (pow_pos hD 3)]
    exact (edgeLength_cube n).1
  rw [he]
  constructor
  · simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ L*Real.sqrt L)
  · simpa using mul_le_mul_of_nonneg_left hfrac' (by positivity : 0 ≤ L*Real.sqrt L)

lemma traceCost_small (n : ℕ) {h s η : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost n h s ≤ η) :
    formA n h*s^(-5/8:ℝ)+formB n/s+formC n ≤ η := by
  have hA := formA_nonneg n hh
  have hB := formB_nonneg n
  have hC := formC_nonneg n
  have hp : 0 ≤ formA n h*s^(-5/8:ℝ) := by positivity
  have hq : 0 ≤ formB n/s := by positivity
  have hroot : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs1
  have hcle : formC n ≤ 2*formC n/Real.sqrt s := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hs)]
    nlinarith [mul_le_mul_of_nonneg_left hroot hC]
  have htail : 0 ≤ 2/((n+1:ℝ)*s*Real.sqrt s) := by positivity
  unfold traceCost at hcost
  have h8 : 8*formB n/s = 8*(formB n/s) := by ring
  rw [h8] at hcost
  nlinarith

open scoped Topology

lemma traceCost_natural_le (n : ℕ) {h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    traceCost n h (naturalEdgeScale n L) ≤ edgeFixedCost h L+
      8*(formB n/naturalEdgeScale n L)+2*(formC n/Real.sqrt (naturalEdgeScale n L)) := by
  have hspace := (naturalEdgeScale_space n hL).1
  have hbot : 0 < L*Real.sqrt L/8 := by positivity
  have htail := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) hbot hspace
  have hA := mul_le_mul_of_nonneg_left (formA_natural_scale n hh hL) (by norm_num : (0:ℝ) ≤ 416)
  rw [show 2/(L*Real.sqrt L/8) = 16/(L*Real.sqrt L) by ring] at htail
  unfold traceCost edgeFixedCost
  ring_nf at hA htail ⊢
  linarith

lemma traceCost_natural_eventually {h L η : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hcost : edgeFixedCost h L < η) :
    ∀ᶠ n : ℕ in atTop, traceCost n h (naturalEdgeScale n L) ≤ η := by
  have ht := ((formB_natural_scale_tendsto L).const_mul 8).add
    ((formC_natural_scale_tendsto hL).const_mul 2)
  have ht' : Tendsto (fun n => 8*(formB n/naturalEdgeScale n L)+
      2*(formC n/Real.sqrt (naturalEdgeScale n L))) atTop (𝓝 0) := by simpa using ht
  filter_upwards [ht'.eventually (gt_mem_nhds (sub_pos.mpr hcost))] with n hn
  linarith [traceCost_natural_le n hh hL]

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SmallBall
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

open Set MeasureTheory Filter

lemma goe_natural_spectral_bad {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h (naturalEdgeScale n L))ᶜ) ≤ 32*Real.exp (-h^2) := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  filter_upwards [traceCost_natural_eventually hh hLp hcost,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hc hs
  apply goe_spectral_bad_probability_s2 n hh (naturalEdgeScale_pos n hLp) (naturalEdgeScale_base n hL1)
  have ht := traceCost_small n hh (naturalEdgeScale_pos n hLp) hs.le hc
  have hA : 0 ≤ formA n h*(naturalEdgeScale n L)^(-5/8:ℝ) := by
    exact mul_nonneg (formA_nonneg n hh) (Real.rpow_nonneg (naturalEdgeScale_pos n hLp).le _)
  have hB : 0 ≤ formB n / naturalEdgeScale n L := div_nonneg (formB_nonneg n) (naturalEdgeScale_pos n hLp).le
  nlinarith

lemma disorder_goe_event (n : ℕ) {E : Set (Disorder (n+1))} (hE : MeasurableSet E) :
    (disorderLaw (n+1)).real E = (goeLaw (Fin (n+1)) (goeScale n)).real (gaussianDisorder ⁻¹' E) := by
  rw [← goe_disorder_law n]
  unfold Measure.real
  rw [Measure.map_apply (gaussianDisorder_measurable _) hE]

lemma natural_smallBallObstruction_probability_s2_oai {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      (smallBallObstruction (n+4) (b*(n+4:ℝ)^(1/3:ℝ)) δ) ≤
      32*Real.exp (-h^2)+(2*naturalSmallBallConstant L*b+4*(ε+naturalOrientationTail (n+3) L))/δ := by
  have hspectral := (tendsto_add_atTop_nat 3).eventually (goe_natural_spectral_bad hh hL hcost)
  filter_upwards [hspectral,spectralGood_natural_sphere_bounds_s2 hh hL hcost,
    spectralGood_orientation_variance_s2 hh hL hcost hε] with n hn hball hvar
  rw [disorder_goe_event (n+3) (smallBallObstruction_closed _ _ _).measurableSet]
  let G : Set (GaussianMatrix (Fin (n+4))) := matrixOrderedEigenvalues ⁻¹' spectralGood (n+3) h (naturalEdgeScale (n+3) L)
  have hG : MeasurableSet G := (spectralGood_measurable _ _ _).preimage (matrixOrderedEigenvalues_measurable _)
  have he := goe_event_from_orbit_bound (goeScale (n+3))
    ((smallBallObstruction_closed _ _ _).measurableSet.preimage (gaussianDisorder_measurable _)) hG
    (show 0 ≤ (2*naturalSmallBallConstant L*b+4*(ε+naturalOrientationTail (n+3) L))/δ from by
      unfold naturalSmallBallConstant naturalOrientationTail; positivity)
    (fun A hAG hA => by
      have hbnd := haar_smallBallObstruction_bound (by omega : 0 < n+4) A hA
        (b*(n+4:ℝ)^(1/3:ℝ)) hδ (2 : Fin (n+4))
      apply hbnd.trans
      apply div_le_div_of_nonneg_right _ hδ.le
      have hB := (hball (matrixOrderedEigenvalues A) hAG).1 b hb
      have hV := hvar (matrixOrderedEigenvalues A) hAG
      simpa only [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using
        add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2))
          (mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 4)))
  exact he.trans (add_le_add hn le_rfl)

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.natural_smallBallObstruction_probability_s2_oai := @OAI.CriticalSK.natural_smallBallObstruction_probability_s2_oai
