-- Prove2me | solution 1 for OAI.CriticalSK.pairMoment_variational_upper_general_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:06:34.433422+00:00
-- url     : https://prove2.me/submissions/5103a69e-1e39-4ac7-aeeb-f6938c1ec89d

import Mathlib
import Definitions.Def_OAIQ074C000

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

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
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMoments
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

namespace CriticalSK

lemma gaussian_square_density (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ha : 0 < 1 / 2 - t := by linarith
  have hb : 0 < 1 - 2 * t := by linarith
  apply (mul_left_inj' (Real.sqrt_ne_zero'.mpr hb)).mp
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hb)]
  have he : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t) =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / (1 / 2 - t) * (1 - 2 * t) =
      2 * Real.pi by field_simp]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1 / 2 - t)) *
        Real.sqrt (1 - 2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [mul_assoc, he]
    _ = 1 := inv_mul_cancel₀ (by positivity)

lemma gaussian_square_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  change 0 < ∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1
  rw [gaussian_square_integral t ht]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

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

variable [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereArea_pos : 0 < sphereArea (ι := ι) := by
  exact ENNReal.toReal_pos ((measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne')
    (measure_ne_top _ _)

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereUniform_integral (f : unitSphere ι → ℝ) :
    (∫ u, f u ∂sphereUniform) = sphereAverage f := by
  rw [sphereUniform, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  exact inv_mul_eq_div _ _

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma sphere_energy_continuous (lam : ι → ℝ) (a r : ℝ) :
    Continuous (fun u : unitSphere ι => Real.exp (a / 2 * diagonalEnergy lam (r • u.val))) := by
  have hscale : Continuous (fun u : unitSphere ι => r • (u.val : EuclideanSpace ℝ ι)) :=
    (continuous_const_smul r).comp continuous_subtype_val
  have henergy := (diagonalEnergy_continuous lam).comp hscale
  exact (henergy.const_mul (a / 2)).rexp

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

omit [Nonempty ι] in
lemma sphereUniform_rotation_preserving (U : Matrix.orthogonalGroup ι ℝ) :
    MeasurePreserving (orthogonalSphere U) (sphereUniform (ι := ι)) sphereUniform :=
  (sphereMap_preserving (orthogonalIsometry U)).smul_measure _

omit [Nonempty ι] in
lemma orthogonalSphere_injective (U : Matrix.orthogonalGroup ι ℝ) :
    Function.Injective (orthogonalSphere U) := by
  intro x y h
  apply Subtype.ext
  exact (orthogonalIsometry U).injective (congrArg Subtype.val h)

omit [Nonempty ι] in
lemma orthogonalSphere_fixed_continuous (U : Matrix.orthogonalGroup ι ℝ) :
    Continuous (orthogonalSphere U) := sphereMap_continuous (orthogonalIsometry U)

lemma spherePair_rotation_integral (U : Matrix.orthogonalGroup ι ℝ)
    (f : unitSphere ι × unitSphere ι → ℝ) :
    (∫ p, f (orthogonalSphere U p.1, orthogonalSphere U p.2)
      ∂(sphereUniform.prod sphereUniform)) = ∫ p, f p ∂(sphereUniform.prod sphereUniform) := by
  have hp := (sphereUniform_rotation_preserving U).prod (sphereUniform_rotation_preserving U)
  have hc : Continuous (Prod.map (orthogonalSphere U) (orthogonalSphere U)) :=
    (orthogonalSphere_fixed_continuous U).prodMap (orthogonalSphere_fixed_continuous U)
  have hinj : Function.Injective (Prod.map (orthogonalSphere U) (orthogonalSphere U)) := by
    intro a b h
    exact Prod.ext (orthogonalSphere_injective U (congrArg Prod.fst h))
      (orthogonalSphere_injective U (congrArg Prod.snd h))
  exact hp.integral_comp (hc.measurableEmbedding hinj) f

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma continuous_pair_first {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] {f : A × B → D} (hf : Continuous f) :
    Continuous (fun z : A × (B × C) => f (z.1, z.2.1)) :=
  hf.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma continuous_pair_second {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] {f : A × C → D} (hf : Continuous f) :
    Continuous (fun z : A × (B × C) => f (z.1, z.2.2)) :=
  hf.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

omit [Nonempty ι] in
lemma spherePair_first_continuous :
    Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      orthogonalSphere z.1 z.2.1) :=
  continuous_pair_first (orthogonalSphere_continuous (ι := ι))

omit [Nonempty ι] in
lemma spherePair_second_continuous :
    Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      orthogonalSphere z.1 z.2.2) :=
  continuous_pair_second (orthogonalSphere_continuous (ι := ι))

omit [Nonempty ι] in
lemma spherePair_action_continuous :
    Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      (orthogonalSphere z.1 z.2.1, orthogonalSphere z.1 z.2.2)) :=
  (spherePair_first_continuous (ι := ι)).prodMk (spherePair_second_continuous (ι := ι))

lemma spherePair_haar_average (f : unitSphere ι × unitSphere ι → ℝ) (hf : Continuous f) :
    (∫ p, ∫ U, f (orthogonalSphere U p.1, orthogonalSphere U p.2) ∂orthogonalHaar ι
      ∂(sphereUniform.prod sphereUniform)) = ∫ p, f p ∂(sphereUniform.prod sphereUniform) := by
  have hc : Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      f (orthogonalSphere z.1 z.2.1, orthogonalSphere z.1 z.2.2)) :=
    hf.comp spherePair_action_continuous
  have hi : Integrable (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      f (orthogonalSphere z.1 z.2.1, orthogonalSphere z.1 z.2.2))
      ((orthogonalHaar ι).prod (sphereUniform.prod sphereUniform)) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [← integral_integral_swap hi]
  simp only [spherePair_rotation_integral, integral_const, probReal_univ, one_smul]

omit [DecidableEq ι] [Nonempty ι] in
lemma sphere_inner_abs_le_one (x y : unitSphere ι) : |inner ℝ x.val y.val| ≤ 1 := by
  have h := abs_real_inner_le_norm x.val y.val
  simpa only [mem_sphere_zero_iff_norm.mp x.property, mem_sphere_zero_iff_norm.mp y.property,
    one_mul] using h

end

section

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ) :
    (∫ x, f x ∂μ) = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      f (p.2.val • p.1.val) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)) := by
  calc
    _ = ∫ x : ({(0)}ᶜ : Set E), f x.val ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((homeomorphUnitSphereProd E).symm p).val)

lemma radial_map_preserving (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) μ := by
  have hs : MeasurePreserving (Subtype.val : ({(0)}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    simpa only [restrict_compl_singleton] using
      (measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl)
  exact hs.comp (MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    μ.measurePreserving_homeomorphUnitSphereProd)

end

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

variable {ι : Type*} [Fintype ι]

lemma gaussianPiPDF_nonneg (v : ι → ℝ≥0) (x : ι → ℝ) : 0 ≤ gaussianPiPDF v x := by
  exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)

lemma gaussianPiPDF_integrable (v : ι → ℝ≥0) : Integrable (gaussianPiPDF v) :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

lemma gaussianPi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianPiPDF v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (gaussianPiPDF_integrable v).integrableOn
      (Filter.Eventually.of_forall (gaussianPiPDF_nonneg v))]
  change ENNReal.ofReal (∫ x, gaussianPiPDF v x
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  simp only [gaussianPiPDF]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [gaussianReal_of_var_ne_zero _ (hv i), withDensity_apply _ (hs i)]
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianPDFReal 0 (v i)).integrableOn
      (Filter.Eventually.of_forall (gaussianPDFReal_nonneg 0 (v i)))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg 0 (v i))

lemma gaussianPiPDF_continuous (v : ι → ℝ≥0) : Continuous (gaussianPiPDF v) := by
  unfold gaussianPiPDF gaussianPDFReal
  fun_prop

lemma map_density_of_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ν)
    (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (T x))).map T = ν.withDensity w := by
  ext A hA
  rw [Measure.map_apply hT.measurable hA, withDensity_apply _ (hT.measurable hA),
    withDensity_apply _ hA]
  exact hT.setLIntegral_comp_preimage hA hw

lemma density_toLp (w : (ι → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    ((volume : Measure (ι → ℝ)).withDensity w).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) :=
    hw.comp (WithLp.measurable_ofLp 2 _)
  simpa only [WithLp.ofLp_toLp] using
    map_density_of_preserving (PiLp.volume_preserving_toLp ι)
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) hm

lemma diagonalGaussian_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (gaussianPiPDF v (WithLp.ofLp x))) := by
  change (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = _
  rw [gaussianPi_density v hv]
  exact density_toLp _ (gaussianPiPDF_continuous v).measurable.ennreal_ofReal

lemma euclideanGaussianPDF_continuous (v : ι → ℝ≥0) :
    Continuous (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) :=
  (gaussianPiPDF_continuous v).comp (PiLp.continuous_ofLp 2 _)

lemma euclideanGaussianPDF_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) := by
  exact (PiLp.volume_preserving_ofLp ι).integrable_comp
    (gaussianPiPDF_integrable v).aestronglyMeasurable |>.mpr (gaussianPiPDF_integrable v)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar_iterated (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r : Ioi (0 : ℝ), ∫ u : sphere (0 : E) 1,
      f (r.val • u.val) ∂μ.toSphere ∂volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [integral_polar μ f]
  exact integral_prod_symm _
    ((radial_map_preserving μ).integrable_comp hf.aestronglyMeasurable |>.mpr hf)

omit [Nontrivial E] in
lemma angular_integral_continuous (μ : Measure E) [μ.IsAddHaarMeasure]
    [ProperSpace E] {f : E → ℝ} (hf : Continuous f) (A : Set (sphere (0 : E) 1)) :
    Continuous (fun r : ℝ => ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere.restrict A) := by
  have h : Continuous (Function.uncurry (fun r : ℝ => fun u : sphere (0 : E) 1 =>
      f (r • u.val))) := hf.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := μ.toSphere.restrict A) h
      (isCompact_univ : IsCompact (Set.univ : Set (sphere (0 : E) 1))))

lemma integral_polar_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) *
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [integral_polar_iterated μ hf, Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => (ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1))).toReal •
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma normShell_measurable (a b : ℝ) : MeasurableSet (normShell (E := E) a b) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normShell_radial (a b : ℝ) (r : Ioi (0 : ℝ)) (u : sphere (0 : E) 1) :
    r.val • u.val ∈ normShell a b ↔ r.val ∈ Ioc a b := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [normShell, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos r.property.out,
    hu, mul_one, Set.mem_Ioc]

lemma normShell_integral (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ x in normShell a b, f x ∂μ) = ∫ r in Ioc a b,
      r ^ (Module.finrank ℝ E - 1) * ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [← integral_indicator (normShell_measurable a b),
    integral_polar_real μ (hf.indicator (normShell_measurable a b))]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Ioc a b).indicator
        (fun r => r ^ (Module.finrank ℝ E - 1) *
          ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hh (u : sphere (0 : E) 1) := normShell_radial a b ⟨r, hr⟩ u
      by_cases hab : r ∈ Ioc a b
      · simp only [Set.indicator_of_mem hab]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => Set.indicator_of_mem ((hh u).mpr hab) f)
      · simp only [Set.indicator_of_notMem hab]
        have hz : (∫ u : sphere (0 : E) 1,
            (normShell a b).indicator f (r • u.val) ∂μ.toSphere) = 0 := by
          apply integral_eq_zero_of_ae
          exact Filter.Eventually.of_forall (fun u => Set.indicator_of_notMem
            (fun h => hab ((hh u).mp h)) f)
        rw [hz, mul_zero]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt ha h.1
      rw [Set.inter_eq_right.mpr hsub]

omit [Nontrivial E] in
lemma radialDensity_continuous (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Continuous f) : Continuous (radialDensity μ f) := by
  have h := angular_integral_continuous μ hf Set.univ
  simp only [Measure.restrict_univ] at h
  exact (continuous_id.pow _).mul h

lemma normShell_density (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b) =
      ENNReal.ofReal (∫ r in Ioc a b, radialDensity μ f r) := by
  rw [withDensity_apply _ (normShell_measurable a b),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hfn),
    normShell_integral μ hf ha]
  rfl

lemma normShell_density_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b)).toReal =
      ∫ r in Ioc a b, radialDensity μ f r := by
  rw [normShell_density μ hf hfn ha, ENNReal.toReal_ofReal]
  apply setIntegral_nonneg measurableSet_Ioc
  intro r hr
  exact mul_nonneg (pow_nonneg (le_trans ha hr.1.le) _) (integral_nonneg (fun u => hfn _))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma squareNormShell_measurable (s δ : ℝ) : MeasurableSet (squareNormShell (E := E) s δ) :=
  (measurableSet_lt measurable_const (measurable_norm.pow_const 2)).inter
    (measurableSet_le (measurable_norm.pow_const 2) measurable_const)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma squareNormShell_eq {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    squareNormShell (E := E) s δ = normShell (Real.sqrt s) (Real.sqrt (s+δ)) := by
  ext x
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt (by linarith : 0 ≤ s+δ)
  have h3 := Real.sqrt_nonneg s
  have h4 := Real.sqrt_nonneg (s+δ)
  have h5 := norm_nonneg x
  change (s < ‖x‖^2 ∧ ‖x‖^2 ≤ s+δ) ↔ (Real.sqrt s < ‖x‖ ∧ ‖x‖ ≤ Real.sqrt (s+δ))
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

lemma squareNormShell_density_limit (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Integrable f μ) (hfc : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun δ : ℝ =>
      (μ.withDensity (fun x => ENNReal.ofReal (f x)) (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (radialDensity μ f (Real.sqrt s) / (2 * Real.sqrt s))) := by
  have hq := radialDensity_continuous μ hfc
  have hd : HasDerivAt (fun t : ℝ => ∫ r in Real.sqrt s..t, radialDensity μ f r)
      (radialDensity μ f (Real.sqrt s)) (Real.sqrt s) :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hd' := hd.comp s (Real.hasDerivAt_sqrt hs.ne')
  have hh := hd'.tendsto_slope_zero_right
  simp only [Function.comp_def, mul_one_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  rw [squareNormShell_eq hs.le hδ0.le,
    normShell_density_real μ hf hfn (Real.sqrt_nonneg _), intervalIntegral.integral_same,
    sub_zero, smul_eq_mul, intervalIntegral.integral_of_le (Real.sqrt_le_sqrt (by linarith))]
  exact mul_comm _ _

end

section

lemma splitPair_preserving (n : ℕ) (μ : Fin (n+2) → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (splitPair n) (Measure.pi μ)
      (((μ 0).prod (μ 1)).prod (Measure.pi (fun i => μ i.succ.succ))) := by
  have h1 := measurePreserving_piFinSuccAbove μ 0
  have h2 := (MeasurePreserving.id (μ 0)).prod
    (measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => μ i.succ) 0)
  have h3 := (measurePreserving_prodAssoc (μ 0) (μ 1)
    (Measure.pi fun i : Fin n => μ i.succ.succ)).symm
  exact h3.comp (h2.comp h1)

lemma splitPair_square_sum (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i, x i^2) = x 0^2 + x 1^2 + ∑ i : Fin n, x i.succ.succ^2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

section

lemma squareDisk_measurable (s : ℝ) : MeasurableSet (squareDisk s) := by
  exact measurableSet_le (by fun_prop) measurable_const

lemma squareDisk_complex {s : ℝ} (hs : 0 ≤ s) :
    Complex.measurableEquivRealProd ⁻¹' squareDisk s =
      Metric.closedBall (0 : ℂ) (Real.sqrt s) := by
  ext z
  simp only [Set.mem_preimage, squareDisk, Set.mem_ofPred_eq,
    Complex.measurableEquivRealProd_apply, Metric.mem_closedBall, dist_zero_right]
  rw [show z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 by rw [Complex.sq_norm, Complex.normSq_apply]; ring]
  exact (Real.le_sqrt (norm_nonneg _) hs).symm

lemma volume_squareDisk {s : ℝ} (hs : 0 ≤ s) :
    volume (squareDisk s) = ENNReal.ofReal (Real.pi * s) := by
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage
    (squareDisk_measurable s).nullMeasurableSet, squareDisk_complex hs, Complex.volume_closedBall,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hs]
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul hs, mul_comm]

lemma squareAnnulus_sdiff (s δ : ℝ) :
    squareAnnulus s δ = squareDisk (s+δ) \ squareDisk s := by
  ext p
  simp [squareAnnulus, squareDisk, and_comm]

lemma volume_squareAnnulus {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) = ENNReal.ofReal (Real.pi * δ) := by
  rw [squareAnnulus_sdiff, measure_sdiff (by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s at hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s+δ
    linarith) (squareDisk_measurable s).nullMeasurableSet (by
      rw [volume_squareDisk hs]
      exact ENNReal.ofReal_ne_top)]
  rw [volume_squareDisk (by linarith), volume_squareDisk hs,
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  ring

lemma gaussianPairPrefactor_nonneg (a b : ℝ≥0) : 0 ≤ gaussianPairPrefactor a b := by
  unfold gaussianPairPrefactor
  positivity

lemma gaussianPair_density (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y =
      gaussianPairPrefactor a b * Real.exp (-(x^2/(2*a) + y^2/(2*b))) := by
  simp only [gaussianPDFReal, sub_zero, gaussianPairPrefactor, mul_inv, neg_div]
  rw [show (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (-(x^2/(2*a))) *
      ((Real.sqrt (2*Real.pi*b))⁻¹ * Real.exp (-(y^2/(2*b)))) =
      ((Real.sqrt (2*Real.pi*a))⁻¹ * (Real.sqrt (2*Real.pi*b))⁻¹) *
      (Real.exp (-(x^2/(2*a))) * Real.exp (-(y^2/(2*b)))) by ring,
    ← Real.exp_add, ← neg_add]

lemma gaussianPair_density_upper (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y ≤ gaussianPairPrefactor a b := by
  rw [gaussianPair_density]
  have h : Real.exp (-(x^2/(2*a) + y^2/(2*b))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left h (gaussianPairPrefactor_nonneg a b)

lemma gaussianPair_apply {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (s : Set (ℝ × ℝ)) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) s =
      ∫⁻ p in s, ENNReal.ofReal (gaussianPDFReal 0 a p.1 * gaussianPDFReal 0 b p.2) := by
  rw [gaussianReal_of_var_ne_zero _ ha, gaussianReal_of_var_ne_zero _ hb,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    withDensity_apply' _ s]
  apply lintegral_congr
  intro p
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

lemma volume_squareAnnulus_le {s δ : ℝ} (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) ≤ ENNReal.ofReal (Real.pi * δ) := by
  by_cases hs : 0 ≤ s
  · exact le_of_eq (volume_squareAnnulus hs hδ)
  · have hsn : s < 0 := lt_of_not_ge hs
    by_cases ht : 0 ≤ s+δ
    · have hsub : squareAnnulus s δ ⊆ squareDisk (s+δ) := fun _ h => h.2
      calc
        _ ≤ volume (squareDisk (s+δ)) := measure_mono hsub
        _ = ENNReal.ofReal (Real.pi*(s+δ)) := volume_squareDisk ht
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
    · have hset : squareAnnulus s δ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)
        exact ht (le_trans hh hp.2)
      rw [hset, measure_empty]
      exact bot_le

lemma gaussianPair_annulus_upper_all {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) (squareAnnulus s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) := by
  rw [gaussianPair_apply ha hb]
  calc
    _ ≤ ∫⁻ _p in squareAnnulus s δ, ENNReal.ofReal (gaussianPairPrefactor a b) := by
      exact lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (gaussianPair_density_upper a b p.1 p.2))
    _ ≤ ENNReal.ofReal (gaussianPairPrefactor a b) * ENNReal.ofReal (Real.pi * δ) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_mul_of_nonneg_left (volume_squareAnnulus_le hδ) bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (gaussianPairPrefactor_nonneg _ _), mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sumSquareShell_measurable {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    MeasurableSet (sumSquareShell Z s δ) := by
  have h : Measurable (fun p : (ℝ × ℝ) × Ω => p.1.1^2 + p.1.2^2 + Z p.2) := by fun_prop
  exact (measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_const)

lemma sumSquareShell_apply (μ : Measure (ℝ × ℝ)) (ν : Measure Ω) [SFinite μ] [SFinite ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    (μ.prod ν) (sumSquareShell Z s δ) = ∫⁻ ω, μ (squareAnnulus (s-Z ω) δ) ∂ν := by
  rw [Measure.prod_apply_symm (sumSquareShell_measurable hZ s δ)]
  apply lintegral_congr
  intro ω
  congr 1
  ext p
  simp only [Set.mem_preimage, sumSquareShell, squareAnnulus, Set.mem_ofPred_eq]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gaussianPair_bulk_upper {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((gaussianReal 0 a).prod (gaussianReal 0 b)).prod ν) (sumSquareShell Z s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) := by
  rw [sumSquareShell_apply _ _ hZ]
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) ∂ν :=
      lintegral_mono (fun ω => gaussianPair_annulus_upper_all ha hb (s-Z ω) hδ)
    _ = _ := by simp

end

section

lemma fourth_power_le_exp (x : ℝ) : x ^ 4 ≤ 32 * Real.exp (x^2/4) := by
  have h := Real.pow_div_factorial_le_exp (x^2/4) (by positivity) 2
  norm_num at h
  nlinarith

lemma gaussian_fourth_integrable : Integrable (fun x : ℝ => x^4) (gaussianReal 0 1) := by
  apply ((gaussian_square_integrable (1/4) (by norm_num)).const_mul 32).mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x^4)]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using fourth_power_le_exp x

lemma gaussian_as_scaled (v : ℝ≥0) : gaussianReal 0 v =
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]

lemma gaussian_fourth_integrable_var (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  rw [gaussian_as_scaled]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, mul_pow] using gaussian_fourth_integrable.const_mul ((Real.sqrt v)^4)

lemma gaussian_square_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_fourth_integrable_var v

lemma gaussian_square_mean (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_eq_sub (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2)
  simpa only [variance_id_gaussianReal, id_eq, Pi.pow_apply, integral_id_gaussianReal,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

variable {ι : Type*} [Fintype ι]

lemma piSquareSum_memLp (v : ι → ℝ≥0) :
    MemLp (piSquareSum (ι := ι)) 2 (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  exact memLp_finsetSum _ (fun i _ => (gaussian_square_memLp (v i)).comp_measurePreserving
    (measurePreserving_eval _ i))

lemma piSquareSum_mean (v : ι → ℝ≥0) :
    (∫ x, piSquareSum x ∂Measure.pi (fun i => gaussianReal 0 (v i))) = ∑ i, (v i : ℝ) := by
  unfold piSquareSum
  rw [integral_finsetSum Finset.univ (f := fun (i : ι) (x : ι → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i)
      ((gaussian_square_memLp (v i)).integrable (by norm_num)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i) (f := fun x : ℝ => x^2) (by fun_prop)]
  exact gaussian_square_mean (v i)

end

section

open Set Filter

variable {n : ℕ}

lemma diagonalGaussian_shell_split (v : Fin (n+2) → ℝ≥0) (s δ : ℝ) :
    diagonalGaussian v (squareNormShell s δ) =
      (((gaussianReal 0 (v 0)).prod (gaussianReal 0 (v 1))).prod
        (Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ)))
      (sumSquareShell piSquareSum s δ) := by
  rw [diagonalGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _)
    (squareNormShell_measurable s δ)]
  rw [← (splitPair_preserving n (fun i => gaussianReal 0 (v i))).measure_preimage
    (sumSquareShell_measurable (by unfold piSquareSum; fun_prop) s δ).nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_preimage, squareNormShell, sumSquareShell, Set.mem_ofPred_eq,
    EuclideanSpace.real_norm_sq_eq, splitPair, piSquareSum]
  rw [splitPair_square_sum]

lemma diagonalGaussian_shell_upper (v : Fin (n+2) → ℝ≥0)
    (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    diagonalGaussian v (squareNormShell s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1)) := by
  rw [diagonalGaussian_shell_split]
  exact gaussianPair_bulk_upper (by unfold piSquareSum; fun_prop) h0 h1 s hδ

lemma diagonalSquareDensity_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (diagonalGaussian v (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (diagonalSquareDensity v s)) := by
  rw [diagonalGaussian_density v hv]
  exact squareNormShell_density_limit volume (euclideanGaussianPDF_integrable v)
    (euclideanGaussianPDF_continuous v) (fun x => gaussianPiPDF_nonneg v x) hs

lemma diagonalSquareDensity_upper (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {s : ℝ} (hs : 0 < s) :
    diagonalSquareDensity v s ≤ Real.pi * gaussianPairPrefactor (v 0) (v 1) := by
  apply le_of_tendsto (diagonalSquareDensity_limit v hv hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (diagonalGaussian_shell_upper v (hv 0) (hv 1) s hδ0.le)
  have hp := gaussianPairPrefactor_nonneg (v 0) (v 1)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  apply (div_le_iff₀ hδ0).mpr
  nlinarith

end

open Set Filter

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma sphereAverage_one : sphereAverage (fun _ : unitSphere ι => (1:ℝ)) = 1 := by
  unfold sphereAverage sphereArea
  simp only [integral_const, smul_eq_mul, mul_one]
  exact div_self (ne_of_gt (sphereArea_pos (ι := ι)))

omit [Nonempty ι] in
lemma gaussianPiPDF_exp (v : ι → ℝ≥0) (x : ι → ℝ) :
    gaussianPiPDF v x = gaussianPiPrefactor v * Real.exp (-∑ i, x i ^ 2 / (2*v i)) := by
  simp only [gaussianPiPDF, gaussianPDFReal, sub_zero, Finset.prod_mul_distrib,
    gaussianPiPrefactor, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_pos {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    0 < gaussianPiPrefactor v := by
  apply Finset.prod_pos
  intro i _
  have hvi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
  positivity

omit [Nonempty ι] in
lemma unitSphere_sum_sq (u : unitSphere ι) : ∑ i, u.val i ^ 2 = 1 := by
  have hn : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [hn, one_pow] using (EuclideanSpace.real_norm_sq_eq u.val).symm

omit [Nonempty ι] in
lemma sphereGaussianPDF {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (r : ℝ) (u : unitSphere ι) :
    gaussianPiPDF v (WithLp.ofLp (r • u.val)) = gaussianPiPrefactor v * Real.exp (-z*r^2/2) *
      Real.exp (a/2 * diagonalEnergy lam (r • u.val)) := by
  rw [gaussianPiPDF_exp, mul_assoc, ← Real.exp_add]
  congr 2
  have hsum : ∑ i, (r • u.val) i ^ 2 / (2 * v i) =
      z*r^2/2 - a/2 * diagonalEnergy lam (r • u.val) := by
    simp only [diagonalEnergy, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = ∑ i, (z*r^2/2 * u.val i^2 - a/2 * (lam i*(r*u.val i)^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv, mul_inv, hq i]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, unitSphere_sum_sq, mul_one,
          ← Finset.mul_sum]
  rw [hsum]
  ring

lemma radialDensity_spherePartition {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (r : ℝ) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) r =
      r ^ (Fintype.card ι - 1) * gaussianPiPrefactor v * Real.exp (-z*r^2/2) *
      sphereArea (ι := ι) * spherePartition lam a r := by
  unfold radialDensity spherePartition sphereAverage
  simp only [finrank_euclideanSpace]
  simp_rw [sphereGaussianPDF hq]
  rw [integral_const_mul]
  have ha := ne_of_gt (sphereArea_pos (ι := ι))
  field_simp

lemma spherePartition_zero (lam : ι → ℝ) (r : ℝ) : spherePartition lam 0 r = 1 := by
  simpa only [spherePartition, zero_div, zero_mul, Real.exp_zero] using sphereAverage_one (ι := ι)

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

lemma radialDensity_standard (r : ℝ) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) r =
      r ^ (Fintype.card ι - 1) * gaussianPiPrefactor (fun _ : ι => 1) * Real.exp (-r^2/2) *
      sphereArea (ι := ι) := by
  have h := radialDensity_spherePartition (lam := fun _ : ι => (0:ℝ))
    (v := fun _ => 1) (z := 1) (a := 0) (by norm_num) r
  simpa only [spherePartition_zero, mul_one, neg_mul, one_mul] using h

lemma spherical_radial_ratio {lam : ι → ℝ} {v : ι → ℝ≥0} {z a r : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (hr : 0 < r) :
    radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) r /
      radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) r =
      gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1) *
        Real.exp (-(z-1)*r^2/2) * spherePartition lam a r := by
  rw [radialDensity_spherePartition hq, radialDensity_standard]
  have hE : Real.exp (-(z-1)*r^2/2) = Real.exp (-z*r^2/2) / Real.exp (-r^2/2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hE]
  have h1 := ne_of_gt (gaussianPiPrefactor_pos (v := fun _ : ι => 1) (by simp))
  have h2 := ne_of_gt (sphereArea_pos (ι := ι))
  have h3 := ne_of_gt (pow_pos hr (Fintype.card ι - 1))
  have h4 := ne_of_gt (Real.exp_pos (-r^2/2))
  field_simp

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_PartitionBounds
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

namespace CriticalSK

section

lemma log_le_square_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ (x^2-1)/2 := by
  have hh := Real.log_le_sub_one_of_pos (sq_pos_of_pos hx)
  rw [Real.log_pow] at hh
  norm_num at hh
  linarith

lemma gaussian_radial_shape_bound (p : ℕ) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hp : (p:ℝ) ≤ R) :
    r^p * Real.exp (-r^2/2) ≤
      Real.exp ((R-p)/2) * (Real.sqrt R)^p * Real.exp (-R/2) := by
  have hs := Real.sqrt_pos.mpr hR
  have hs2 := Real.sq_sqrt hR.le
  let x := r / Real.sqrt R
  have hx : 0 < x := div_pos hr hs
  have hxid : Real.sqrt R*x = r := by dsimp [x]; field_simp
  have hx2 : R*x^2 = r^2 := by nlinarith [sq_nonneg (Real.sqrt R*x-r)]
  have hlog := mul_le_mul_of_nonneg_left (log_le_square_half hx) (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  have hn : 0 ≤ (R-p)*x^2 := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg x)
  have he : (p:ℝ)*Real.log x-r^2/2 ≤ (R-p)/2-R/2 := by nlinarith
  have he' := Real.exp_le_exp.mpr he
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hx,Real.exp_sub] at he'
  have he'' : x^p * Real.exp (-r^2/2) ≤ Real.exp ((R-p)/2)*Real.exp (-R/2) := by
    rw [show -r^2/2 = -(r^2/2) by ring, show -R/2 = -(R/2) by ring, Real.exp_neg, Real.exp_neg]
    simpa only [div_eq_mul_inv] using he'
  calc
    r^p * Real.exp (-r^2/2) = (Real.sqrt R)^p*(x^p*Real.exp (-r^2/2)) := by
      rw [← mul_assoc,← mul_pow,hxid]
    _ ≤ (Real.sqrt R)^p*(Real.exp ((R-p)/2)*Real.exp (-R/2)) :=
      mul_le_mul_of_nonneg_left he'' (pow_nonneg hs.le _)
    _ = _ := by ring

open Set Filter

variable {ι : Type*} [Fintype ι]

lemma diagonalGaussian_normSq_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^2) (diagonalGaussian v) := by
  unfold diagonalGaussian
  apply (integrable_map_measure (by fun_prop) (WithLp.measurable_toLp 2 _).aemeasurable).mpr
  have hi := (piSquareSum_memLp v).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  unfold piSquareSum at hi
  simpa only [Function.comp_def,EuclideanSpace.real_norm_sq_eq] using hi

lemma diagonalGaussian_normSq_mean (v : ι → ℝ≥0) :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖^2 ∂diagonalGaussian v) = ∑ i, (v i : ℝ) := by
  rw [diagonalGaussian,integral_map (WithLp.measurable_toLp 2 _).aemeasurable (by fun_prop)]
  simpa only [EuclideanSpace.real_norm_sq_eq,piSquareSum] using piSquareSum_mean v

lemma diagonalGaussian_singleton_zero [Nonempty ι] (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v ({0} : Set (EuclideanSpace ℝ ι)) = 0 := by
  rw [diagonalGaussian_density v hv]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

lemma diagonalGaussian_standard_shell_half [Nonempty ι] :
    (1:ℝ)/2 ≤ (diagonalGaussian (fun _ : ι => 1) (normShell 0 (Real.sqrt (2*Fintype.card ι)))).toReal := by
  let μ := diagonalGaussian (fun _ : ι => 1)
  let A : Set (EuclideanSpace ℝ ι) := normShell 0 (Real.sqrt (2*Fintype.card ι))
  have hN : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have htail := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Eventually.of_forall (fun x : EuclideanSpace ℝ ι => sq_nonneg ‖x‖))
    (diagonalGaussian_normSq_integrable (fun _ => 1)) (2*Fintype.card ι)
  rw [diagonalGaussian_normSq_mean] at htail
  simp only [NNReal.coe_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at htail
  have hcomp : Aᶜ ⊆ ({0} : Set (EuclideanSpace ℝ ι)) ∪ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2} := by
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      change 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hh : Real.sqrt (2*Fintype.card ι) < ‖x‖ := by
        by_contra h
        exact hx ⟨hn,le_of_not_gt h⟩
      have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2*Fintype.card ι by positivity)
      have hspos := Real.sqrt_nonneg (2*(Fintype.card ι : ℝ))
      nlinarith
  have hcomp' : μ Aᶜ ≤ μ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2} := by
    apply (measure_mono hcomp).trans
    apply (measure_union_le _ _).trans
    rw [show μ ({0} : Set (EuclideanSpace ℝ ι)) = 0 from diagonalGaussian_singleton_zero _ (by simp),zero_add]
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hcomp'
  have hsum : (μ A).toReal+(μ Aᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl (normShell_measurable _ _),measure_univ,ENNReal.toReal_one]
  change 1/2 ≤ (μ A).toReal
  change 2*(Fintype.card ι : ℝ)*(μ {x | 2*(Fintype.card ι : ℝ) ≤ ‖x‖^2}).toReal ≤ Fintype.card ι at htail
  nlinarith

variable (n : ℕ)

lemma diagonalSquareDensity_standard_formula :
    diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) =
      (Real.sqrt (n+2))^n * gaussianPiPrefactor (fun _ : Fin (n+2) => 1) *
        Real.exp (-(n+2)/2) * sphereArea (ι := Fin (n+2)) / 2 := by
  rw [diagonalSquareDensity,radialDensity_standard]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ,
    Real.sq_sqrt (show (0:ℝ) ≤ n+2 by positivity)]
  field_simp

lemma standard_radial_density_upper {r : ℝ} (hr : 0 ≤ r) :
    radialDensity volume (fun x : EuclideanSpace ℝ (Fin (n+2)) => gaussianPiPDF (fun _ => 1) x) r ≤
      2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
  rw [radialDensity_standard,diagonalSquareDensity_standard_formula]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ]
  rcases hr.eq_or_lt with h | h
  · simp [← h]
  · have hp := gaussian_radial_shape_bound n (by positivity : (0:ℝ) < n+2) h (by linarith : (n:ℝ) ≤ n+2)
    rw [show ((n:ℝ)+2-n)/2=1 by ring] at hp
    have hmul := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ r*gaussianPiPrefactor (fun _ : Fin (n+2) => 1)*sphereArea (ι := Fin (n+2)) by
        exact mul_nonneg (mul_nonneg h.le (gaussianPiPrefactor_pos (by simp)).le) sphereArea_pos.le)
    convert hmul using 1 <;> first | rfl | ring_nf

lemma diagonalSquareDensity_standard_lower :
    1/(4*Real.exp 1*(n+2)) ≤ diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
  let R := Real.sqrt (2*((n:ℝ)+2))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*((n:ℝ)+2) := Real.sq_sqrt (by positivity)
  have hmass := diagonalGaussian_standard_shell_half (ι := Fin (n+2))
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hmass
  rw [diagonalGaussian_density _ (by simp),normShell_density_real volume
    (euclideanGaussianPDF_integrable _) (fun x => gaussianPiPDF_nonneg _ x.ofLp) (le_refl 0)] at hmass
  have hi := setIntegral_mono_on (μ := (volume : Measure ℝ)) (s := Ioc 0 R)
    ((radialDensity_continuous volume (euclideanGaussianPDF_continuous (fun _ : Fin (n+2) => 1))).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((show Continuous (fun r : ℝ => 2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2)) by fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    measurableSet_Ioc (fun r hr => standard_radial_density_upper n hr.1.le)
  have he : (∫ r in Ioc 0 R, 2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2)) =
      2*((n:ℝ)+2)*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
    rw [← intervalIntegral.integral_of_le hR,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,integral_id]
    rw [hR2]
    ring
  rw [he] at hi
  have hh : 1/2 ≤ 2*((n:ℝ)+2)*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) :=
    hmass.trans hi
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma saddleRadius_spec (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    spectralTop lam < saddleRadius lam a ∧ spectralStieltjes lam (saddleRadius lam a) = a := by
  simpa only [saddleRadius,dite_eq_left ha] using (spectralStieltjes_exists lam ha).choose_spec

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
    all_goals try with_reducible_and_instances rfl
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

end

section

open Set

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v) = -(∑ i, Real.log (2*Real.pi*(v i:ℝ)))/2 := by
  unfold gaussianPiPrefactor
  rw [Real.log_prod (fun i _ => inv_ne_zero (Real.sqrt_ne_zero'.mpr (by
    have hi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
    positivity)))]
  have hs (i : ι) : Real.log (Real.sqrt (2*Real.pi*(v i:ℝ))) = Real.log (2*Real.pi*(v i:ℝ))/2 :=
    Real.log_sqrt (by positivity)
  simp_rw [Real.log_inv,hs]
  simp only [Finset.sum_neg_distrib,← Finset.sum_div,neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log_ratio {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1)) =
      (∑ i, Real.log ((v i : ℝ)⁻¹))/2 := by
  rw [Real.log_div (gaussianPiPrefactor_pos hv).ne'
    (gaussianPiPrefactor_pos (v := fun _ : ι => 1) (by simp)).ne',
    gaussianPiPrefactor_log hv,gaussianPiPrefactor_log (v := fun _ : ι => 1) (by simp)]
  have hlog (i : ι) : Real.log (2*Real.pi*(v i:ℝ)) = Real.log (2*Real.pi)+Real.log (v i) :=
    Real.log_mul (by positivity) (NNReal.coe_ne_zero.mpr (hv i))
  simp_rw [hlog,NNReal.coe_one,mul_one,Real.log_inv]
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

lemma spherical_gaussian_identity {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i) :
    spherePartition lam a (Real.sqrt (Fintype.card ι)) =
      Real.exp ((Fintype.card ι : ℝ)*saddleObjective lam a z) *
        (diagonalSquareDensity v (Fintype.card ι) /
          diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι)) := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hs := Real.sqrt_pos.mpr hN
  have hr := spherical_radial_ratio hq hs
  have hp := gaussianPiPrefactor_log_ratio hv
  simp_rw [hq] at hp
  have he : gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1) *
      Real.exp (-(z-1)*(Real.sqrt (Fintype.card ι))^2/2) =
      Real.exp (-((Fintype.card ι : ℝ)*saddleObjective lam a z)) := by
    rw [← Real.exp_log (div_pos (gaussianPiPrefactor_pos hv) (gaussianPiPrefactor_pos (by simp))),
      ← Real.exp_add,hp,Real.sq_sqrt hN.le]
    congr 1
    unfold saddleObjective
    field_simp
    ring
  rw [he] at hr
  have hd : diagonalSquareDensity v (Fintype.card ι) /
      diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι) =
      radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) (Real.sqrt (Fintype.card ι)) /
        radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) (Real.sqrt (Fintype.card ι)) := by
    unfold diagonalSquareDensity
    rw [div_div_div_cancel_right₀ (mul_ne_zero two_ne_zero hs.ne')]
  rw [hd,hr,Real.exp_neg]
  field_simp

lemma saddleZ_le_bound (lam : ι → ℝ) {a C : ℝ} (ha : 0 ≤ a) (hlam : ∀ i, lam i ≤ C) :
    saddleZ lam a ≤ 1+a*C := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hlam i) (inv_pos.mpr (saddleZ_gap_pos lam ha i)).le)
  rw [← Finset.mul_sum,saddleZ_reciprocal_sum lam ha] at hs
  have hh := mul_le_mul_of_nonneg_left hs ha
  rw [← saddleZ_weighted_identity lam ha] at hh
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  nlinarith

lemma saddleVariance_coe (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    (saddleVariance lam a i : ℝ) = (saddleZ lam a-a*lam i)⁻¹ :=
  Real.coe_toNNReal _ (inv_pos.mpr (saddleZ_gap_pos lam ha i)).le

lemma saddleVariance_pos (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    0 < saddleVariance lam a i := by
  rw [← NNReal.coe_pos,saddleVariance_coe lam ha]
  exact inv_pos.mpr (saddleZ_gap_pos lam ha i)

lemma saddleVariance_lower (lam : ι → ℝ) {a : ℝ} (ha : a ∈ Icc 0 2)
    (hlam : ∀ i, |lam i| ≤ 3) (i : ι) : (1:ℝ)/13 ≤ saddleVariance lam a i := by
  rw [saddleVariance_coe lam ha.1]
  have hz := saddleZ_le_bound lam ha.1 (fun i => (abs_le.mp (hlam i)).2)
  have hi := (abs_le.mp (hlam i)).1
  have hm := mul_le_mul_of_nonneg_left hi ha.1
  have hg : saddleZ lam a-a*lam i ≤ 13 := by nlinarith [ha.2]
  simpa using inv_anti₀ (saddleZ_gap_pos lam ha.1 i) hg

lemma gaussianPairPrefactor_bound {a b : ℝ≥0} {c : ℝ} (hc : 0 < c)
    (ha : c⁻¹ ≤ (a:ℝ)) (hb : c⁻¹ ≤ (b:ℝ)) :
    Real.pi*gaussianPairPrefactor a b ≤ c/2 := by
  have hc' : 0 < 2*Real.pi/c := by positivity
  have h1 : Real.sqrt (2*Real.pi/c) ≤ Real.sqrt (2*Real.pi*a) :=
    Real.sqrt_le_sqrt (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2*Real.pi))
  have h2 : Real.sqrt (2*Real.pi/c) ≤ Real.sqrt (2*Real.pi*b) :=
    Real.sqrt_le_sqrt (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2*Real.pi))
  have hh := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← sq,Real.sq_sqrt hc'.le] at hh
  have hi := inv_anti₀ hc' hh
  have hp := mul_le_mul_of_nonneg_left hi Real.pi_pos.le
  unfold gaussianPairPrefactor
  convert hp using 1 <;> first | rfl | field_simp

variable (n : ℕ)

lemma spherePartition_upper (lam : Fin (n+2) → ℝ) {a : ℝ} (ha : a ∈ Icc 0 2)
    (hlam : ∀ i, |lam i| ≤ 3) :
    spherePartition lam a (Real.sqrt (n+2)) ≤
      26*Real.exp 1*(n+2)*Real.exp ((n+2)*sphericalVariational lam a) := by
  have hv : ∀ i, saddleVariance lam a i ≠ 0 := fun i => (saddleVariance_pos lam ha.1 i).ne'
  have hq (i) : (saddleVariance lam a i : ℝ)⁻¹ = saddleZ lam a-a*lam i := by
    rw [saddleVariance_coe lam ha.1,inv_inv]
  have hid := spherical_gaussian_identity hv hq
  rw [← sphericalVariational_eq lam ha.1] at hid
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] at hid
  rw [hid]
  have hu := (diagonalSquareDensity_upper (saddleVariance lam a) hv
    (by positivity : (0:ℝ) < n+2)).trans (gaussianPairPrefactor_bound (by norm_num : (0:ℝ) < 13)
      (by simpa using saddleVariance_lower lam ha hlam 0) (by simpa using saddleVariance_lower lam ha hlam 1))
  have hd := diagonalSquareDensity_standard_lower n
  have hdpos : 0 < diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) :=
    lt_of_lt_of_le (by positivity) hd
  have hratio : diagonalSquareDensity (saddleVariance lam a) (n+2) /
      diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) ≤ 26*Real.exp 1*(n+2) := by
    apply (div_le_iff₀ hdpos).mpr
    have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 26*Real.exp 1*((n:ℝ)+2) by positivity)
    have he : 26*Real.exp 1*((n:ℝ)+2)*(1/(4*Real.exp 1*((n:ℝ)+2))) = 13/2 := by field_simp; ring
    rw [he] at hm
    exact hu.trans hm
  have hh := mul_le_mul_of_nonneg_left hratio (Real.exp_pos (((n:ℝ)+2)*sphericalVariational lam a)).le
  simpa only [mul_comm] using hh

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_OrientationBounds
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



section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exp_midpoint_bound (A B : ℝ) : Real.exp ((A+B)/2) ≤ (Real.exp A+Real.exp B)/2 := by
  have he : Real.exp ((A+B)/2)*Real.cosh ((A-B)/2) = (Real.exp A+Real.exp B)/2 := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
    rw [show (A+B)/2+(A-B)/2=A by ring,
      show (A+B)/2+-((A-B)/2)=B by ring]
  rw [← he]
  exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh _)

omit [DecidableEq ι] in
lemma correlatedVector_gram {u v : EuclideanSpace ℝ ι} {r t : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) (ht : |t| ≤ 1) :
    ‖correlatedVector u v t‖ = r ∧ inner ℝ u (correlatedVector u v t) = t*r^2 := by
  have ht2 : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht2)
  have horth' : inner ℝ v u = 0 := by rw [real_inner_comm,horth]
  have huu : inner ℝ u u = r^2 := by rw [real_inner_self_eq_norm_sq,hu]
  have hvv : inner ℝ v v = r^2 := by rw [real_inner_self_eq_norm_sq,hv]
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  constructor
  · apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
    rw [← real_inner_self_eq_norm_sq]
    simp only [correlatedVector,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,horth,horth',huu,hvv]
    nlinarith
  · simp only [correlatedVector,inner_add_right,real_inner_smul_right,horth,huu,mul_zero,add_zero]

omit [DecidableEq ι] in
lemma correlatedEnergy_sign (lam : ι → ℝ) (u v : EuclideanSpace ℝ ι) (t : ℝ) :
    diagonalEnergy lam (correlatedVector u v t)+diagonalEnergy lam (correlatedVector u (-v) t) =
      2*(t^2*diagonalEnergy lam u+(Real.sqrt (1-t^2))^2*diagonalEnergy lam v) := by
  simp only [diagonalEnergy,correlatedVector,PiLp.add_apply,PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma correlatedMoment_sign (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι}
    (horth : inner ℝ u v = 0) (q t : ℝ) :
    pairMoment lam u (correlatedVector u (-v) t) q = pairMoment lam u (correlatedVector u v t) q := by
  have he := orthogonal_pair_integral_eq
    (fun x y => Real.exp (((1+q)*diagonalEnergy lam x+(1-q)*diagonalEnergy lam (correlatedVector x y t))/2))
    (x := u) (y := -v) (x' := u) (y' := v) rfl (norm_neg v)
    (by rw [inner_neg_right,horth,neg_zero])
  simpa only [pairMoment,pairIntegrand,correlatedVector,map_add,map_smul,map_neg] using he

lemma pairMoment_correlated_lower (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι}
    (hnorm : ‖u‖ = ‖v‖) (horth : inner ℝ u v = 0) {q t : ℝ}
    (hq : q ∈ Set.Icc 0 1) (ht : |t| ≤ 1) :
    pairMoment lam u v q ≤ pairMoment lam u (correlatedVector u v t) q := by
  let p := q+(1-q)*t^2
  have hpq : |q| ≤ |p| := (le_abs_self p).trans' (by
    rw [abs_of_nonneg hq.1]
    dsimp [p]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2) (sq_nonneg t)])
  apply (pairMoment_mono_abs lam hnorm hpq).trans
  have ht2 : t^2 ≤ 1 := by nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hs := Real.sq_sqrt (sub_nonneg.mpr ht2)
  have hpt (U : Matrix.orthogonalGroup ι ℝ) : pairIntegrand lam u v p U ≤
      (pairIntegrand lam u (correlatedVector u v t) q U+
        pairIntegrand lam u (correlatedVector u (-v) t) q U)/2 := by
    have hE := correlatedEnergy_sign lam (orthogonalIsometry U u) (orthogonalIsometry U v) t
    have hmid := exp_midpoint_bound
      (((1+q)*diagonalEnergy lam (orthogonalIsometry U u)+(1-q)*diagonalEnergy lam (correlatedVector (orthogonalIsometry U u) (orthogonalIsometry U v) t))/2)
      (((1+q)*diagonalEnergy lam (orthogonalIsometry U u)+(1-q)*diagonalEnergy lam (correlatedVector (orthogonalIsometry U u) (-(orthogonalIsometry U v)) t))/2)
    convert! hmid using 1
    · unfold pairIntegrand
      congr 1
      dsimp [p]
      rw [hs] at hE
      linear_combination -(1-q)/4*hE
    · simp only [pairIntegrand,correlatedVector,map_add,map_smul,map_neg]
  have hi := integral_mono (orthogonalHaar_integrable (pairIntegrand_continuous lam u v p))
    (((orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u v t) q)).add
      (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u (-v) t) q))).div_const 2) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_div,integral_add
    (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u v t) q))
    (orthogonalHaar_integrable (pairIntegrand_continuous lam u (correlatedVector u (-v) t) q))] at hi
  change pairMoment lam u v p ≤ (pairMoment lam u (correlatedVector u v t) q+
    pairMoment lam u (correlatedVector u (-v) t) q)/2 at hi
  rw [correlatedMoment_sign lam horth] at hi
  linarith

end


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pairMoment_min_at_orthogonal (lam : ι → ℝ) {u v x y : EuclideanSpace ℝ ι} {r t q : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (hx : ‖x‖ = r) (hy : ‖y‖ = r) (ht : |t| ≤ 1)
    (hxy : inner ℝ x y = t*r^2) (hq : q ∈ Set.Icc 0 1) :
    pairMoment lam u v q ≤ pairMoment lam x y q := by
  have hg := correlatedVector_gram hu hv horth ht
  have he := orthogonal_pair_integral_eq
    (fun x y => Real.exp (((1+q)*diagonalEnergy lam x+(1-q)*diagonalEnergy lam y)/2))
    (x := u) (y := correlatedVector u v t) (x' := x) (y' := y)
    (hu.trans hx.symm) (hg.1.trans hy.symm) (hg.2.trans hxy.symm)
  change pairMoment lam u (correlatedVector u v t) q = pairMoment lam x y q at he
  exact (pairMoment_correlated_lower lam (hu.trans hv.symm) horth hq ht).trans_eq he

variable [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereWeightedPair_factor (lam : ι → ℝ) (r q : ℝ) (p : unitSphere ι × unitSphere ι) :
    sphereWeightedPair lam r q p =
      Real.exp ((1+q)/2*diagonalEnergy lam (r • p.1.val))*
        Real.exp ((1-q)/2*diagonalEnergy lam (r • p.2.val)) := by
  rw [← Real.exp_add]
  unfold sphereWeightedPair
  congr 1
  ring

omit [DecidableEq ι] [Nonempty ι] in
lemma sphereWeightedPair_continuous (lam : ι → ℝ) (r q : ℝ) : Continuous (sphereWeightedPair lam r q) := by
  change Continuous (fun p => sphereWeightedPair lam r q p)
  simp_rw [sphereWeightedPair_factor]
  exact ((sphere_energy_continuous lam (1+q) r).comp continuous_fst).mul
    ((sphere_energy_continuous lam (1-q) r).comp continuous_snd)

omit [DecidableEq ι] in
lemma sphereWeightedPair_integral (lam : ι → ℝ) (r q : ℝ) :
    (∫ p, sphereWeightedPair lam r q p ∂(sphereUniform.prod sphereUniform)) =
      spherePartition lam (1+q) r * spherePartition lam (1-q) r := by
  simp_rw [sphereWeightedPair_factor]
  rw [integral_prod_mul (fun u : unitSphere ι => Real.exp ((1+q)/2*diagonalEnergy lam (r • u.val)))
    (fun v : unitSphere ι => Real.exp ((1-q)/2*diagonalEnergy lam (r • v.val))),
    sphereUniform_integral,sphereUniform_integral]
  rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma continuous_product_swap {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α × β → γ} (hf : Continuous f) :
    Continuous (fun z : β × α => f (z.2,z.1)) := hf.comp continuous_swap

omit [Nonempty ι] in
lemma spherePair_haar_continuous (f : unitSphere ι × unitSphere ι → ℝ) (hf : Continuous f) :
    Continuous (fun p : unitSphere ι × unitSphere ι =>
      ∫ U, f (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι) := by
  have hc0 : Continuous (fun z : Matrix.orthogonalGroup ι ℝ × (unitSphere ι × unitSphere ι) =>
      f (orthogonalSphere z.1 z.2.1,orthogonalSphere z.1 z.2.2)) :=
    hf.comp spherePair_action_continuous
  have hc := continuous_product_swap hc0
  simpa only [setIntegral_univ] using
    continuous_parametric_integral_of_continuous (μ := orthogonalHaar ι)
      (f := fun (p : unitSphere ι × unitSphere ι) U => f (orthogonalSphere U p.1,orthogonalSphere U p.2)) hc (s := Set.univ) isCompact_univ

lemma pairMoment_le_partition_product (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r q : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) (hq : q ∈ Set.Icc 0 1) :
    pairMoment lam u v q ≤ spherePartition lam (1+q) r * spherePartition lam (1-q) r := by
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hnorm (x : unitSphere ι) : ‖r • x.val‖ = r := by
    rw [norm_smul,Real.norm_of_nonneg hr,mem_sphere_zero_iff_norm.mp x.property,mul_one]
  have hle (p : unitSphere ι × unitSphere ι) : pairMoment lam u v q ≤
      ∫ U, sphereWeightedPair lam r q (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι := by
    have hxy : inner ℝ (r • p.1.val) (r • p.2.val) = inner ℝ p.1.val p.2.val*r^2 := by
      rw [real_inner_smul_left,real_inner_smul_right]
      ring
    have hh := pairMoment_min_at_orthogonal lam hu hv horth (hnorm p.1) (hnorm p.2)
      (sphere_inner_abs_le_one p.1 p.2) hxy hq
    simpa only [pairMoment,pairIntegrand,sphereWeightedPair,orthogonalSphere,sphereMap,map_smul] using hh
  have hc := spherePair_haar_continuous _ (sphereWeightedPair_continuous lam r q)
  have hi : Integrable (fun p : unitSphere ι × unitSphere ι =>
      ∫ U, sphereWeightedPair lam r q (orthogonalSphere U p.1,orthogonalSphere U p.2) ∂orthogonalHaar ι)
      (sphereUniform.prod sphereUniform) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  have hh := integral_mono (integrable_const (pairMoment lam u v q)) hi hle
  rw [integral_const,probReal_univ,one_smul,spherePair_haar_average _
    (sphereWeightedPair_continuous lam r q),sphereWeightedPair_integral] at hh
  exact hh

end

section

open Set

variable {n : ℕ}

lemma pairMoment_abs (lam : Fin (n+2) → ℝ) {u v : EuclideanSpace ℝ (Fin (n+2))}
    (h : ‖u‖ = ‖v‖) (q : ℝ) : pairMoment lam u v q = pairMoment lam u v |q| := by
  rcases le_or_gt 0 q with hp | hp
  · rw [abs_of_nonneg hp]
  · rw [abs_of_neg hp,pairMoment_even lam h]

lemma pairMoment_variational_upper (lam : Fin (n+2) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+2))} (hu : ‖u‖ = Real.sqrt (n+2))
    (hv : ‖v‖ = Real.sqrt (n+2)) (horth : inner ℝ u v = 0)
    (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
    (hlo : K*Real.exp ((n+2)*sphericalVariational lam 1) ≤
      spherePartition lam 1 (Real.sqrt (n+2))) :
    pairMoment lam u v q / spherePartition lam 1 (Real.sqrt (n+2))^2 ≤
      (26*Real.exp 1*(n+2)/K)^2 * Real.exp ((n+2)*saddlePairDeficit lam |q|) := by
  let S := spherePartition lam 1 (Real.sqrt (n+2))
  let A := 26*Real.exp 1*((n:ℝ)+2)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hm := pairMoment_le_partition_product lam hu hv horth (show |q| ∈ Set.Icc (0:ℝ) 1 from ⟨abs_nonneg _,hq⟩)
  rw [← pairMoment_abs lam (hu.trans hv.symm) q] at hm
  have hup := spherePartition_upper n lam (show 1+|q| ∈ Set.Icc (0:ℝ) 2 by constructor <;> linarith [abs_nonneg q]) hlam
  have hdown := spherePartition_upper n lam (show 1-|q| ∈ Set.Icc (0:ℝ) 2 by constructor <;> linarith [abs_nonneg q]) hlam
  have hprod := mul_le_mul hup hdown (spherePartition_pos lam (1-|q|) (Real.sqrt (n+2))).le (by positivity)
  have hupper : pairMoment lam u v q ≤ A^2 * Real.exp (((n:ℝ)+2)*
      (sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|))) := by
    calc
      _ ≤ _ := hm.trans hprod
      _ = A^2 * Real.exp (((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|))) := by
        rw [mul_add (((n:ℝ)+2)) (sphericalVariational lam (1+|q|)) (sphericalVariational lam (1-|q|)),Real.exp_add]
        dsimp only [A]
        ring
  have hlower : (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 ≤ S^2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hpos : 0 < (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 := by positivity
  calc
    pairMoment lam u v q / S^2 ≤
        (A^2 * Real.exp (((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|)))) /
          (K*Real.exp (((n:ℝ)+2)*sphericalVariational lam 1))^2 :=
      div_le_div₀ (by positivity) hupper hpos hlower
    _ = _ := by
      have he : ((n:ℝ)+2)*saddlePairDeficit lam |q| =
          ((n:ℝ)+2)*(sphericalVariational lam (1+|q|)+sphericalVariational lam (1-|q|)) -
            2*(((n:ℝ)+2)*sphericalVariational lam 1) := by unfold saddlePairDeficit; ring
      rw [he,Real.exp_sub,two_mul,Real.exp_add]
      dsimp only [A]
      field_simp

end

open Set MeasureTheory Filter

lemma pairMoment_variational_upper_general_s2_oai {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = Real.sqrt n)
    (hv : ‖v‖ = Real.sqrt n) (horth : inner ℝ u v = 0)
    (hlam : ∀ i, |lam i| ≤ 3) {q K : ℝ} (hq : |q| ≤ 1) (hK : 0 < K)
    (hlo : K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n)) :
    pairMoment lam u v q / spherePartition lam 1 (Real.sqrt n)^2 ≤
      (26*Real.exp 1*n/K)^2 * Real.exp ((n:ℝ)*saddlePairDeficit lam |q|) := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  simpa only [Nat.cast_add,Nat.cast_ofNat] using pairMoment_variational_upper lam (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hu) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hv) horth hlam hq hK (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hlo)

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.pairMoment_variational_upper_general_s2_oai := @OAI.CriticalSK.pairMoment_variational_upper_general_s2_oai
