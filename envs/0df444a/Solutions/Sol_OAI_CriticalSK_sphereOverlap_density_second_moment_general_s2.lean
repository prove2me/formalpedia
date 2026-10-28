-- Prove2me | solution 1 for OAI.CriticalSK.sphereOverlap_density_second_moment_general_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:11:07.607698+00:00
-- url     : https://prove2.me/submissions/91fd4db6-644d-425a-ba34-acf7102000be

import Mathlib
import Definitions.Def_OAIQ074C000

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

lemma orthogonalSphere_transitive (u w : unitSphere ι) :
    ∃ U : Matrix.orthogonalGroup ι ℝ, orthogonalSphere U u = w := by
  obtain ⟨U,hU⟩ := orthogonal_transitive
    ((mem_sphere_zero_iff_norm.mp u.property).trans (mem_sphere_zero_iff_norm.mp w.property).symm)
  exact ⟨U, Subtype.ext hU⟩

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

omit [DecidableEq ι] in
lemma diagonalEnergy_continuous (lam : ι → ℝ) : Continuous (diagonalEnergy lam) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((PiLp.continuous_apply 2 _ i).pow 2)

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

omit [DecidableEq ι] [Nonempty ι] in
lemma spherePairEnergy_factor (lam : ι → ℝ) (r : ℝ) (p : unitSphere ι × unitSphere ι) :
    spherePairEnergy lam r p =
      Real.exp (1 / 2 * diagonalEnergy lam (r • p.1.val)) *
      Real.exp (1 / 2 * diagonalEnergy lam (r • p.2.val)) := by
  rw [← Real.exp_add]
  unfold spherePairEnergy
  congr 1
  ring

omit [DecidableEq ι] [Nonempty ι] in
lemma spherePairEnergy_continuous (lam : ι → ℝ) (r : ℝ) : Continuous (spherePairEnergy lam r) := by
  have hf := sphere_energy_continuous lam 1 r
  have he : spherePairEnergy lam r = fun p : unitSphere ι × unitSphere ι =>
      Real.exp (1 / 2 * diagonalEnergy lam (r • p.1.val)) *
      Real.exp (1 / 2 * diagonalEnergy lam (r • p.2.val)) := funext (spherePairEnergy_factor lam r)
  rw [he]
  exact (hf.comp continuous_fst).mul (hf.comp continuous_snd)

omit [DecidableEq ι] in
lemma spherePairEnergy_integral (lam : ι → ℝ) (r : ℝ) :
    (∫ p, spherePairEnergy lam r p ∂(sphereUniform.prod sphereUniform)) =
      (spherePartition lam 1 r)^2 := by
  simp_rw [spherePairEnergy_factor]
  let f : unitSphere ι → ℝ := fun u => Real.exp (1 / 2 * diagonalEnergy lam (r • u.val))
  change (∫ p, f p.1 * f p.2 ∂((sphereUniform (ι := ι)).prod sphereUniform)) = _
  rw [integral_prod_mul f f, sphereUniform_integral]
  exact (pow_two _).symm

lemma spectrum_pair_second_moment (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ p : unitSphere ι × unitSphere ι, pairMoment lam u v (inner ℝ p.1.val p.2.val)
      ∂(sphereUniform.prod sphereUniform)) = (spherePartition lam 1 r)^2 := by
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hnorm (x : unitSphere ι) : ‖r • x.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, mem_sphere_zero_iff_norm.mp x.property, mul_one]
  have he (p : unitSphere ι × unitSphere ι) :
      pairMoment lam u v (inner ℝ p.1.val p.2.val) =
        ∫ U, spherePairEnergy lam r (orthogonalSphere U p.1, orthogonalSphere U p.2)
          ∂orthogonalHaar ι := by
    have hxy : inner ℝ (r • p.1.val) (r • p.2.val) = inner ℝ p.1.val p.2.val * r^2 := by
      rw [real_inner_smul_left, real_inner_smul_right]
      ring
    rw [← pair_energy_orbit lam (hnorm p.1) (hnorm p.2) hu hv horth
      (sphere_inner_abs_le_one p.1 p.2) hxy]
    apply integral_congr_ae
    filter_upwards [] with U
    simp only [spherePairEnergy, orthogonalSphere, sphereMap, map_smul]
  simp_rw [he]
  rw [spherePair_haar_average _ (spherePairEnergy_continuous lam r), spherePairEnergy_integral]

lemma sphereOverlap_second_moment (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q, pairMoment lam u v q ∂sphereOverlapLaw ι) = (spherePartition lam 1 r)^2 := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι => inner ℝ p.1.val p.2.val) :=
    (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
  rw [sphereOverlapLaw, integral_map hc.measurable.aemeasurable
    (pairMoment_continuous lam u v).aestronglyMeasurable]
  exact spectrum_pair_second_moment lam hu hv horth

end

section

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma radial_map_preserving (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) μ := by
  have hs : MeasurePreserving (Subtype.val : ({(0)}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    simpa only [restrict_compl_singleton] using
      (measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl)
  exact hs.comp (MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    μ.measurePreserving_homeomorphUnitSphereProd)

lemma lintegral_polar (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      f (p.2.val • p.1.val) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)) :=
  ((radial_map_preserving μ).lintegral_comp hf).symm

end

section

lemma radialGaussian_finite (n : ℕ) : radialGaussian n < ⊤ := by
  apply Integrable.lintegral_lt_top
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg (n-1)))
  simp only [Real.rpow_natCast, neg_one_mul] at h
  change Integrable _ (volume.restrict (Ioi 0)) at h
  exact h

lemma radialGaussian_pos (n : ℕ) : 0 < radialGaussian n := by
  rw [radialGaussian, setLIntegral_pos_iff (by fun_prop)]
  have he : Function.support (fun r : ℝ => ENNReal.ofReal (r^(n-1) * Real.exp (-r^2))) ∩
      Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro r hr
    exact (ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hr _) (Real.exp_pos _))).ne'
  rw [he, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

lemma lintegral_scale_pos {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x, f x) = ∫⁻ t : ℝ, ENNReal.ofReal a * f (a*t) := by
  have hi : (fun t : ℝ => a*t) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (fun x => ⟨x/a, mul_div_cancel₀ x ha.ne'⟩)
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f' := fun _ => a) MeasurableSet.univ
    (fun t _ => by convert! ((hasDerivAt_id t).const_mul a).hasDerivWithinAt (s := Set.univ) using 1; simp only [mul_one])
    (mul_right_injective₀ ha.ne').injOn f
  simpa only [hi, setLIntegral_univ, abs_of_pos ha] using h

lemma lintegral_scale_pos_Ioi {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi 0, f x) = ∫⁻ t in Ioi 0, ENNReal.ofReal a * f (a*t) := by
  have hi : (fun t : ℝ => a*t) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mul_pos ha ht
    · intro hx
      exact ⟨x/a, div_pos hx ha, mul_div_cancel₀ x ha.ne'⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f' := fun _ => a) measurableSet_Ioi
    (fun t _ => by convert! ((hasDerivAt_id t).const_mul a).hasDerivWithinAt (s := Ioi (0 : ℝ)) using 1; simp only [mul_one])
    (mul_right_injective₀ ha.ne').injOn f
  simpa only [hi, abs_of_pos ha] using h

lemma radialGaussian_scaled (k : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^k * Real.exp (-(c*r)^2))) =
      ENNReal.ofReal (c⁻¹^(k+1)) * radialGaussian (k+1) := by
  rw [lintegral_scale_pos_Ioi (inv_pos.mpr hc)]
  have he (r : ℝ) :
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal ((c⁻¹*r)^k * Real.exp (-(c*(c⁻¹*r))^2)) =
        ENNReal.ofReal (c⁻¹^(k+1)) * ENNReal.ofReal (r^k * Real.exp (-r^2)) := by
    rw [mul_inv_cancel_left₀ hc.ne', mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hc.le) _)]
    congr 1
    rw [pow_succ]
    ring
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma radialGaussian_polar (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ≥0∞}
    (hg : Measurable g) (hhom : ∀ (r : ℝ), 0 < r → ∀ x : E, g (r • x) = g x) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-‖x‖^2)) * g x ∂μ) =
      (∫⁻ u : sphere (0 : E) 1, g u.val ∂μ.toSphere) * radialGaussian (Module.finrank ℝ E) := by
  rw [lintegral_polar μ (by fun_prop)]
  have he (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
      ENNReal.ofReal (Real.exp (-‖p.2.val • p.1.val‖^2)) * g (p.2.val • p.1.val) =
      g p.1.val * ENNReal.ofReal (Real.exp (-p.2.val^2)) := by
    rw [hhom _ p.2.property, norm_smul, Real.norm_of_nonneg p.2.property.le,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one, mul_comm]
  simp_rw [he]
  rw [lintegral_prod_mul (f := fun u : sphere (0 : E) 1 => g u.val)
    (g := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (Real.exp (-r.val^2))) (by fun_prop) (by fun_prop)]
  congr 1
  rw [volumeIoiPow, lintegral_withDensity_eq_lintegral_mul
    (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val^(Module.finrank ℝ E-1)))
    (g := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (Real.exp (-r.val^2))) _ (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.val^(Module.finrank ℝ E-1) * Real.exp (-r.val^2))
        ∂volume.comap Subtype.val := by
      apply lintegral_congr
      intro r
      exact (ENNReal.ofReal_mul (pow_nonneg r.property.le _)).symm
    _ = _ := lintegral_subtype_comap (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r^(Module.finrank ℝ E-1) * Real.exp (-r^2)))

end

lemma volumeIoiPow_lintegral (k : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r : Ioi (0 : ℝ), f r.val ∂volumeIoiPow k) =
      ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^k) * f r := by
  rw [volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _
    (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val^k))
    (g := fun r : Ioi (0 : ℝ) => f r.val) (by fun_prop) (by fun_prop)]
  exact lintegral_subtype_comap (μ := volume) (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun r : ℝ => ENNReal.ofReal (r^k) * f r)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma lintegral_radial_norm (μ : Measure E) [μ.IsAddHaarMeasure] {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f ‖x‖ ∂μ) = μ.toSphere Set.univ *
      ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(Module.finrank ℝ E-1)) * f r := by
  rw [lintegral_polar μ (f := fun x => f ‖x‖) (by fun_prop)]
  have he (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
      f ‖p.2.val • p.1.val‖ = (1 : ℝ≥0∞) * f p.2.val := by
    rw [norm_smul, Real.norm_of_nonneg p.2.property.le,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one, one_mul]
  simp_rw [he]
  rw [lintegral_prod_mul (f := fun _ : sphere (0 : E) 1 => (1 : ℝ≥0∞))
    (g := fun r : Ioi (0 : ℝ) => f r.val) (by fun_prop) (by fun_prop),
    lintegral_const, one_mul, volumeIoiPow_lintegral _ hf]

end

lemma sphereRatio_den_pos (t : ℝ) : 0 < 1+t^2 := by positivity

lemma sphereRatio_sq (t : ℝ) : sphereRatio t ^ 2 = t^2/(1+t^2) := by
  rw [sphereRatio, div_pow, Real.sq_sqrt (sphereRatio_den_pos t).le]

lemma one_sub_sphereRatio_sq (t : ℝ) : 1-sphereRatio t ^ 2 = 1/(1+t^2) := by
  rw [sphereRatio_sq]
  field_simp
  ring

lemma sphereRatio_mem (t : ℝ) : sphereRatio t ∈ Ioo (-1 : ℝ) 1 := by
  have hp : 0 < 1-sphereRatio t^2 := by rw [one_sub_sphereRatio_sq]; positivity
  constructor <;> nlinarith [sq_nonneg (sphereRatio t + 1), sq_nonneg (sphereRatio t - 1)]

lemma sphereRatioInv_den_pos {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    0 < 1-q^2 := by nlinarith [hq.1, hq.2]

lemma one_add_sphereRatioInv_sq {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    1+sphereRatioInv q ^ 2 = 1/(1-q^2) := by
  rw [sphereRatioInv, div_pow, Real.sq_sqrt (sphereRatioInv_den_pos hq).le]
  field_simp [(sphereRatioInv_den_pos hq).ne']
  ring

lemma sphereRatio_left_inverse (t : ℝ) : sphereRatioInv (sphereRatio t) = t := by
  unfold sphereRatioInv
  rw [one_sub_sphereRatio_sq, Real.sqrt_div (by norm_num), Real.sqrt_one]
  unfold sphereRatio
  simpa only [div_one] using
    div_div_div_cancel_right₀ (Real.sqrt_ne_zero'.mpr (sphereRatio_den_pos t)) t 1

lemma sphereRatio_right_inverse {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    sphereRatio (sphereRatioInv q) = q := by
  unfold sphereRatio
  rw [one_add_sphereRatioInv_sq hq, Real.sqrt_div (by norm_num), Real.sqrt_one]
  unfold sphereRatioInv
  simpa only [div_one] using
    div_div_div_cancel_right₀ (Real.sqrt_ne_zero'.mpr (sphereRatioInv_den_pos hq)) q 1

lemma sphereRatioInv_injOn : Set.InjOn sphereRatioInv (Ioo (-1 : ℝ) 1) := by
  intro q hq r hr he
  have := congrArg sphereRatio he
  simpa only [sphereRatio_right_inverse hq, sphereRatio_right_inverse hr] using this

lemma sphereRatioInv_image : sphereRatioInv '' Ioo (-1 : ℝ) 1 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact ⟨sphereRatio t, sphereRatio_mem t, sphereRatio_left_inverse t⟩

lemma sphereRatioInv_hasDerivAt {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt sphereRatioInv (1/(Real.sqrt (1-q^2))^3) q := by
  have hder := (hasDerivAt_id q).div
    (((hasDerivAt_const q 1).sub ((hasDerivAt_id q).pow 2)).sqrt
      (sphereRatioInv_den_pos hq).ne')
    (Real.sqrt_ne_zero'.mpr (sphereRatioInv_den_pos hq))
  convert! hder using 1
  all_goals try with_reducible_and_instances rfl
  have hs := Real.sq_sqrt (sphereRatioInv_den_pos hq).le
  have hn := (Real.sqrt_ne_zero'.mpr (sphereRatioInv_den_pos hq))
  dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, mul_one, zero_sub]
  field_simp [hn]
  nlinarith

lemma sphereRatioInv_jacobian_shape {n : ℕ} (hn : 3 ≤ n) {q : ℝ}
    (hq : q ∈ Ioo (-1 : ℝ) 1) :
    |1/(Real.sqrt (1-q^2))^3| * (Real.sqrt (1+sphereRatioInv q^2))⁻¹ ^ n =
      sphereOverlapShape n q := by
  have hs : 0 < Real.sqrt (1-q^2) := Real.sqrt_pos.mpr (sphereRatioInv_den_pos hq)
  rw [abs_of_pos (by positivity), one_add_sphereRatioInv_sq hq,
    Real.sqrt_div (by norm_num), Real.sqrt_one]
  simp only [one_div, inv_inv]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (pow_sub₀ _ hs.ne' hn).symm

lemma sphereRatio_integral {n : ℕ} (hn : 3 ≤ n) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ENNReal.ofReal ((Real.sqrt (1+t^2))⁻¹ ^ n) * f (sphereRatio t)) =
      ∫⁻ q in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sphereOverlapShape n q) * f q := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun q hq => (sphereRatioInv_hasDerivAt hq).hasDerivWithinAt) sphereRatioInv_injOn
    (fun t => ENNReal.ofReal ((Real.sqrt (1+t^2))⁻¹ ^ n) * f (sphereRatio t))
  rw [sphereRatioInv_image, setLIntegral_univ] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro q hq
  dsimp only
  rw [sphereRatio_right_inverse hq, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    sphereRatioInv_jacobian_shape hn hq]

lemma scaled_ratio {r : ℝ} (hr : 0 < r) (t : ℝ) :
    r*t / Real.sqrt ((r*t)^2+r^2) = sphereRatio t := by
  rw [show (r*t)^2+r^2 = r^2*(1+t^2) by ring,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  exact mul_div_mul_left t _ hr.ne'

lemma cylinderKernel_scaled {r : ℝ} (hr : 0 < r) (t : ℝ) (f : ℝ → ℝ≥0∞) :
    cylinderKernel f (r*t) r =
      ENNReal.ofReal (Real.exp (-(Real.sqrt (1+t^2)*r)^2)) * f (sphereRatio t) := by
  unfold cylinderKernel
  rw [scaled_ratio hr]
  congr 3
  simp only [mul_pow, Real.sq_sqrt (sphereRatio_den_pos t).le]
  ring

lemma cylinder_scalar_scale {f : ℝ → ℝ≥0∞} {r : ℝ} (hr : 0 < r) :
    (∫⁻ s : ℝ, cylinderKernel f s r) =
      ENNReal.ofReal r * ∫⁻ t : ℝ,
        ENNReal.ofReal (Real.exp (-(Real.sqrt (1+t^2)*r)^2)) * f (sphereRatio t) := by
  rw [lintegral_scale_pos hr]
  simp_rw [cylinderKernel_scaled hr]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma cylinder_radius_integral (k : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^k) * ∫⁻ s : ℝ, cylinderKernel f s r) =
      radialGaussian (k+2) * ∫⁻ t : ℝ,
        ENNReal.ofReal ((Real.sqrt (1+t^2))⁻¹^(k+2)) * f (sphereRatio t) := by
  calc
    _ = ∫⁻ r : ℝ in Ioi 0, ∫⁻ t : ℝ, ENNReal.ofReal (r^(k+1)) *
        (ENNReal.ofReal (Real.exp (-(Real.sqrt (1+t^2)*r)^2)) * f (sphereRatio t)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [cylinder_scalar_scale hr, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _),
        ← pow_succ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ t : ℝ, ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(k+1)) *
        (ENNReal.ofReal (Real.exp (-(Real.sqrt (1+t^2)*r)^2)) * f (sphereRatio t)) := by
      apply lintegral_lintegral_swap
      unfold sphereRatio
      fun_prop
    _ = ∫⁻ t : ℝ, ENNReal.ofReal ((Real.sqrt (1+t^2))⁻¹^(k+2)) *
        radialGaussian (k+2) * f (sphereRatio t) := by
      apply lintegral_congr
      intro t
      calc
        _ = (∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(k+1) * Real.exp (-(Real.sqrt (1+t^2)*r)^2))) *
            f (sphereRatio t) := by
          rw [← lintegral_mul_const _ (by fun_prop)]
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro r hr
          dsimp only
          rw [ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_assoc]
        _ = _ := by rw [radialGaussian_scaled _ (Real.sqrt_pos.mpr (sphereRatio_den_pos t))]
    _ = _ := by
      simp_rw [mul_assoc, mul_left_comm _ (radialGaussian (k+2))]
      exact lintegral_const_mul' _ _ (radialGaussian_finite _).ne

lemma euclidSplit_preserving (n : ℕ) :
    MeasurePreserving (euclidSplit n) volume (volume.prod volume) := by
  have hs := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0).comp
    (PiLp.volume_preserving_ofLp (Fin (n+1)))
  have ht := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  exact ht.comp hs

lemma euclidSplit_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ‖x‖^2 = (euclidSplit n x).1^2 + ‖(euclidSplit n x).2‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, EuclideanSpace.norm_sq_eq]
  simp only [euclidSplit, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]

lemma euclidSplit_integral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin (n+1)),
      ENNReal.ofReal (Real.exp (-‖x‖^2)) * f (x 0 / ‖x‖)) =
    ∫⁻ p : ℝ × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (Real.exp (-(p.1^2 + ‖p.2‖^2))) *
        f (p.1 / Real.sqrt (p.1^2 + ‖p.2‖^2)) ∂volume.prod volume := by
  have hm : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.exp (-(p.1^2 + ‖p.2‖^2))) *
        f (p.1 / Real.sqrt (p.1^2 + ‖p.2‖^2))) := by fun_prop
  rw [← (euclidSplit_preserving n).lintegral_comp hm]
  apply lintegral_congr
  intro x
  rw [← euclidSplit_norm_sq, Real.sqrt_sq (norm_nonneg x)]
  rfl

lemma gaussian_cylinder_volume (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin (n+3)),
      ENNReal.ofReal (Real.exp (-‖x‖^2)) * f (x 0 / ‖x‖)) =
    (volume : Measure (EuclideanSpace ℝ (Fin (n+2)))).toSphere Set.univ *
      radialGaussian (n+3) * ∫⁻ t : ℝ,
        ENNReal.ofReal ((Real.sqrt (1+t^2))⁻¹^(n+3)) * f (sphereRatio t) := by
  rw [euclidSplit_integral (n+2) hf]
  change (∫⁻ p : ℝ × EuclideanSpace ℝ (Fin (n+2)), cylinderKernel f p.1 ‖p.2‖
    ∂volume.prod volume) = _
  rw [lintegral_prod _ (by unfold cylinderKernel; fun_prop)]
  have ht (s : ℝ) : (∫⁻ y : EuclideanSpace ℝ (Fin (n+2)), cylinderKernel f s ‖y‖) =
      (volume : Measure (EuclideanSpace ℝ (Fin (n+2)))).toSphere Set.univ *
        ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(n+1)) * cylinderKernel f s r := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, show n+2-1=n+1 by omega] using
      (lintegral_radial_norm (volume : Measure (EuclideanSpace ℝ (Fin (n+2))))
        (f := fun r => cylinderKernel f s r) (by unfold cylinderKernel; fun_prop))
  simp_rw [ht]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
  calc
    _ = (volume : Measure (EuclideanSpace ℝ (Fin (n+2)))).toSphere Set.univ *
        ∫⁻ r : ℝ in Ioi 0, ENNReal.ofReal (r^(n+1)) * ∫⁻ s : ℝ, cylinderKernel f s r := by
      congr 1
      rw [lintegral_lintegral_swap (by unfold cylinderKernel Function.uncurry; fun_prop)]
      apply lintegral_congr
      intro r
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [cylinder_radius_integral _ hf, ← mul_assoc]

lemma gaussian_coordinate_polar (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin (n+3)),
      ENNReal.ofReal (Real.exp (-‖x‖^2)) * f (x 0 / ‖x‖)) =
    (∫⁻ u : sphere (0 : EuclideanSpace ℝ (Fin (n+3))) 1,
      f (u.val 0) ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+3)))).toSphere) *
        radialGaussian (n+3) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin (n+3)) => f (x 0 / ‖x‖)) := by fun_prop
  have hhom (r : ℝ) (hr : 0 < r) (x : EuclideanSpace ℝ (Fin (n+3))) :
      f ((r • x) 0 / ‖r • x‖) = f (x 0 / ‖x‖) := by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    change f (r * x 0 / (r * ‖x‖)) = _
    rw [mul_div_mul_left _ _ hr.ne']
  have h := radialGaussian_polar volume hm hhom
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    mem_sphere_zero_iff_norm.mp (Subtype.property _), div_one] at h
  exact h

lemma sphere_coordinate_lintegral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u : sphere (0 : EuclideanSpace ℝ (Fin (n+3))) 1,
      f (u.val 0) ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+3)))).toSphere) =
    (volume : Measure (EuclideanSpace ℝ (Fin (n+2)))).toSphere Set.univ *
      ∫⁻ q in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sphereOverlapShape (n+3) q) * f q := by
  apply (ENNReal.mul_left_inj (radialGaussian_pos (n+3)).ne' (radialGaussian_finite (n+3)).ne).mp
  rw [← gaussian_coordinate_polar n hf, gaussian_cylinder_volume n hf,
    sphereRatio_integral (by omega : 3 ≤ n+3)]
  ac_rfl

lemma overlapShapeMeasure_lintegral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂overlapShapeMeasure n) =
      ∫⁻ q in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sphereOverlapShape n q) * f q := by
  rw [overlapShapeMeasure, lintegral_withDensity_eq_lintegral_mul _ (by unfold sphereOverlapShape; fun_prop) hf]
  rfl

lemma overlapShapeMeasure_univ (n : ℕ) :
    overlapShapeMeasure n Set.univ = ∫⁻ q in Ioo (-1 : ℝ) 1, ENNReal.ofReal (sphereOverlapShape n q) := by
  rw [← lintegral_one, overlapShapeMeasure_lintegral n measurable_const]
  simp only [mul_one]

lemma sphereUniform_coordinate_lintegral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u : unitSphere (Fin (n+3)), f (u.val 0) ∂sphereUniform) =
      ∫⁻ q, f q ∂normalizedOverlapShape (n+3) := by
  let A := (volume : Measure (EuclideanSpace ℝ (Fin (n+2)))).toSphere Set.univ
  have hA0 : A ≠ 0 := (measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne'
  have hAt : A ≠ ⊤ := measure_ne_top _ _
  have hfull : (volume : Measure (EuclideanSpace ℝ (Fin (n+3)))).toSphere Set.univ =
      A * overlapShapeMeasure (n+3) Set.univ := by
    have h := sphere_coordinate_lintegral n (f := fun _ => 1) measurable_const
    simpa only [lintegral_one, mul_one, overlapShapeMeasure_univ, A] using h
  rw [sphereUniform, lintegral_smul_measure, smul_eq_mul, sphere_coordinate_lintegral n hf,
    hfull, ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), normalizedOverlapShape,
    lintegral_smul_measure, smul_eq_mul, overlapShapeMeasure_lintegral _ hf]
  change (A⁻¹ * (overlapShapeMeasure (n+3) Set.univ)⁻¹) * (A * _) = _
  rw [mul_assoc, mul_left_comm _ A, ENNReal.inv_mul_cancel_left hA0 hAt]

lemma sphere_inner_coordinate_lintegral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (u : unitSphere (Fin (n+1))) :
    (∫⁻ v : unitSphere (Fin (n+1)), f (inner ℝ u.val v.val) ∂sphereUniform) =
      ∫⁻ v : unitSphere (Fin (n+1)), f (v.val 0) ∂sphereUniform := by
  obtain ⟨U, hU⟩ := orthogonalSphere_transitive (firstUnit n) u
  have hm : Measurable (fun v : unitSphere (Fin (n+1)) => f (inner ℝ u.val v.val)) := by fun_prop
  rw [← (sphereUniform_rotation_preserving U).lintegral_comp hm]
  apply lintegral_congr
  intro v
  congr 1
  rw [← hU]
  change inner ℝ (orthogonalIsometry U (firstUnit n).val) (orthogonalIsometry U v.val) = _
  rw [(orthogonalIsometry U).inner_map_map]
  simp only [firstUnit, EuclideanSpace.inner_single_left, map_one, one_mul]

lemma sphereOverlapLaw_lintegral (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂sphereOverlapLaw (Fin (n+3))) =
      ∫⁻ q, f q ∂normalizedOverlapShape (n+3) := by
  rw [sphereOverlapLaw, lintegral_map hf (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  simp_rw [sphere_inner_coordinate_lintegral (n+2) hf]
  rw [lintegral_const, measure_univ, mul_one, sphereUniform_coordinate_lintegral n hf]

lemma sphereOverlapLaw_density (n : ℕ) :
    sphereOverlapLaw (Fin (n+3)) = normalizedOverlapShape (n+3) := by
  apply Measure.ext_of_lintegral
  exact fun _ hf => sphereOverlapLaw_lintegral n hf

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_CubeOverlap
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
namespace CriticalSK

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

open MeasureTheory Set

lemma integral_shape_on_Ioo {n : ℕ} (hn : 4 ≤ n) (h : ℝ → ℝ) :
    (∫ q in Ioo (-1:ℝ) 1, h q*sphereOverlapShape n q) = ∫ q, h q*sphereOverlapShape n q := by
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Ioo (-1:ℝ) 1
  · simp only [indicator_of_mem hq]
  · have hqs : 1 ≤ |q| := by
      rw [Set.mem_Ioo,not_and_or] at hq
      rcases hq with hq | hq
      · exact (le_neg_of_le_neg (le_of_not_gt hq)).trans (neg_le_abs q)
      · exact (le_of_not_gt hq).trans (le_abs_self q)
    simp only [indicator_of_notMem hq,sphereOverlapShape_eq_zero hn hqs,mul_zero]

lemma overlapShapeMeasure_real_univ {n : ℕ} (hn : 4 ≤ n) :
    (overlapShapeMeasure n Set.univ).toReal = ∫ q, sphereOverlapShape n q := by
  rw [overlapShapeMeasure_univ,← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (sphereOverlapShape_nonneg n))
    (sphereOverlapShape_continuous n).aestronglyMeasurable]
  simpa only [one_mul] using integral_shape_on_Ioo hn (fun _ => 1)

lemma normalizedOverlapShape_integral {n : ℕ} (hn : 4 ≤ n) (h : ℝ → ℝ) :
    (∫ q, h q ∂normalizedOverlapShape n) = ∫ q, h q*sphereOverlapDensity n q := by
  rw [normalizedOverlapShape,integral_smul_measure,ENNReal.toReal_inv,
    overlapShapeMeasure_real_univ hn]
  rw [overlapShapeMeasure,integral_withDensity_eq_integral_toReal_smul
    (by unfold sphereOverlapShape; fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (sphereOverlapShape_nonneg _ _), smul_eq_mul]
  simp_rw [mul_comm (sphereOverlapShape n _)]
  rw [integral_shape_on_Ioo hn,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  unfold sphereOverlapDensity
  ring

lemma sphereOverlap_density_second_moment (n : ℕ) (lam : Fin (n+4) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+4))} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, pairMoment lam u v q*sphereOverlapDensity (n+4) q) = spherePartition lam 1 r^2 := by
  rw [← normalizedOverlapShape_integral (by omega : 4 ≤ n+4),← sphereOverlapLaw_density (n+1)]
  exact sphereOverlap_second_moment lam hu hv horth

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



open Set MeasureTheory Filter

lemma sphereOverlap_density_second_moment_general_s2_oai {n : ℕ} (hn : 4 ≤ n) (lam : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, pairMoment lam u v q*sphereOverlapDensity n q) = spherePartition lam 1 r^2 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hm
  subst n
  exact sphereOverlap_density_second_moment m lam hu hv horth

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.sphereOverlap_density_second_moment_general_s2_oai := @OAI.CriticalSK.sphereOverlap_density_second_moment_general_s2_oai
