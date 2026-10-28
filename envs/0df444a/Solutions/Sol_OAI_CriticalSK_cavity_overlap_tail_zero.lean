-- Prove2me | solution 1 for OAI.CriticalSK.cavity_overlap_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:34:55.892792+00:00
-- url     : https://prove2.me/submissions/d688339b-5b61-453f-b817-aa8aa32e887f

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK001
import Theorems.Thm_OAI_CriticalSK_spectralGood_natural_sphere_bounds
import Theorems.Thm_OAI_CriticalSK_spectralGood_orientation_variance
import Theorems.Thm_OAI_CriticalSK_goe_spectral_bad_probability
import Theorems.Thm_OAI_CriticalSK_naturalOrientationInputs
import Theorems.Thm_OAI_CriticalSK_orientation_normalized_overlap_bound

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
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

end

section

lemma rotatedCubePartition_continuous {n : ℕ} (lam : Fin n → ℝ) (a : ℝ) :
    Continuous (rotatedCubePartition lam a) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  exact (continuous_const.mul ((diagonalEnergy_continuous lam).comp
    (orthogonalIsometry_fixed_continuous (cubeVector x)))).rexp

lemma cube_pair_energy_continuous {n : ℕ} (lam : Fin n → ℝ) (x y : Spin n) :
    Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x)) +
        diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2)) := by
  have hx := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous (cubeVector x))
  have hy := (diagonalEnergy_continuous lam).comp (orthogonalIsometry_fixed_continuous (cubeVector y))
  exact ((hx.add hy).div_const 2).rexp

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

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma sphereTilted_integral (lam : ι → ℝ) (a r : ℝ) (F : unitSphere ι → ℝ) :
    (∫ u, F u ∂sphereTilted lam a r) =
      (∫ u : unitSphere ι, Real.exp (a/2*diagonalEnergy lam (r • u.val)) * F u
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) /
      (∫ u : unitSphere ι, Real.exp (a/2*diagonalEnergy lam (r • u.val))
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) := by
  rw [sphereTilted, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (by unfold diagonalEnergy; fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sphereWeight_integral_pos lam a r).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  ring

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.OverlapMoments
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
namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
lemma sphereInner_rotation (U : Matrix.orthogonalGroup ι ℝ) (x y : unitSphere ι) :
    inner ℝ (orthogonalSphere U x).val (orthogonalSphere U y).val = inner ℝ x.val y.val :=
  (orthogonalIsometry U).inner_map_map x.val y.val

omit [Nonempty ι] in
lemma spherePairEnergy_haar (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (p : unitSphere ι × unitSphere ι) :
    (∫ U, spherePairEnergy lam r (orthogonalSphere U p.1, orthogonalSphere U p.2)
      ∂orthogonalHaar ι) = pairMoment lam u v (inner ℝ p.1.val p.2.val) := by
  have hr : 0 ≤ r := hu ▸ norm_nonneg u
  have hnorm (x : unitSphere ι) : ‖r • x.val‖ = r := by
    rw [norm_smul,Real.norm_of_nonneg hr,mem_sphere_zero_iff_norm.mp x.property,mul_one]
  have hxy : inner ℝ (r • p.1.val) (r • p.2.val) = inner ℝ p.1.val p.2.val * r^2 := by
    rw [real_inner_smul_left,real_inner_smul_right]; ring
  rw [← pair_energy_orbit lam (hnorm p.1) (hnorm p.2) hu hv horth
    (sphere_inner_abs_le_one p.1 p.2) hxy]
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [spherePairEnergy,orthogonalSphere,sphereMap,map_smul]

lemma sphereOverlap_weighted_pair (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ q, g q*pairMoment lam u v q ∂sphereOverlapLaw ι) =
      ∫ p : unitSphere ι × unitSphere ι,
        g (inner ℝ p.1.val p.2.val)*spherePairEnergy lam r p ∂(sphereUniform.prod sphereUniform) := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι => inner ℝ p.1.val p.2.val) :=
    (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
  rw [sphereOverlapLaw,integral_map hc.measurable.aemeasurable
    (show AEStronglyMeasurable (fun q => g q * pairMoment lam u v q) _ from
      (hg.mul (pairMoment_continuous lam u v)).aestronglyMeasurable)]
  have hf : Continuous (fun p : unitSphere ι × unitSphere ι =>
      g (inner ℝ p.1.val p.2.val)*spherePairEnergy lam r p) :=
    (hg.comp hc).mul (spherePairEnergy_continuous lam r)
  rw [← spherePair_haar_average _ hf]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [sphereInner_rotation]
  rw [integral_const_mul,spherePairEnergy_haar lam hu hv horth]

omit [DecidableEq ι] in
lemma sphereTilted_uniform_integral (lam : ι → ℝ) (a r : ℝ) (F : unitSphere ι → ℝ) :
    (∫ u, F u ∂sphereTilted lam a r) =
      (∫ u, Real.exp (a/2*diagonalEnergy lam (r • u.val))*F u ∂sphereUniform) /
        spherePartition lam a r := by
  rw [sphereTilted_integral,sphereUniform_integral,spherePartition,sphereAverage,sphereAverage]
  have ha := ne_of_gt (sphereArea_pos (ι := ι))
  field_simp [ha]

omit [DecidableEq ι] in
lemma sphereTilted_pair_integral (lam : ι → ℝ) (r : ℝ)
    (F : unitSphere ι × unitSphere ι → ℝ) (hF : Continuous F) :
    (∫ p, F p ∂((sphereTilted lam 1 r).prod (sphereTilted lam 1 r))) =
      (∫ p, spherePairEnergy lam r p*F p ∂(sphereUniform.prod sphereUniform)) /
        spherePartition lam 1 r^2 := by
  have hi : Integrable F ((sphereTilted lam 1 r).prod (sphereTilted lam 1 r)) := by
    simpa only [integrableOn_univ] using hF.continuousOn.integrableOn_compact isCompact_univ
  have hi' : Integrable (fun p => spherePairEnergy lam r p*F p)
      (sphereUniform.prod sphereUniform) := by
    have hc : Continuous (fun p : unitSphere ι × unitSphere ι => spherePairEnergy lam r p * F p) :=
      (spherePairEnergy_continuous lam r).mul hF
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi,integral_prod _ hi']
  simp_rw [sphereTilted_uniform_integral]
  simp_rw [spherePairEnergy_factor,mul_assoc,integral_const_mul]
  simp_rw [← mul_div_assoc,integral_div]
  rw [div_div,← pow_two]

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coordinateReflection_apply (i j : ι) (x : EuclideanSpace ℝ ι) :
    coordinateReflection i x j = if j=i then -x j else x j := by
  classical
  simp only [coordinateReflection, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

lemma coordinateReflection_energy (lam : ι → ℝ) (i : ι) (x : EuclideanSpace ℝ ι) :
    diagonalEnergy lam (coordinateReflection i x) = diagonalEnergy lam x := by
  unfold diagonalEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateReflection_apply]
  split_ifs <;> ring

omit [DecidableEq ι] in
lemma sphereMap_measurableEmbedding (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurableEmbedding (sphereMap U) := by
  apply (sphereMap_continuous U).measurableEmbedding
  intro u w h
  apply Subtype.ext
  exact U.injective (congrArg Subtype.val h)

variable [Nonempty ι]

lemma sphereTilted_coordinate_cross (lam : ι → ℝ) (a r : ℝ) (i j : ι) (hij : i ≠ j) :
    (∫ u : unitSphere ι, ((r • u.val) i) * ((r • u.val) j) ∂sphereTilted lam a r) = 0 := by
  rw [sphereTilted_integral]
  suffices hn : (∫ u : unitSphere ι, Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0 by
    rw [hn, zero_div]
  let F := fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j)
  have he (u : unitSphere ι) : F (sphereMap (coordinateReflection i) u) = -F u := by
    dsimp [F, sphereMap]
    rw [← (coordinateReflection i).map_smul, coordinateReflection_energy]
    simp only [coordinateReflection_apply]
    simp only [ite_eq_left, ite_eq_right hij.symm]
    ring
  have hi := (sphereMap_preserving (coordinateReflection i)).integral_comp
    (sphereMap_measurableEmbedding _) F
  simp_rw [he, integral_neg] at hi
  change (∫ u, F u ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0
  linarith only [hi]

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereTilted_continuous_integrable (lam : ι → ℝ) (a r : ℝ) {f : unitSphere ι → ℝ}
    (hf : Continuous f) : Integrable f (sphereTilted lam a r) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

lemma sphereTilted_linear_square (lam : ι → ℝ) (a r : ℝ) (c : ι → ℝ) :
    (∫ u : unitSphere ι, (∑ i, c i * (r • u.val) i)^2 ∂sphereTilted lam a r) =
      ∑ i, c i^2 * (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) := by
  have hh (u : unitSphere ι) : (∑ i, c i*(r • u.val) i)^2 =
      ∑ i, ∑ j, c i*c j*((r • u.val) i*(r • u.val) j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hh]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single i]
  · simp only [pow_two]
  · intro j _ hji
    rw [sphereTilted_coordinate_cross lam a r i j hji.symm, mul_zero]
  · simp

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma sphereTilted_overlap_moment (lam : ι → ℝ) (a r : ℝ) :
    (∫ p : unitSphere ι × unitSphere ι,
      (inner ℝ (r • p.1.val) (r • p.2.val))^2
      ∂((sphereTilted lam a r).prod (sphereTilted lam a r))) =
      ∑ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r)^2 := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2) := by fun_prop
  have hi : Integrable (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2)
      ((sphereTilted lam a r).prod (sphereTilted lam a r)) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi]
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]
  simp_rw [sphereTilted_linear_square]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_mul_const,pow_two]

lemma sphereOverlap_weighted_tilted (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ q, g q*pairMoment lam u v q ∂sphereOverlapLaw ι) / spherePartition lam 1 r^2 =
      ∫ p : unitSphere ι × unitSphere ι, g (inner ℝ p.1.val p.2.val)
        ∂((sphereTilted lam 1 r).prod (sphereTilted lam 1 r)) := by
  rw [sphereOverlap_weighted_pair lam hu hv horth g hg]
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι => g (inner ℝ p.1.val p.2.val)) :=
    hg.comp ((continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd))
  rw [sphereTilted_pair_integral lam r _ hc]
  simp only [mul_comm]

lemma sphereOverlap_square_moment (lam : ι → ℝ) {u v : EuclideanSpace ℝ ι} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q, q^2*pairMoment lam u v q ∂sphereOverlapLaw ι) / spherePartition lam 1 r^2 =
      (∑ i, (∫ x : unitSphere ι, ((r • x.val) i)^2 ∂sphereTilted lam 1 r)^2) / r^4 := by
  rw [sphereOverlap_weighted_tilted lam hu hv horth (fun q => q^2) (by fun_prop),
    ← sphereTilted_overlap_moment]
  simp_rw [real_inner_smul_left,real_inner_smul_right,mul_pow,integral_const_mul]
  field_simp

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

lemma rotatedCubePair_continuous {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ) :
    Continuous (rotatedCubePair lam g) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact (cube_pair_energy_continuous lam x y).const_mul _

lemma sphereOverlap_density_weighted_moment (n : ℕ) (lam : Fin (n+4) → ℝ)
    {u v : EuclideanSpace ℝ (Fin (n+4))} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r) (horth : inner ℝ u v = 0) :
    (∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity (n+4) q) / spherePartition lam 1 r^2 =
      (∑ i, (∫ x : unitSphere (Fin (n+4)), ((r • x.val) i)^2 ∂sphereTilted lam 1 r)^2)/r^4 := by
  rw [← normalizedOverlapShape_integral (by omega : 4 ≤ n+4),← sphereOverlapLaw_density (n+1)]
  exact sphereOverlap_square_moment lam hr hu hv horth

end

lemma normalized_pair_event_bound {B Z S K : ℝ} (hB : 0 ≤ B) (hZ : 0 < Z)
    (hS : 0 < S) (hK : 0 < K) (hlarge : K ≤ B/Z^2) :
    1 ≤ 4*(Z/S-1)^2+4*(B/S^2)/K := by
  by_cases hz : S/2 ≤ Z
  · have hf : 1 ≤ 4*(B/S^2)/K := by
      have hb := (le_div_iff₀ (sq_pos_of_pos hZ)).mp hlarge
      have hsq : S^2 ≤ 4*Z^2 := by nlinarith
      apply (le_div_iff₀ hK).mpr
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (sq_pos_of_pos hS)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hK.le]
    linarith [sq_nonneg (Z/S-1)]
  · have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 4*(B/S^2)/K := by positivity
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

lemma rotatedCubePair_square_nonneg {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubePair lam (fun q => q^2) U := by
  unfold rotatedCubePair
  positivity

lemma rotatedCubeOverlap_probability {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {K : ℝ} (hK : 0 < K) :
    (orthogonalHaar (Fin n)).real {U | K ≤ rotatedCubeOverlap lam U} ≤
      4*(∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n))+
      4*((∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n))/spherePartition lam 1 (Real.sqrt n)^2)/K := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let S := spherePartition lam 1 (Real.sqrt n)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hV : Integrable (fun U => (rotatedCubePartition lam 1 U / S - 1)^2) (orthogonalHaar (Fin n)) := orthogonalHaar_integrable (((rotatedCubePartition_continuous lam 1).div_const S).sub continuous_const |>.pow 2)
  have hB := orthogonalHaar_integrable (rotatedCubePair_continuous lam (fun q => q^2))
  have hh := integral_dominates_event ((hV.const_mul 4).add (((hB.div_const (S^2)).const_mul 4).div_const K))
    (fun U => by dsimp; have := rotatedCubePair_square_nonneg lam U; positivity) (fun U hU => normalized_pair_event_bound
      (rotatedCubePair_square_nonneg lam U) (rotatedCubePartition_pos lam 1 U) hS hK hU)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hV.const_mul 4) (((hB.div_const (S^2)).const_mul 4).div_const K),
    integral_const_mul,integral_div,integral_const_mul,integral_div] at hh
  exact hh

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
-- module Solutions.OAIQW_CriticalSK.MinMax
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
-- module Solutions.OAIQW_CriticalSK.TriNoise
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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
-- module Solutions.OAIQW_CriticalSK.Resolvent
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
-- module Solutions.OAIQW_CriticalSK.GOESpectrum
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
-- module Solutions.OAIQW_CriticalSK.DisorderTransfer
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.instDecidablePredEdgeTouches
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

lemma gibbs_exp_shift {n : ℕ} {W : Disorder n} (E : Spin n → ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = E x+c) (x : Spin n) :
    gibbs W x = Real.exp (E x)/(∑ y, Real.exp (E y)) := by
  simp only [gibbs,partition,h,Real.exp_add,← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero _)]

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
-- module Solutions.OAIQW_CriticalSK.EdgeAsymptotics
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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

lemma edgeFixedCost_tendsto (h : ℝ) : Tendsto (edgeFixedCost h) atTop (𝓝 0) := by
  have hA := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/8)).const_mul
    (416*formConstant*(h+1))
  have hB := (tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop).const_div_atTop (16:ℝ)
  have ht : Tendsto (fun L => edgeFixedCost h L) atTop (𝓝 0) := by
    simpa only [edgeFixedCost,neg_div,mul_zero,zero_add,id_eq] using hA.add hB
  exact ht

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
-- module Solutions.OAIQW_CriticalSK.OrientationLimits
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


lemma cutoff_cubic_identity {x : ℝ} (hx : 0 < x) :
    x*(x^(-(7/24:ℝ)))^3 = x^(1/8:ℝ) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  conv_lhs => lhs; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]
  norm_num

lemma rpow_exp_small_tendsto (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hx := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/8)).comp hn
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (8*p) (1/24) (by norm_num)).comp hx
  apply hh.congr
  intro n
  change ((n+1:ℝ)^(1/8:ℝ))^(8*p)*_ = _
  rw [← Real.rpow_mul (by positivity)]
  congr 2
  ring

lemma edgeLength_sq_le_linear (n : ℕ) : (edgeLength n:ℝ)^2 ≤ 8*(n+1) := by
  have hd : (1:ℝ) ≤ edgeLength n := by exact_mod_cast edgeLength_pos n
  have hcube := (edgeLength_cube n).2
  have hh : (edgeLength n:ℝ)^2 ≤ (edgeLength n:ℝ)^3 := by nlinarith [sq_nonneg ((edgeLength n:ℝ)-1)]
  exact hh.trans hcube

lemma naturalPartitionBase_pos {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionBase L := by
  unfold naturalPartitionBase
  positivity

lemma naturalPartitionConstant_lower (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalPartitionBase L/(n+1) ≤ naturalPartitionConstant n L := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hd := edgeLength_cast_pos n
  have hh := div_le_div_of_nonneg_left hL.le (pow_pos hd 2) (edgeLength_sq_le_linear n)
  have ht := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 4))
    (Real.exp_pos (-6*(L*Real.sqrt L))).le
  unfold naturalPartitionBase naturalPartitionConstant naturalEdgeScale
  calc
    _ = L/(8*(n+1))/4*Real.exp (-6*(L*Real.sqrt L)) := by
      field_simp
      ring
    _ ≤ _ := ht

lemma naturalPartitionConstant_pos (n : ℕ) {L : ℝ} (hL : 0 < L) : 0 < naturalPartitionConstant n L :=
  (div_pos (naturalPartitionBase_pos hL) (by positivity)).trans_le (naturalPartitionConstant_lower n hL)

lemma naturalOrientationTail_bound (n : ℕ) {L : ℝ} (hL : 0 < L) :
    naturalOrientationTail n L ≤ 2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*
      Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ)) := by
  have hN : (0:ℝ) < n+1 := by positivity
  have hK := naturalPartitionConstant_pos n hL
  have hB := naturalPartitionBase_pos hL
  have he : -(n+1:ℝ)/24*overlapCentralCutoff (n+1)^3 = -(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ) := by
    have hi := cutoff_cubic_identity hN
    unfold overlapCentralCutoff
    push_cast
    linear_combination -(1/24:ℝ)*hi
  have hratio : 26*Real.exp 1*(n+1)/naturalPartitionConstant n L ≤
      (26*Real.exp 1/naturalPartitionBase L)*(n+1)^2 := by
    apply (div_le_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left (naturalPartitionConstant_lower n hL)
      (show 0 ≤ (26*Real.exp 1/naturalPartitionBase L)*(n+1:ℝ)^2 by positivity)
    apply le_trans _ hh
    apply le_of_eq
    field_simp
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 26*Real.exp 1*(n+1:ℝ)/naturalPartitionConstant n L) hratio 2
  have hfac : (n+2:ℝ) ≤ 2*(n+1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold naturalOrientationTail
  rw [he]
  have hh := mul_le_mul hfac (mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))).le)
    (by positivity) (by positivity : (0:ℝ) ≤ 2*(n+1))
  apply hh.trans_eq
  ring

lemma naturalOrientationTail_scaled_tendsto {L : ℝ} (hL : 0 < L) (p : ℝ) :
    Tendsto (fun n : ℕ => (n+1:ℝ)^p*naturalOrientationTail n L) atTop (𝓝 0) := by
  have ht := (rpow_exp_small_tendsto (p+5)).const_mul (2*(26*Real.exp 1/naturalPartitionBase L)^2)
  have hz : Tendsto (fun n : ℕ => (n+1:ℝ)^p*
      (2*(26*Real.exp 1/naturalPartitionBase L)^2*(n+1:ℝ)^5*Real.exp (-(1/24:ℝ)*(n+1:ℝ)^(1/8:ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.congr (fun n => by
      rw [Real.rpow_add (by positivity),show (5:ℝ) = (5:ℕ) by norm_num, Real.rpow_natCast]
      ring)
  apply squeeze_zero (fun n => by unfold naturalOrientationTail; positivity) (fun n =>
    mul_le_mul_of_nonneg_left (naturalOrientationTail_bound n hL) (Real.rpow_nonneg (by positivity) _)) hz

open Set MeasureTheory Filter

lemma orthogonal_equal_norm_pair (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ u v : EuclideanSpace ℝ (Fin (n+2)), ‖u‖ = r ∧ ‖v‖ = r ∧ inner ℝ u v = 0 := by
  let b := EuclideanSpace.basisFun (Fin (n+2)) ℝ
  refine ⟨r • b 0,r • b 1,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,b.norm_eq_one,mul_one]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,b.norm_eq_one,mul_one]
  · rw [real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
    norm_num

lemma edgeLength_rpow_upper (n : ℕ) : (edgeLength n:ℝ) ≤ 2*(n+1:ℝ)^(1/3:ℝ) := by
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (edgeLength n:ℝ)^3)
    (edgeLength_cube n).2 (by norm_num : (0:ℝ) ≤ 1/3)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (by positivity)] at hh
  have hc : (8:ℝ)^(1/3:ℝ) = 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [hc,← Real.rpow_natCast,← Real.rpow_mul (edgeLength_cast_pos n).le] at hh
  norm_num at hh
  exact hh

lemma naturalEdgeScale_sqrt (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (naturalEdgeScale n L) = Real.sqrt L/(edgeLength n) := by
  rw [naturalEdgeScale,Real.sqrt_div hL,Real.sqrt_sq (edgeLength_cast_pos n).le]

lemma naturalOverlapRate_nonneg (n : ℕ) (L : ℝ) : 0 ≤ naturalOverlapRate n L := by
  unfold naturalOverlapRate
  positivity

lemma naturalOverlapRate_scaled_bound (n : ℕ) {L : ℝ} (hL : 0 < L) :
    (n+1:ℝ)^(2/3:ℝ)*naturalOverlapRate n L ≤ naturalOverlapConstant L := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hr := Real.sqrt_pos.mpr hL
  have hd := edgeLength_cast_pos n
  have he : (n+1:ℝ)^(2/3:ℝ)*(n+1:ℝ)^(1/3:ℝ) = n+1 := by
    rw [← Real.rpow_add hn]
    norm_num
  have hh := mul_le_mul_of_nonneg_left (edgeLength_rpow_upper n)
    (show 0 ≤ (n+1:ℝ)^(2/3:ℝ) by positivity)
  have hb : (n+1:ℝ)^(2/3:ℝ)*(edgeLength n:ℝ) ≤ 2*(n+1) := by
    nlinarith [he]
  unfold naturalOverlapRate naturalOverlapConstant
  rw [naturalEdgeScale_sqrt n hL.le]
  have ht := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L) by positivity)
  calc
    _ = (16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L))*
        ((n+1:ℝ)^(2/3:ℝ)*(edgeLength n:ℝ)) := by field_simp
    _ ≤ (16*(16*Real.exp (6*(L*Real.sqrt L)))^2/((n+1:ℝ)*Real.sqrt L))*(2*(n+1)) := ht
    _ = _ := by field_simp; ring

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SmallBall
attribute [-instance] _root_.OAI.CriticalSK.instDecidablePredEdgeTouches
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

open Set MeasureTheory Filter

lemma spectralGood_orientation_overlap {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lam ∈ spectralGood (n+3) h (naturalEdgeScale (n+3) L),
      (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin (n+4))) /
        spherePartition lam 1 (Real.sqrt (n+4))^2 ≤
        (1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L := by
  have ho := (tendsto_add_atTop_nat 4).eventually (orientation_normalized_overlap_bound ε hε)
  filter_upwards [naturalOrientationInputs hh hL hcost, spectralGood_natural_sphere_bounds hh hL hcost,ho] with n hn hb hv
  intro lam hlam
  have hi := hn lam hlam
  obtain ⟨u,v,hu,hv',huv⟩ := orthogonal_equal_norm_pair (n+2) (Real.sqrt (n+4)) (Real.sqrt_nonneg _)
  have hh := hv lam u v _ _
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hu)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hv') huv hi.bounded hi.Kpos hi.partitionLower hi.scaleNonneg
    hi.topUpper hi.topLower hi.trace hi.traceUniform hi.cutoff hi.saddle
  have hsphere := sphereOverlap_density_weighted_moment n lam (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < n+4)) hu hv' huv
  have hroot : Real.sqrt (n+4:ℝ)^4 = (n+4:ℝ)^2 := by
    rw [show (4:ℕ) = 2*2 by omega,pow_mul,Real.sq_sqrt (by positivity)]
  rw [hroot] at hsphere
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
  rw [hsphere] at hh
  apply hh.trans
  have ht := add_le_add_right (mul_le_mul_of_nonneg_left (hb lam hlam).2
    (show 0 ≤ 1+ε by linarith)) (naturalOrientationTail (n+3) L)
  simpa only [naturalOrientationTail,Nat.cast_add,Nat.cast_ofNat,show (n:ℝ)+3+1=n+4 by ring,
    show (n:ℝ)+3+2=n+4+1 by ring, show n+3+1=n+4 by omega, add_comm] using ht

end

open Set MeasureTheory Filter

lemma goe_natural_spectral_bad {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) :
    ∀ᶠ n : ℕ in atTop, (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h (naturalEdgeScale n L))ᶜ) ≤ 32*Real.exp (-h^2) := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  filter_upwards [traceCost_natural_eventually hh hLp hcost,
    (naturalEdgeScale_tendsto L).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hc hs
  apply goe_spectral_bad_probability n hh (naturalEdgeScale_pos n hLp) (naturalEdgeScale_base n hL1)
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

lemma exists_spectral_failure_parameter {α : ℝ} (hα : 0 < α) :
    ∃ h : ℝ, 0 ≤ h ∧ 32*Real.exp (-h^2) < α := by
  have hh : Tendsto (fun h : ℝ => -h^2) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have ht : Tendsto (fun h : ℝ => 32*Real.exp (-h^2)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hh).const_mul 32
  exact ((eventually_ge_atTop 0).and (ht.eventually (gt_mem_nhds hα))).exists

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Covariance
attribute [-instance] _root_.OAI.CriticalSK.instDecidablePredEdgeTouches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK


open Set MeasureTheory

lemma gibbsOverlap_continuous (n : ℕ) : Continuous (gibbsOverlap (n := n)) := by
  unfold gibbsOverlap
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact ((gibbs_continuous x).mul (gibbs_continuous y)).mul continuous_const

lemma rotatedCubeOverlap_eq {n : ℕ} {W : Disorder n} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (c : ℝ)
    (h : ∀ x, hamiltonian W x = (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+c) :
    rotatedCubeOverlap lam U = gibbsOverlap W := by
  have hg := gibbs_exp_shift _ c h
  unfold rotatedCubeOverlap rotatedCubePair rotatedCubePartition gibbsOverlap
  rw [mul_pow,mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero (by positivity : (Fintype.card (Spin n):ℝ) ≠ 0)))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  rw [hg,hg,show (diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
    diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2 =
    (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
      (1/2:ℝ)*diagonalEnergy lam (orthogonalIsometry U (cubeVector y)) by ring,Real.exp_add]
  ring


open Set MeasureTheory Filter

lemma haar_gibbsOverlap_bound {n : ℕ} (hn : 0 < n)
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) {K : ℝ} (hK : 0 < K) :
    (orthogonalHaar (Fin n)).real {U | K ≤ gibbsOverlap (gaussianDisorder (haarConjugate U A))} ≤
      4*(∫ U, (rotatedCubePartition (matrixOrderedEigenvalues A) 1 U /
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n))+
        4*((∫ U, rotatedCubePair (matrixOrderedEigenvalues A) (fun q => q^2) U ∂orthogonalHaar (Fin n))/
          spherePartition (matrixOrderedEigenvalues A) 1 (Real.sqrt n)^2)/K := by
  obtain ⟨V,hV⟩ := gaussian_matrix_energy_eigenbasis A hA
  let lam := matrixOrderedEigenvalues A
  let R := matrixOfIsometry V
  have he (U : Matrix.orthogonalGroup (Fin n) ℝ) : gibbsOverlap (gaussianDisorder (haarConjugate U A)) =
      rotatedCubeOverlap lam (R*U) := by
    symm
    apply rotatedCubeOverlap_eq lam (R*U) (-(1/2:ℝ)*∑ j, haarConjugate U A j j)
    intro x
    simpa only [gaussianDisorder,lam,R,sub_eq_add_neg,neg_mul] using haarConjugate_hamiltonian A hA V hV U x
  simp_rw [he]
  change ((orthogonalHaar (Fin n)) ((fun U => R*U) ⁻¹' {U | K ≤ rotatedCubeOverlap lam U})).toReal ≤ _
  rw [measure_preimage_mul]
  exact rotatedCubeOverlap_probability hn lam hK

lemma natural_gibbsOverlap_probability {h L : ℝ} (hh : 0 ≤ h) (hL : 262144 ≤ L)
    (hcost : edgeFixedCost h L < 1/100) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℝ, 0 < K → (disorderLaw (n+4)).real
      {W | K ≤ gibbsOverlap W} ≤
      32*Real.exp (-h^2)+4*(ε+naturalOrientationTail (n+3) L)+
        4*((1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L)/K := by
  have hspectral := (tendsto_add_atTop_nat 3).eventually (goe_natural_spectral_bad hh hL hcost)
  filter_upwards [hspectral,spectralGood_orientation_variance hh hL hcost hε,
    spectralGood_orientation_overlap hh hL hcost hε] with n hn hvar hover
  intro K hK
  have hE : MeasurableSet {W : Disorder (n+4) | K ≤ gibbsOverlap W} :=
    (isClosed_le continuous_const (gibbsOverlap_continuous _)).measurableSet
  rw [disorder_goe_event (n+3) hE]
  let G : Set (GaussianMatrix (Fin (n+4))) := matrixOrderedEigenvalues ⁻¹' spectralGood (n+3) h (naturalEdgeScale (n+3) L)
  have hG : MeasurableSet G := (spectralGood_measurable _ _ _).preimage (matrixOrderedEigenvalues_measurable _)
  have he := goe_event_from_orbit_bound (goeScale (n+3))
    (hE.preimage (gaussianDisorder_measurable _)) hG
    (show 0 ≤ 4*(ε+naturalOrientationTail (n+3) L)+
        4*((1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L)/K from by
      have := naturalOverlapRate_nonneg (n+3) L
      unfold naturalOrientationTail
      positivity)
    (fun A hAG hA => by
      have hbnd := haar_gibbsOverlap_bound (by omega : 0 < n+4) A hA hK
      apply hbnd.trans
      have hV := hvar (matrixOrderedEigenvalues A) hAG
      have hO := hover (matrixOrderedEigenvalues A) hAG
      norm_num only [Nat.cast_add,Nat.cast_ofNat] at hbnd ⊢
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hV (by norm_num)
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hO (by norm_num)) hK.le)
  have hnn : (goeLaw (Fin (n+4)) (goeScale (n+3))).real Gᶜ ≤ 32*Real.exp (-h^2) := hn
  linarith

lemma naturalOverlapConstant_pos {L : ℝ} (hL : 0 < L) : 0 < naturalOverlapConstant L := by
  unfold naturalOverlapConstant
  positivity

lemma natural_GibbsOverlap_tight {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | C/(n+4:ℝ)^(2/3:ℝ) ≤ gibbsOverlap W} < α := by
  obtain ⟨h,hh,hfail⟩ := exists_spectral_failure_parameter (show 0 < α/4 by positivity)
  obtain ⟨L,hL,hcost⟩ := ((eventually_ge_atTop (262144:ℝ)).and
    ((edgeFixedCost_tendsto h).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)))).exists
  have hLp : 0 < L := by linarith
  let ε := α/32
  have hε : 0 < ε := by dsimp [ε]; positivity
  let D := (1+ε)*naturalOverlapConstant L+1
  have hD : 0 < D := by dsimp [D]; have := naturalOverlapConstant_pos hLp; positivity
  let C := 32*D/α
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have ht : Tendsto (fun n : ℕ => naturalOrientationTail (n+3) L) atTop (𝓝 0) := by
    have hs := (naturalOrientationTail_scaled_tendsto hLp 0).comp (tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def,Real.rpow_zero,one_mul] using hs
  have hst : Tendsto (fun n : ℕ => (n+4:ℝ)^(2/3:ℝ)*naturalOrientationTail (n+3) L)
      atTop (𝓝 0) := by
    have hs := (naturalOrientationTail_scaled_tendsto hLp (2/3)).comp (tendsto_add_atTop_nat 3)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num,add_assoc] using hs
  filter_upwards [natural_gibbsOverlap_probability hh hL hcost hε,
    ht.eventually (gt_mem_nhds hε),hst.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn htail hscale
  let S := (n+4:ℝ)^(2/3:ℝ)
  have hS : 0 < S := by dsimp [S]; positivity
  have hp := hn (C/S) (by positivity)
  apply lt_of_le_of_lt hp
  have hR := naturalOverlapRate_scaled_bound (n+3) hLp
  norm_num only [Nat.cast_add,Nat.cast_ofNat] at hR
  rw [show (n:ℝ)+3+1=n+4 by ring] at hR
  have hnum : S*((1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L) ≤ D := by
    dsimp only [D]
    have hg := mul_le_mul_of_nonneg_left hR (show 0 ≤ 1+ε by positivity)
    change S*naturalOrientationTail (n+3) L < 1 at hscale
    nlinarith
  have hfrac : 4*((1+ε)*naturalOverlapRate (n+3) L+naturalOrientationTail (n+3) L)/(C/S) ≤ α/8 := by
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    have he : α/8*C = 4*D := by dsimp [C]; field_simp; ring
    rw [he]
    nlinarith
  dsimp only [ε] at htail ⊢
  linarith

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Rayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

open Set Filter MeasureTheory

lemma cavity_overlap_tail_zero_oai : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro a ha
    obtain ⟨C,_hC,hp⟩ := natural_GibbsOverlap_tight ha
    have ht : Tendsto (fun n : ℕ => (n+4:ℝ)^(1/15:ℝ)) atTop atTop := by
      have hh := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/15)).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 4))
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh
    filter_upwards [hp,tendsto_atTop.mp ht C] with n hn hCn
    refine lt_of_le_of_lt (measureReal_mono ?_) hn
    intro W hW
    change C/(n+4:ℝ)^(2/3:ℝ) ≤ gibbsOverlap W
    change (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W at hW
    apply le_trans _ hW
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+4:ℝ)^(2/3:ℝ))).mpr
    rw [← Real.rpow_add (by positivity : (0:ℝ)<n+4)]
    norm_num
    exact hCn

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.cavity_overlap_tail_zero_oai := @OAI.CriticalSK.cavity_overlap_tail_zero_oai
