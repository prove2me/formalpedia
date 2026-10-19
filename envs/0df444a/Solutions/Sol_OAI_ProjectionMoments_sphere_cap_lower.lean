-- Prove2me | solution 1 for OAI.ProjectionMoments.sphere_cap_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:55:29.096742+00:00
-- url     : https://prove2.me/submissions/96137a92-7052-458c-980b-ed3964d39b27

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Caps.lean:L184-L209
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.sphere_cap_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
import Theorems.Thm_OAI_ProjectionMoments_rotation_transitive
import Theorems.Thm_OAI_ProjectionMoments_sphere_packing_annulus

-- ---- from OAI.Probability.GaussianRegression.Sphere ----
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

end SphereBounds

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_packing_bound (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ)*r^(Module.finrank ℝ E-1) ≤ (8 : ℝ)^Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have hi : 0 ≤ 1-r/2 := by linarith
  have ho : 0 ≤ 1+r/2 := by positivity
  have hio : 1-r/2 ≤ 1+r/2 := by linarith
  have h := sphere_packing_annulus s hr hr1 hs hsep
  have hdiff : (1+r/2)^d - (1-r/2)^d ≤ r*d*(1+r/2)^(d-1) := by
    have hh := abs_pow_sub_pow_le (a := (1+r/2)) (b := (1-r/2)) (n := d)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hi hio d)),
      abs_of_nonneg ho, abs_of_nonneg hi, max_eq_left hio,
      show (1+r/2)-(1-r/2) = r by ring, abs_of_pos hr] at hh
    exact hh
  have hpow : (1+r/2)^(d-1) ≤ (2 : ℝ)^d := by
    exact (pow_le_pow_left₀ ho (by linarith : 1+r/2 ≤ 2) _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1))
  have hd2 : (d : ℝ) ≤ (2 : ℝ)^d := by
    have hn : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        rw [Nat.cast_succ, pow_succ]
        linarith
    exact hn d
  have hupper : r*d*(1+r/2)^(d-1) ≤ r*(4 : ℝ)^d := by
    calc
      _ ≤ r*2^d*2^d := mul_le_mul (mul_le_mul_of_nonneg_left hd2 hr.le) hpow (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num
  have hall := h.trans (hdiff.trans hupper)
  have htwo : 0 < (2 : ℝ)^d := by positivity
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ htwo] at hall
  have hp : r^d = r^(d-1)*r := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hp, ← mul_assoc, mul_assoc r, ← mul_pow] at hall
  norm_num only at hall
  nlinarith

lemma sphere_cap_mass_center [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1)
    (r : ℝ) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) =
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' r) := by
  obtain ⟨O,hO⟩ := rotation_transitive
    (show Orthonormal ℝ (fun _ : Fin 1 => c) by simpa using hc)
    (show Orthonormal ℝ (fun _ : Fin 1 => c') by simpa using hc')
  let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv O
  have he : e c = c' := hO 0
  have hh := (NoiselessRegression.ambientSphereLaw_isometry e).map_eq
  have hpre : e ⁻¹' Metric.closedBall c' r = Metric.closedBall c r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, ← he, e.dist_map]
  have h := congrArg (fun μ : Measure E => μ (Metric.closedBall c' r)) hh
  rw [Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet, hpre] at h
  exact h

lemma sphere_finite_net {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ = 1) ∧
      (∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → r < dist c c') ∧
      ∀ x : E, ‖x‖ = 1 → ∃ c ∈ s, dist x c ≤ r := by
  classical
  let N := ⌈((1+r/2)/(r/2))^Module.finrank ℝ E⌉₊
  obtain ⟨s,hs,hsep,hnet⟩ := NoiselessRegression.exists_net_of_finite_packing_bound
    {x : E | ‖x‖ = 1} hr.le N (by
      intro s hs hsep
      have hh := NoiselessRegression.card_le_volume_ratio s hr (by norm_num : (0:ℝ) ≤ 1)
        (fun c hc => (hs c hc).le) (fun c hc c' hc' hne => (hsep c hc c' hc' hne).le)
      exact_mod_cast hh.trans (Nat.le_ceil _))
  exact ⟨s,hs,hsep,hnet⟩

lemma sphere_cap_lower_one [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  classical
  let μ : Measure E := NoiselessRegression.ambientSphereLaw
  obtain ⟨s,hs,hsep,hnet⟩ := sphere_finite_net (E := E) hr
  have hcard := sphere_packing_bound s hr hr1
    (Module.finrank_pos (R := ℝ) (M := E)) hs
    (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
  have hcover : μ (⋃ x ∈ s, Metric.closedBall x r) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [NoiselessRegression.ambientSphereLaw_ae_norm (E := E)] with x hx
    apply propext
    change (x ∈ ⋃ y ∈ s, Metric.closedBall y r) ↔ x ∈ Set.univ
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y,hy,hxy⟩ := hnet x hx
    exact Set.mem_iUnion₂.mpr ⟨y,hy,hxy⟩
  have hone : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞)*μ (Metric.closedBall c r) := by
    calc
      _ = μ (⋃ x ∈ s, Metric.closedBall x r) := hcover.symm
      _ ≤ ∑ x ∈ s, μ (Metric.closedBall x r) := measure_biUnion_finset_le _ _
      _ = _ := by
        have hm : ∀ x ∈ s, μ (Metric.closedBall x r) = μ (Metric.closedBall c r) :=
          fun x hx => sphere_cap_mass_center (hs x hx) hc r
        simp_rw [Finset.sum_congr rfl hm]
        simp
  calc
    _ = ENNReal.ofReal (r^(Module.finrank ℝ E-1))*1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (r^(Module.finrank ℝ E-1))*
        ((s.card : ℝ≥0∞)*μ (Metric.closedBall c r)) := mul_le_mul' le_rfl hone
    _ = ENNReal.ofReal ((s.card:ℝ)*r^(Module.finrank ℝ E-1))*
        μ (Metric.closedBall c r) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hcard) le_rfl

lemma sphere_cap_lower [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  by_cases hr1 : r ≤ 1
  · exact (sphere_cap_lower_one hc hr hr1).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8)
        (by norm_num : (8:ℝ) ≤ 16) _)) le_rfl)
  · have h1 := sphere_cap_lower_one hc (by norm_num : (0:ℝ) < 1) le_rfl
    simp only [one_pow, ENNReal.ofReal_one] at h1
    have h2 : r^(Module.finrank ℝ E-1) ≤ (2:ℝ)^Module.finrank ℝ E :=
      (pow_le_pow_left₀ hr.le hr2 _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    calc
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*1 := by
        simpa using ENNReal.ofReal_le_ofReal h2
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c 1)) := mul_le_mul' le_rfl h1
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)) := by
          gcongr
          exact le_of_not_ge hr1
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]; norm_num

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.sphere_cap_lower := @_root_.OAI.ProjectionMoments.sphere_cap_lower
