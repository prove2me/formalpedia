-- Prove2me | solution 1 for OAI.SubsphereCurrent.Slice.ballCap_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:00:03.511289+00:00
-- url     : https://prove2.me/submissions/8204cb44-52eb-4cf4-876b-b7c6402d4044

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Integration.lean:L624-L685
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Slice.ballCap_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Theorems.Thm_OAI_SubsphereCurrent_Polar_measurable_radial

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma introducing_radius :
    MeasurePreserving
      (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.val • z.1.val)
      ((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)))
      volume := by
  have h₁ := MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    ((volume : Measure E).measurePreserving_homeomorphUnitSphereProd)
  have h₂ := measurePreserving_subtype_coe (μa := (volume : Measure E))
    (measurableSet_singleton (0 : E)).compl
  rw [Measure.restrict_eq_self_of_ae_mem] at h₂
  · exact h₂.comp h₁
  · exact ae_iff.mpr (by simp)

omit [Nontrivial E] in
lemma orthogonal_sum_volume (H : Submodule ℝ E) :
    MeasurePreserving (fun z : H × Hᗮ => (z.1 : E)+(z.2 : E))
      ((volume : Measure H).prod (volume : Measure Hᗮ)) volume := by
  exact H.orthogonalDecomposition.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp H Hᗮ)

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma orthogonal_radius_norm (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (s : Metric.sphere (0 : K) 1) (r : ℝ) :
    ‖x+r • (s.val : E)‖^2 = ‖x‖^2+r^2 := by
  have ho : ⟪x,(s.val : E)⟫ = 0 := Submodule.inner_left_of_mem_orthogonal s.val.property hx
  have hs : ‖(s.val : E)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,hs,mul_one,
    Real.norm_eq_abs,sq_abs]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_eq_radiusNorm (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (s : Metric.sphere (0 : K) 1) (r : ℝ) : ‖x+r • (s.val : E)‖ = radiusNorm x r := by
  have h := orthogonal_radius_norm K hx s r
  have hr : 0 ≤ radiusNorm x r := Real.sqrt_nonneg _
  nlinarith [radiusNorm_sq x r, norm_nonneg (x+r • (s.val : E))]

omit [MeasurableSpace E] [BorelSpace E] in
lemma radial_on_slice (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ) {r : ℝ} (hr : 0 < r)
    (s : Metric.sphere (0 : K) 1) :
    Polar.radial g (x+r • (s.val : E)) = g ((scaledTest K hx r hr).point s) := by
  have hp := radiusNorm_pos x hr
  have hn := norm_eq_radiusNorm K hx s r
  have hne : x+r • (s.val : E) ≠ 0 := by
    intro he
    rw [he,norm_zero] at hn
    linarith
  rw [Polar.radial,dite_eq_right hne]
  congr 1
  apply Subtype.ext
  simp only [Polar.unitDirection,NormedSpace.normalize,hn,Test.point,scaledTest]
  rw [smul_add,smul_smul,div_eq_mul_inv,mul_comm r]

lemma radial_slice_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} {k b : ℕ} {C : ℝ≥0∞}
    (hc : Controlled g k b C) (K : Submodule ℝ E) (hK : Module.finrank ℝ K = k)
    {x : E} (hx : x ∈ Kᗮ) {r : ℝ} (hr : 0 < r) (hsmall : radiusNorm x r ≤ 1) :
    (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
      ∂Affine.sphereLaw K) ≤ C * (ENNReal.ofReal (r^b))⁻¹ := by
  let A := scaledTest K hx r hr
  have ha := hc (hK ▸ A)
  have hav : ENNReal.ofReal ((r/radiusNorm x r)^b) *
      (∫⁻ s : Metric.sphere (0 : K) 1, g (A.point s) ∂Affine.sphereLaw K) ≤ C := by
    subst k
    exact ha
  have hrr : r ≤ r/radiusNorm x r := by
    apply (le_div_iff₀ (radiusNorm_pos x hr)).2
    nlinarith
  have hmul : ENNReal.ofReal (r^b) *
      (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
        ∂Affine.sphereLaw K) ≤ C := by
    simp_rw [radial_on_slice g K hx hr]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hr.le hrr b)) le_rfl).trans hav
  have h0 : ENNReal.ofReal (r^b) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (r^b) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ = (ENNReal.ofReal (r^b))⁻¹ * (ENNReal.ofReal (r^b) *
        ∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E)) ∂Affine.sphereLaw K) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ht,one_mul]
    _ ≤ (ENNReal.ofReal (r^b))⁻¹ * C := mul_le_mul' le_rfl hmul
    _ = _ := mul_comm _ _

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

lemma radius_inverse_density (k b : ℕ) (hb : b+1 ≤ k) :
    (Measure.volumeIoiPow (k-1)).withDensity
      (fun r : Ioi (0 : ℝ) => (ENNReal.ofReal (r.val^b))⁻¹) =
        Measure.volumeIoiPow (k-b-1) := by
  rw [Measure.volumeIoiPow,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  ext r
  have hr : 0 < r.val := r.property
  change ENNReal.ofReal (r.val^(k-1)) * (ENNReal.ofReal (r.val^b))⁻¹ =
    ENNReal.ofReal (r.val^(k-b-1))
  have hn : k-1 = (k-b-1)+b := by omega
  rw [hn,pow_add,ENNReal.ofReal_mul (by positivity),mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,mul_one]

lemma radius_inverse_integral (k b : ℕ) (hb : b+1 ≤ k) {t : ℝ} (ht : 0 < t) :
    (∫⁻ r in Iio (⟨t,ht⟩ : Ioi (0 : ℝ)), (ENNReal.ofReal (r.val^b))⁻¹
      ∂Measure.volumeIoiPow (k-1)) = ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) := by
  rw [← withDensity_apply _ measurableSet_Iio,radius_inverse_density k b hb,
    Measure.volumeIoiPow_apply_Iio]
  have hn : k-b-1+1 = k-b := by omega
  rw [hn]
  congr 2
  exact_mod_cast hn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma sphere_integral_unnormalize (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) :
    (∫⁻ s, g s ∂(volume : Measure E).toSphere) =
      ((volume : Measure E).toSphere univ) * (∫⁻ s, g s ∂Affine.sphereLaw E) := by
  have h0 : (volume : Measure E).toSphere univ ≠ 0 := by
    intro h
    exact Measure.toSphere_ne_zero volume (Measure.measure_univ_eq_zero.mp h)
  have ht : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  rw [Affine.sphereLaw,lintegral_smul_measure,smul_eq_mul,← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht,one_mul]

omit [Nontrivial E] in
lemma measurable_capFunction {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : Measurable g) (z : E) (t : ℝ) : Measurable (capFunction g z t) :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) hg measurable_const

omit [Nontrivial E] in
lemma measurable_ballCap {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : Measurable g) (z : E) (t : ℝ) : Measurable (ballCap g z t) :=
  (Polar.measurable_radial (measurable_capFunction hg z t)).indicator Metric.isOpen_ball.measurableSet

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma ballCap_le (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ) (x : E) :
    ballCap g z t x ≤ Polar.radial g x := by
  classical
  apply (Set.indicator_le_self _ _ _).trans
  by_cases hx : x = 0
  · simp [Polar.radial,hx]
  · rw [Polar.radial,dite_eq_right hx,Polar.radial,dite_eq_right hx]
    unfold capFunction
    split_ifs <;> simp

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma ballCap_support (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (K : Submodule ℝ E) {z x : E} (hz : z ∈ Kᗮ) (hx : x ∈ Kᗮ)
    {r t : ℝ} (hr : 0 < r) (s : Metric.sphere (0 : K) 1)
    (hnz : ballCap g z t (x+r • (s.val : E)) ≠ 0) :
    ‖x‖ < 1 ∧ r < t ∧ radiusNorm x r < 1 := by
  classical
  have hn := norm_eq_radiusNorm K hx s r
  have hp := radiusNorm_pos x hr
  have hne : x+r • (s.val : E) ≠ 0 := by
    intro hh
    rw [hh,norm_zero] at hn
    linarith
  have hball : x+r • (s.val : E) ∈ Metric.ball (0 : E) 1 := by
    by_contra hh
    exact hnz (Set.indicator_of_notMem hh _)
  have hb : radiusNorm x r < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right,hn] using hball
  have hcap : dist (Polar.unitDirection (x+r • (s.val : E)) hne).val z ≤ t := by
    by_contra hh
    apply hnz
    rw [ballCap,Set.indicator_of_mem hball,Polar.radial,dite_eq_right hne,capFunction,
      ite_eq_right hh]
  have hx' : ‖x‖ < 1 := by
    have hh := radiusNorm_sq x r
    nlinarith [norm_nonneg x,sq_nonneg r]
  have hproj : K.orthogonalProjectionOnto
      ((Polar.unitDirection (x+r • (s.val : E)) hne).val-z) =
        ((radiusNorm x r)⁻¹*r) • s.val := by
    simp only [Polar.unitDirection,NormedSpace.normalize,hn,map_sub,map_smul,map_add,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,zero_add,sub_zero,smul_smul]
  have hl := K.norm_orthogonalProjectionOnto_apply_le
    ((Polar.unitDirection (x+r • (s.val : E)) hne).val-z)
  rw [hproj,norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (inv_pos.mpr hp) hr),
    mem_sphere_zero_iff_norm.mp s.property,mul_one] at hl
  rw [dist_eq_norm] at hcap
  have hrt : r < t := by
    have hr' : r < (radiusNorm x r)⁻¹*r := by
      have : 1 < (radiusNorm x r)⁻¹ := (one_lt_inv₀ hp).2 hb
      nlinarith
    exact hr'.trans_le (hl.trans hcap)
  exact ⟨hx',hrt,hb⟩

omit [Nontrivial E] in
lemma angular_ballCap_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} {k b : ℕ} {C : ℝ≥0∞}
    (hc : Controlled g k b C) (K : Submodule ℝ E) [Nontrivial K]
    (hK : Module.finrank ℝ K = k) {z x : E} (hz : z ∈ Kᗮ) (hx : x ∈ Kᗮ)
    {r t : ℝ} (hr : 0 < r) :
    (∫⁻ s : Metric.sphere (0 : K) 1, ballCap g z t (x+r • (s.val : E))
      ∂(volume : Measure K).toSphere) ≤
        (if ‖x‖ < 1 ∧ r < t then
          ((volume : Measure K).toSphere univ) * C * (ENNReal.ofReal (r^b))⁻¹ else 0) := by
  classical
  by_cases hh : ‖x‖ < 1 ∧ r < t
  · rw [ite_eq_left hh]
    by_cases hs : radiusNorm x r < 1
    · calc
        _ ≤ ∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
            ∂(volume : Measure K).toSphere := lintegral_mono fun s => ballCap_le _ _ _ _
        _ = (volume : Measure K).toSphere univ *
            (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
              ∂Affine.sphereLaw K) := sphere_integral_unnormalize _
        _ ≤ (volume : Measure K).toSphere univ * (C * (ENNReal.ofReal (r^b))⁻¹) :=
          mul_le_mul' le_rfl (radial_slice_bound hc K hK hx hr hs.le)
        _ = _ := (mul_assoc _ _ _).symm
    · have he (s : Metric.sphere (0 : K) 1) : ballCap g z t (x+r • (s.val : E)) = 0 := by
        by_contra hnz
        exact hs (ballCap_support g K hz hx hr s hnz).2.2
      simp only [he,lintegral_zero,zero_le]
  · rw [ite_eq_right hh]
    have he (s : Metric.sphere (0 : K) 1) : ballCap g z t (x+r • (s.val : E)) = 0 := by
      by_contra hnz
      have hp := ballCap_support g K hz hx hr s hnz
      exact hh ⟨hp.1,hp.2.1⟩
    simp only [he,lintegral_zero,le_refl]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma ballCap_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ y : E, ballCap g z t y ∂volume) ≤
      ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) *
          (volume : Measure Kᗮ) (Metric.ball 0 1) := by
  classical
  have hcb := measurable_ballCap hg z t
  have hf : Measurable (fun w : K × Kᗮ => ballCap g z t ((w.1 : E)+(w.2 : E))) :=
    hcb.comp ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd))
  rw [← (Polar.orthogonal_sum_volume K).lintegral_comp hcb,
    lintegral_prod_symm _ hf.aemeasurable]
  have hi (x : Kᗮ) :
      (∫⁻ y : K, ballCap g z t ((y : E)+(x : E)) ∂volume) ≤
      (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) := by
    have hym : Measurable (fun y : K => ballCap g z t ((y : E)+(x : E))) :=
      hcb.comp (measurable_subtype_coe.add measurable_const)
    have hpm : Measurable (fun w : Metric.sphere (0 : K) 1 × Ioi (0 : ℝ) =>
        ballCap g z t ((w.2.val • w.1.val : K)+(x : E))) := by
      apply hcb.comp
      fun_prop
    rw [← (Polar.introducing_radius (E := K)).lintegral_comp hym,
      lintegral_prod_symm _ hpm.aemeasurable]
    calc
      _ ≤ ∫⁻ r : Ioi (0 : ℝ), (if ‖(x : E)‖ < 1 ∧ r.val < t then
          (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹ else 0)
          ∂Measure.volumeIoiPow (k-1) := by
        rw [hK]
        apply lintegral_mono
        intro r
        have hh := angular_ballCap_bound hc K hK hz x.property r.property (t := t)
        simpa only [Submodule.coe_smul,add_comm (x : E)] using hh
      _ = (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
          ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) := by
        by_cases hx : ‖x‖ < 1
        · simp only [Submodule.norm_coe,hx,true_and,ite_true]
          have he : (fun r : Ioi (0 : ℝ) => if r.val < t then
              (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹ else 0) =
              (Iio (⟨t,ht⟩ : Ioi (0 : ℝ))).indicator
                (fun r => (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹) := by
            ext r
            simp only [Set.indicator_apply,Set.mem_Iio]
            rfl
          rw [he,lintegral_indicator measurableSet_Iio,lintegral_const_mul _ (by fun_prop),
            Polar.radius_inverse_integral k b hb ht]
        · simp only [Submodule.norm_coe,hx,false_and,ite_false,lintegral_zero]
  calc
    _ ≤ ∫⁻ x : Kᗮ, (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) ∂volume := lintegral_mono hi
    _ = _ := by
      have he : (fun x : Kᗮ => if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
          ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) =
          (Metric.ball (0 : Kᗮ) 1).indicator (fun _ => ((volume : Measure K).toSphere univ) * C *
            ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ))) := by
        ext x
        simp only [Set.indicator_apply,Metric.mem_ball,dist_zero_right]
      rw [he,lintegral_indicator_const Metric.isOpen_ball.measurableSet]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Slice
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Slice.ballCap_integral := @_root_.OAI.SubsphereCurrent.Slice.ballCap_integral
