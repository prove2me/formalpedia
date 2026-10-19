-- Prove2me | solution 1 for OAI.SubsphereCurrent.Slice.controlled_cap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:02:30.915593+00:00
-- url     : https://prove2.me/submissions/f8050d3d-2906-4a30-a588-20e03eade1fb

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/Integration.lean:L710-L743
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Slice.controlled_cap_bound. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereCurrent_Slice_ballCap_integral

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma lintegral_polar (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume : Measure E)) =
    ∫⁻ s : Metric.sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), f (r.val • s.val)
      ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) ∂(volume : Measure E).toSphere := by
  rw [← introducing_radius.lintegral_comp hf]
  exact lintegral_prod _ (hf.comp introducing_radius.measurable).aemeasurable

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma radial_smul (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (s : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) : radial g (r • s.val) = g s := by
  have hs : s.val ≠ 0 := by
    intro hs
    have hn := mem_sphere_zero_iff_norm.mp s.property
    rw [hs,norm_zero] at hn
    norm_num at hn
  rw [radial,dite_eq_right (smul_ne_zero hr.ne' hs)]
  congr 1
  apply Subtype.ext
  exact (NormedSpace.normalize_smul_of_pos hr _).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp s.property))

lemma radial_ball_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in Metric.ball (0 : E) 1, radial g x ∂volume) =
      (volume (Metric.ball (0 : E) 1)) * ∫⁻ s, g s ∂Affine.sphereLaw E := by
  classical
  let d := Module.finrank ℝ E
  have hd : 0 < d := Module.finrank_pos
  have hm : Measurable ((Metric.ball (0 : E) 1).indicator (radial g)) :=
    (measurable_radial hg).indicator Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,lintegral_polar _ hm]
  have he (s : Metric.sphere (0 : E) 1) :
      (fun r : Ioi (0 : ℝ) => (Metric.ball (0 : E) 1).indicator (radial g) (r.val • s.val)) =
        (Iio (⟨1,by norm_num⟩ : Ioi (0 : ℝ))).indicator (fun _ => g s) := by
    ext r
    have hn : ‖r.val • s.val‖ = r.val := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
        mem_sphere_zero_iff_norm.mp s.property,mul_one]
    simp only [Set.indicator_apply,Metric.mem_ball,dist_zero_right,hn,Set.mem_Iio,
      radial_smul g s r.property]
    rfl
  simp_rw [he,lintegral_indicator_const measurableSet_Iio,
    Measure.volumeIoiPow_apply_Iio]
  have hed : Module.finrank ℝ E - 1 + 1 = d := Nat.sub_add_cancel hd
  simp only [hed, one_pow]
  have hrd : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hed
  rw [hrd]
  rw [lintegral_mul_const]
  rw [Affine.sphereLaw,lintegral_smul_measure,Measure.toSphere_apply_univ]
  have hv0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hd : (0 : ℝ) < d),
    ENNReal.ofReal_natCast, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    _ = (d : ℝ≥0∞)⁻¹ * ∫⁻ s, g s ∂(volume : Measure E).toSphere := mul_comm _ _
    _ = (volume (Metric.ball (0 : E) 1) * ((d : ℝ≥0∞)⁻¹ * (volume (Metric.ball (0 : E) 1))⁻¹)) *
        ∫⁻ s, g s ∂(volume : Measure E).toSphere := by
      congr 1
      rw [mul_left_comm, ENNReal.mul_inv_cancel hv0 hvt, mul_one]
    _ = _ := by rw [mul_assoc]
  all_goals exact hg

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma orthogonal_volume_ratio (K : Submodule ℝ E) :
    (volume : Measure K) (Metric.ball 0 1) *
      (volume : Measure Kᗮ) (Metric.ball 0 1) ≤
        (2 : ℝ≥0∞)^Module.finrank ℝ E * (volume : Measure E) (Metric.ball 0 1) := by
  have hp := orthogonal_sum_volume K
  have hsub : (Metric.ball (0 : K) (1/2)) ×ˢ (Metric.ball (0 : Kᗮ) (1/2)) ⊆
      (fun z : K × Kᗮ => (z.1 : E)+(z.2 : E)) ⁻¹' Metric.ball 0 1 := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    change dist ((x : E)+(y : E)) 0 < 1
    simp only [Metric.mem_ball,dist_zero_right] at hx hy ⊢
    have hh := norm_add_le (x : E) (y : E)
    change ‖(x : E)+(y : E)‖ < 1
    have hx' : ‖(x : E)‖ < 1/2 := hx
    have hy' : ‖(y : E)‖ < 1/2 := hy
    linarith
  have hm := measure_mono (μ := (volume : Measure K).prod (volume : Measure Kᗮ)) hsub
  rw [Measure.prod_prod,hp.measure_preimage Metric.isOpen_ball.measurableSet.nullMeasurableSet] at hm
  rw [Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2),
      Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2)] at hm
  have hd := K.finrank_add_finrank_orthogonal
  have he : ENNReal.ofReal ((1/2 : ℝ)^Module.finrank ℝ K) *
      ENNReal.ofReal ((1/2 : ℝ)^Module.finrank ℝ Kᗮ) =
      ((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity),← pow_add,hd,
      ENNReal.ofReal_pow (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num [ENNReal.inv_pow]
  have hh : ((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ *
      ((volume : Measure K) (Metric.ball 0 1) * (volume : Measure Kᗮ) (Metric.ball 0 1)) ≤
        (volume : Measure E) (Metric.ball 0 1) := by
    rw [← he]
    convert hm using 1
    ring
  have h0 : (2 : ℝ≥0∞)^Module.finrank ℝ E ≠ 0 := by positivity
  have ht : (2 : ℝ≥0∞)^Module.finrank ℝ E ≠ ∞ := by finiteness
  calc
    _ = (2 : ℝ≥0∞)^Module.finrank ℝ E *
        (((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ *
          ((volume : Measure K) (Metric.ball 0 1) * (volume : Measure Kᗮ) (Metric.ball 0 1))) := by
      rw [← mul_assoc,ENNReal.mul_inv_cancel h0 ht,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hh

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

omit [Nontrivial E] in
lemma measurable_capFunction {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : Measurable g) (z : E) (t : ℝ) : Measurable (capFunction g z t) :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) hg measurable_const

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
lemma radius_mass_le (K : Submodule ℝ E) {b : ℕ} (hb : b+1 ≤ Module.finrank ℝ K)
    (h2b : 2*b ≤ Module.finrank ℝ K) {t : ℝ} (ht : 0 < t) :
    ((volume : Measure K).toSphere univ) *
      ENNReal.ofReal (t^(Module.finrank ℝ K-b)/((Module.finrank ℝ K-b : ℕ) : ℝ)) ≤
        2 * (volume : Measure K) (Metric.ball 0 1) * ENNReal.ofReal (t^(Module.finrank ℝ K-b)) := by
  let k := Module.finrank ℝ K
  have hkb : (0 : ℝ) < (k-b : ℕ) := by exact_mod_cast (by dsimp [k]; omega : 0 < k-b)
  have hratio : (k : ℝ) * (t^(k-b)/((k-b : ℕ) : ℝ)) ≤ 2*t^(k-b) := by
    have hk : (k : ℝ) ≤ 2*(k-b : ℕ) := by exact_mod_cast (by dsimp [k]; omega : k ≤ 2*(k-b))
    rw [← mul_div_assoc,div_le_iff₀ hkb]
    have h := mul_le_mul_of_nonneg_right hk (pow_nonneg ht.le (k-b))
    nlinarith [h]
  rw [Measure.toSphere_apply_univ]
  calc
    _ = (volume : Measure K) (Metric.ball 0 1) *
        ENNReal.ofReal ((k : ℝ)*(t^(k-b)/((k-b : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
      ring
    _ ≤ (volume : Measure K) (Metric.ball 0 1) * ENNReal.ofReal (2*t^(k-b)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hratio)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num; ring

lemma controlled_cap_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) (h2b : 2*b ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ s, capFunction g z t s ∂Affine.sphereLaw E) ≤
      (2 : ℝ≥0∞)^(Module.finrank ℝ E+1) * C * ENNReal.ofReal (t^(k-b)) := by
  have hball := Polar.radial_ball_integral (measurable_capFunction hg z t)
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet] at hball
  change (∫⁻ y : E, ballCap g z t y ∂volume) = _ at hball
  have hh := ballCap_integral hg hc K hK hb hz ht
  rw [hball] at hh
  have hmass := radius_mass_le K (by simpa only [hK] using hb) (by simpa only [hK] using h2b) ht
  rw [hK] at hmass
  have hratio := Polar.orthogonal_volume_ratio K
  have hv0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hfinal : (volume : Measure E) (Metric.ball 0 1) *
      (∫⁻ s, capFunction g z t s ∂Affine.sphereLaw E) ≤
      (volume : Measure E) (Metric.ball 0 1) *
        ((2 : ℝ≥0∞)^(Module.finrank ℝ E+1)*C*ENNReal.ofReal (t^(k-b))) := by
    calc
      _ ≤ (volume : Measure K).toSphere univ*C*ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ))*
          (volume : Measure Kᗮ) (Metric.ball 0 1) := hh
      _ = ((volume : Measure K).toSphere univ*ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)))*
          C*(volume : Measure Kᗮ) (Metric.ball 0 1) := by ring
      _ ≤ (2*(volume : Measure K) (Metric.ball 0 1)*ENNReal.ofReal (t^(k-b)))*
          C*(volume : Measure Kᗮ) (Metric.ball 0 1) := by gcongr
      _ = ((volume : Measure K) (Metric.ball 0 1)*(volume : Measure Kᗮ) (Metric.ball 0 1))*
          (2*C*ENNReal.ofReal (t^(k-b))) := by ring
      _ ≤ ((2 : ℝ≥0∞)^Module.finrank ℝ E*(volume : Measure E) (Metric.ball 0 1))*
          (2*C*ENNReal.ofReal (t^(k-b))) := mul_le_mul' hratio le_rfl
      _ = _ := by rw [pow_succ]; ring
  exact (ENNReal.mul_le_mul_iff_right hv0 hvt).mp hfinal

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


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Slice.controlled_cap_bound := @_root_.OAI.SubsphereCurrent.Slice.controlled_cap_bound
