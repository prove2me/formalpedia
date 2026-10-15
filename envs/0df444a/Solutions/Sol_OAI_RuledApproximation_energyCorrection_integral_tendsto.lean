-- Prove2me | solution 1 for OAI.RuledApproximation.energyCorrection_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:55:48.750771+00:00
-- url     : https://prove2.me/submissions/0eeda64f-9263-49a7-9fc4-849828af6e37

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularEnergy.lean:L147-L195
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.energyCorrection_integral_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Definitions.Def_OAI_Geometry_RuledCovering_CapAsymptotics
import Definitions.Def_OAI_Geometry_RuledCovering_SingularEnergy
import Theorems.Thm_OAI_RuledApproximation_coneTriangle_isCompact
import Theorems.Thm_OAI_RuledApproximation_singularDomain_isCompact
import Theorems.Thm_OAI_RuledApproximation_singularField_homogeneous_bounds

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceiling_nonneg {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (b : ℝ) :
    0 ≤ ceilingPolynomial p b := by
  unfold ceilingPolynomial
  have : 0 ≤ 2-p := sub_nonneg.mpr hp2
  positivity

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c^q) (𝓝[>] 0) (𝓝 ((0:ℝ)^q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularEnergy ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularEnergy_nonneg (p : ℝ) (z : Plane) : 0 ≤ singularEnergy p z := by
  unfold singularEnergy
  positivity

lemma singularEnergy_measurable (p : ℝ) : Measurable (singularEnergy p) := by
  unfold singularEnergy singularField
  simp only [vec2_apply_zero,vec2_apply_one]
  fun_prop

lemma singularField_zero {p : ℝ} (hp : 1 < p) : singularField p 0 = 0 := by
  ext i
  fin_cases i <;> simp [singularField,vec2,Real.zero_rpow (show p-1 ≠ 0 by linarith)]

lemma singularEnergy_zero {p : ℝ} (hp : 1 < p) : singularEnergy p 0 = 0 := by
  simp [singularEnergy,singularField_zero hp]

lemma singularEnergy_bounded {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ coneTriangle 2, singularEnergy p z ≤ C := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  let B := C*(2:ℝ)^(p-1)
  have hB : 0 ≤ B := mul_nonneg (by linarith) (by positivity)
  refine ⟨3*B^2,by positivity,?_⟩
  intro z hz
  have hv : ‖singularField p z‖ ≤ B := by
    by_cases hzr : z 1 = 0
    · have he : z = 0 := by
        have hb : z 0 = 0 := abs_nonpos_iff.mp (hz.2.2.trans_eq hzr)
        ext i
        fin_cases i <;> assumption
      rw [he,singularField_zero hp,norm_zero]
      exact hB
    · have hz1 : 0 < z 1 := lt_of_le_of_ne hz.1 (Ne.symm hzr)
      exact (hbound z hz1 (hz.2.2.trans (by linarith))).1.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1 hz.2.1 (by linarith)) (by linarith))
  have hx := (plane_coordinate_le (singularField p z) 0).trans hv
  have hy := (plane_coordinate_le (singularField p z) 1).trans hv
  have hx' := sq_le_sq₀ (abs_nonneg _) hB |>.mpr hx
  have hy' := sq_le_sq₀ (abs_nonneg _) hB |>.mpr hy
  simp only [sq_abs] at hx' hy'
  unfold singularEnergy
  nlinarith only [hx',hy']

lemma singularEnergy_integrable {p : ℝ} (hp : 1 < p) :
    IntegrableOn (singularEnergy p) (coneTriangle 2) := by
  obtain ⟨C,_,hC⟩ := singularEnergy_bounded hp
  apply IntegrableOn.of_bound (coneTriangle_isCompact 2).measure_lt_top
    (singularEnergy_measurable p).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (coneTriangle_isCompact 2).measurableSet] with z hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg (singularEnergy_nonneg p z)] using hC z hz

lemma energyCorrection_measurable (p c : ℝ) : Measurable (energyCorrection p c) := by
  unfold energyCorrection
  have hm := singularEnergy_measurable p
  fun_prop

lemma energy_sqrt_ge_one (p c : ℝ) (z : Plane) :
    1 ≤ Real.sqrt (1+c^2*singularEnergy p z) := by
  have he := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1+c^2*singularEnergy p z by
    nlinarith only [mul_nonneg (sq_nonneg c) (singularEnergy_nonneg p z)])
  simpa only [Real.sqrt_one] using he

lemma energyCorrection_norm (p c : ℝ) (z : Plane) :
    ‖energyCorrection p c z‖ ≤ singularEnergy p z/2 := by
  have hH := singularEnergy_nonneg p z
  have hs := energy_sqrt_ge_one p c z
  unfold energyCorrection
  rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_nonneg hH,
    abs_of_pos (by nlinarith : 0 < Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1))]
  apply div_le_div_of_nonneg_left hH (by norm_num)
  nlinarith

lemma energyCorrection_tendsto (p : ℝ) (z : Plane) :
    Tendsto (fun c : ℝ => energyCorrection p c z) (𝓝[>] 0) (𝓝 (-singularEnergy p z/2)) := by
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun c : ℝ => Real.sqrt (1+c^2*singularEnergy p z)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun c : ℝ => 1+c^2*singularEnergy p z) (𝓝[>] 0) (𝓝 1) := by
      simpa using ((h0.pow 2).mul_const (singularEnergy p z)).const_add 1
    simpa only [Real.sqrt_one] using h.sqrt
  have hd : Tendsto (fun c : ℝ => Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1)) (𝓝[>] 0) (𝓝 2) := by
    convert hs.mul (hs.add (tendsto_const_nhds (x := (1:ℝ)))) using 1
    norm_num
  exact tendsto_const_nhds.div hd (by norm_num)

lemma singularDomain_subset_cone (p gamma c : ℝ) : singularDomain p gamma c ⊆ coneTriangle 2 := by
  intro z hz
  exact ⟨(abs_nonneg _).trans hz.2.2.1,hz.2.1,hz.2.2.1⟩

lemma singularDomain_eventually_mem {p gamma : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (hg : 0 < gamma)
    {z : Plane} (hz : z ∈ coneTriangle 2) (hz1 : 0 < z 1) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, z ∈ singularDomain p gamma c ↔ z ∈ coneTriangle (1/2) := by
  by_cases hr : z 1 ≤ 1/2
  · filter_upwards [self_mem_nhdsWithin,
      (right_rpow_tendsto_zero hg).eventually (gt_mem_nhds hz1)] with c hc hd
    have hm : z ∈ singularDomain p gamma c := by
      refine ⟨hd.le,hz.2.1,hz.2.2,hr.trans ?_⟩
      have hn := ceiling_nonneg hp hp2 (z 0)
      have hn' : 0 ≤ c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ) :=
        add_nonneg (mul_nonneg (sq_nonneg c) hn) (Real.rpow_nonneg hc.le _)
      linarith
    exact ⟨fun _ => ⟨hz.1,hr,hz.2.2⟩,fun _ => hm⟩
  · have ht : Tendsto (fun c : ℝ => (1/2:ℝ)+c^2*ceilingPolynomial p (z 0)+c^(5/2:ℝ))
        (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.add ((h0.pow 2).mul_const (ceilingPolynomial p (z 0)))).add
        (right_rpow_tendsto_zero (q := (5/2:ℝ)) (by norm_num))
    filter_upwards [ht.eventually (gt_mem_nhds (lt_of_not_ge hr))] with c hc
    exact ⟨fun h => False.elim (not_le_of_gt hc h.2.2.2),fun h => False.elim (hr h.2.1)⟩

lemma energyCorrection_integral_tendsto {p gamma : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hg : 0 < gamma) :
    Tendsto (fun c : ℝ => ∫ z in singularDomain p gamma c, energyCorrection p c z) (𝓝[>] 0)
      (𝓝 (-(∫ z in coneTriangle (1/2), singularEnergy p z)/2)) := by
  have ht : Tendsto (fun c : ℝ => ∫ z in coneTriangle 2,
      (singularDomain p gamma c).indicator (energyCorrection p c) z) (𝓝[>] 0)
      (𝓝 (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => singularEnergy p z/2)
    · exact Filter.Eventually.of_forall (fun c =>
        ((energyCorrection_measurable p c).indicator (singularDomain_isCompact p gamma c).measurableSet).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall (fun z => by
        by_cases hz : z ∈ singularDomain p gamma c
        · rw [Set.indicator_of_mem hz]
          exact energyCorrection_norm p c z
        · rw [Set.indicator_of_notMem hz,norm_zero]
          exact div_nonneg (singularEnergy_nonneg p z) (by norm_num)))
    · exact (singularEnergy_integrable hp).div_const 2
    · filter_upwards [ae_restrict_mem (coneTriangle_isCompact 2).measurableSet] with z hz
      by_cases hzr : z 1 = 0
      · have he : z = 0 := by
          have hb : z 0 = 0 := abs_nonpos_iff.mp (hz.2.2.trans_eq hzr)
          ext i
          fin_cases i <;> assumption
        subst z
        have he : ∀ c : ℝ, energyCorrection p c 0 = 0 := by simp [energyCorrection,singularEnergy_zero hp]
        simp [Set.indicator,he,singularEnergy_zero hp]
      · have he := singularDomain_eventually_mem (le_trans (by norm_num) hp.le) hp2 hg hz
          (lt_of_le_of_ne hz.1 (Ne.symm hzr))
        by_cases hza : z ∈ coneTriangle (1/2)
        · rw [Set.indicator_of_mem hza]
          apply (energyCorrection_tendsto p z).congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_mem (hc.mpr hza) _).symm
        · rw [Set.indicator_of_notMem hza]
          apply tendsto_const_nhds.congr'
          filter_upwards [he] with c hc
          exact (Set.indicator_of_notMem (fun h => hza (hc.mp h)) _).symm
  have he₁ : ∀ c : ℝ, (∫ z in coneTriangle 2, (singularDomain p gamma c).indicator (energyCorrection p c) z) =
      ∫ z in singularDomain p gamma c, energyCorrection p c z := by
    intro c
    rw [integral_indicator (singularDomain_isCompact p gamma c).measurableSet,
      Measure.restrict_restrict (singularDomain_isCompact p gamma c).measurableSet,
      Set.inter_eq_left.mpr (singularDomain_subset_cone p gamma c)]
  have he₂ : (∫ z in coneTriangle 2, (coneTriangle (1/2)).indicator (fun z => -singularEnergy p z/2) z) =
      -(∫ z in coneTriangle (1/2), singularEnergy p z)/2 := by
    rw [integral_indicator (coneTriangle_isCompact (1/2)).measurableSet,
      Measure.restrict_restrict (coneTriangle_isCompact (1/2)).measurableSet,
      Set.inter_eq_left.mpr (show coneTriangle (1/2) ⊆ coneTriangle 2 from fun z hz =>
        ⟨hz.1,hz.2.1.trans (by norm_num),hz.2.2⟩),integral_div,integral_neg]
  simpa only [he₁,he₂] using ht

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.energyCorrection_integral_tendsto := @_root_.OAI.RuledApproximation.energyCorrection_integral_tendsto
