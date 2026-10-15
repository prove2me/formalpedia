-- Prove2me | solution 1 for OAI.RuledApproximation.singular_inverse_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:33:55.646615+00:00
-- url     : https://prove2.me/submissions/59759ebd-eca5-47df-b1fa-00bcffb86f39

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularInverse.lean:L42-L125
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_inverse_small. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt
import Theorems.Thm_OAI_RuledApproximation_singularField_homogeneous_bounds

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularField_wall (p : ℝ) {b r : ℝ} (hr : 0 < r) :
    singularField p (vec2 b r) 1 + singularField p (vec2 b r) 0 =
      (r+b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r+p) ∧
    singularField p (vec2 b r) 1 - singularField p (vec2 b r) 0 =
      (r-b)/2*(r/(1/2:ℝ))^(p-2)*((2-p)*b/r-p) := by
  have hp : (r/(1/2:ℝ))^(p-1) = (r/(1/2:ℝ))^(p-2)*(r/(1/2)) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one (by positivity : r/(1/2:ℝ)≠0)]
  simp only [singularField,vec2_apply_one,vec2_apply_zero,hp]
  constructor <;> field_simp <;> ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma vec2_coordinates (z : Plane) : vec2 (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

lemma singular_wall_coefficient_bound (p : ℝ) {z : Plane}
    (hz : 0 < z 1) (hb : |z 0| ≤ 2*z 1) {e : ℝ} (he : |e| ≤ 1) :
    |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
      ((2:ℝ)^(p-2)/2*(2*|2-p|+|p|))*(z 1)^(p-2) := by
  have hq : |z 0/z 1| ≤ 2 := by
    rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
    exact hb
  have ha : |(2-p)*(z 0/z 1)+e*p| ≤ 2*|2-p|+|p| := by
    calc
      _ ≤ |(2-p)*(z 0/z 1)|+|e*p| := abs_add_le _ _
      _ = |2-p| *|z 0/z 1|+|e| *|p| := by rw [abs_mul,abs_mul]
      _ ≤ |2-p| *2+1*|p| := add_le_add
        (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
        (mul_le_mul_of_nonneg_right he (abs_nonneg _))
      _ = _ := by ring
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (z 1/(1/2:ℝ))^(p-2)/2)]
  calc
    _ ≤ (z 1/(1/2:ℝ))^(p-2)/2*(2*|2-p|+|p|) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by
      rw [show z 1/(1/2:ℝ)=2*z 1 by ring,Real.mul_rpow (by norm_num) hz.le]
      ring

lemma singular_uniform_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) ∧
      ∀ e : ℝ, |e| ≤ 1 → |(z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)| ≤
        C*(z 1)^(p-2) := by
  obtain ⟨C,hC,hbound⟩ := singularField_homogeneous_bounds p
  let W := (2:ℝ)^(p-2)/2*(2*|2-p|+|p|)
  refine ⟨max C W,hC.trans (le_max_left _ _),?_⟩
  intro z hz hb
  obtain ⟨h0,h1⟩ := hbound z hz hb
  refine ⟨h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
    h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),?_⟩
  intro e he
  exact (singular_wall_coefficient_bound p hz hb he).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularInverse ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma inverse_in_closedBall {V : Plane → Plane} {q : Plane} {R k : ℝ} (hR : 0 ≤ R)
    (hcont : ∀ z ∈ Metric.closedBall q R, DifferentiableAt ℝ V z)
    (hsize : ∀ z ∈ Metric.closedBall q R, |k| *‖V z‖ ≤ R)
    (hder : ∀ z ∈ Metric.closedBall q R, |k| *‖fderiv ℝ V z‖ ≤ 1/2) :
    ∃ z ∈ Metric.closedBall q R, q = z+k • V z := by
  let S := Metric.closedBall q R
  let F : S → S := fun z => ⟨q-k • V z,by
    rw [Metric.mem_closedBall,dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs]
    exact hsize z z.2⟩
  have hL : ContractingWith (1/2 : NNReal) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z => k • V z) (C := 1/2)
      (fun z hz => (hcont z hz).const_smul k)
      (fun z hz => by
        rw [fderiv_fun_const_smul (hcont z hz),norm_smul,Real.norm_eq_abs]
        exact hder z hz)
      (convex_closedBall q R) y.2 x.2
    change ‖(q-k • V x)-(q-k • V y)‖ ≤ (1/2)*‖(x:Plane)-(y:Plane)‖
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
    exact he
  have : Nonempty S := ⟨⟨q,Metric.mem_closedBall_self hR⟩⟩
  have : IsClosed S := Metric.isClosed_closedBall
  let z := ContractingWith.fixedPoint F hL
  have hz := congrArg Subtype.val hL.fixedPoint_isFixedPt
  refine ⟨z,z.2,?_⟩
  change q-k • V z = z at hz
  exact (sub_eq_iff_eq_add.mp hz)

lemma singular_inverse_small {p : ℝ} (hp2 : p < 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d c B T k : ℝ), 0 < d → 0 ≤ c →
      c*C*d^(p-2) ≤ 1/8 → 2*d ≤ T → T ≤ 1 → |B| ≤ T → |k| ≤ c →
      ∃ z : Plane, d ≤ z 1 ∧ z 1 ≤ 2 ∧ |z 0| ≤ z 1 ∧
        vec2 B T = z+k • singularField p z := by
  obtain ⟨C,hC,hbound⟩ := singular_uniform_bounds p
  refine ⟨C,hC,?_⟩
  intro d c B T k hd hc hsmall hT hT1 hB hk
  have hTp : 0 < T := by linarith
  have hCp : 0 ≤ C := by linarith
  have hball : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4),
      d ≤ z 1 ∧ z 1 ≤ 5*T/4 ∧ |z 0| ≤ 2*z 1 := by
    intro z hz
    rw [Metric.mem_closedBall,dist_eq_norm] at hz
    have hr := (plane_coordinate_le (z-vec2 B T) 1).trans hz
    have hb := (plane_coordinate_le (z-vec2 B T) 0).trans hz
    change |z 1-T| ≤ T/4 at hr
    change |z 0-B| ≤ T/4 at hb
    obtain ⟨hrl,hru⟩ := abs_le.mp hr
    have hb' : |z 0| ≤ T/4+T := by
      calc
        _ = |(z 0-B)+B| := by congr 1; ring
        _ ≤ |z 0-B|+|B| := abs_add_le _ _
        _ ≤ T/4+T := add_le_add hb hB
    exact ⟨by linarith,by linarith,by linarith⟩
  have hprod : ∀ z ∈ Metric.closedBall (vec2 B T) (T/4), |k| * C*(z 1)^(p-2) ≤ 1/8 := by
    intro z hz
    have hz' := hball z hz
    have hzp : 0 < z 1 := hd.trans_le hz'.1
    calc
      _ ≤ c*C*(z 1)^(p-2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk hCp) (by positivity)
      _ ≤ c*C*d^(p-2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hd hz'.1 (by linarith)) (mul_nonneg hc hCp)
      _ ≤ _ := hsmall
  obtain ⟨z,hz,heq⟩ := inverse_in_closedBall (V := singularField p)
    (k := k) (show 0 ≤ T/4 by positivity)
    (fun z hz => (singularField_contDiffAt p (hd.trans_le (hball z hz).1)).differentiableAt (by norm_num))
    (fun z hz => by
      have hz' := hball z hz
      have hzp := hd.trans_le hz'.1
      have hV := (hbound z hzp hz'.2.2).1
      calc
        _ ≤ |k| * (C*(z 1)^(p-1)) := mul_le_mul_of_nonneg_left hV (abs_nonneg _)
        _ = (|k| * C*(z 1)^(p-2))*z 1 := by
          rw [show p-1=p-2+1 by ring,Real.rpow_add_one hzp.ne']
          ring
        _ ≤ (1/8)*z 1 := mul_le_mul_of_nonneg_right (hprod z hz) hzp.le
        _ ≤ T/4 := by linarith)
    (fun z hz => by
      have hz' := hball z hz
      have hV := (hbound z (hd.trans_le hz'.1) hz'.2.2).2.1
      exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans
        (by simpa only [mul_assoc] using hprod z hz)).trans (by norm_num))
  have hz' := hball z hz
  have hzp := hd.trans_le hz'.1
  have htheta : ∀ e : ℝ, |e| ≤ 1 →
      0 < 1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p)) := by
    intro e he
    have ht := mul_le_mul_of_nonneg_left ((hbound z hzp hz'.2.2).2.2 e he) (abs_nonneg k)
    rw [← abs_mul] at ht
    have ht' : |k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+e*p))| ≤ 1/8 := by
      exact ht.trans (by simpa only [mul_assoc] using hprod z hz)
    have := (abs_le.mp ht').1
    linarith
  have he0 := congrArg (fun w : Plane => w 0) heq
  have he1 := congrArg (fun w : Plane => w 1) heq
  change B = z 0+k*singularField p z 0 at he0
  change T = z 1+k*singularField p z 1 at he1
  have hw := singularField_wall p (b := z 0) hzp
  rw [vec2_coordinates] at hw
  have hwplus : T+B = (z 1+z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+1*p))) := by
    calc
      _ = z 1+z 0+k*(singularField p z 1+singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.1]; ring
  have hwminus : T-B = (z 1-z 0)*(1+k*((z 1/(1/2:ℝ))^(p-2)/2*((2-p)*(z 0/z 1)+(-1)*p))) := by
    calc
      _ = z 1-z 0+k*(singularField p z 1-singularField p z 0) := by rw [he0,he1]; ring
      _ = _ := by rw [hw.2]; ring
  have hp0 : 0 ≤ z 1+z 0 := (mul_nonneg_iff_of_pos_right (htheta 1 (by norm_num))).mp
    (by rw [← hwplus]; linarith [(abs_le.mp hB).1])
  have hm0 : 0 ≤ z 1-z 0 := (mul_nonneg_iff_of_pos_right (htheta (-1) (by norm_num))).mp
    (by rw [← hwminus]; linarith [(abs_le.mp hB).2])
  exact ⟨z,hz'.1,by linarith [hz'.2.1],abs_le.mpr ⟨by linarith,by linarith⟩,heq⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_inverse_small := @_root_.OAI.RuledApproximation.singular_inverse_small
