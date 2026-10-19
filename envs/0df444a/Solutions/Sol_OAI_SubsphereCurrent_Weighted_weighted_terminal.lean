-- Prove2me | solution 1 for OAI.SubsphereCurrent.Weighted.weighted_terminal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:18:13.755506+00:00
-- url     : https://prove2.me/submissions/ff96ad2b-695d-46bf-8ee5-85c72729ebc3

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/Weighted.lean:L168-L213
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Weighted.weighted_terminal. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Theorems.Thm_OAI_SubsphereRegression_sphereLaw_cap_raw

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Affine ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Stream
variable {J : Type*} [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J] [Nonempty J]
  {T : ℕ}

end Stream
end SubsphereCurrent.Fixed
end
end
section
/-! Exact Gaussian reconstruction for an affine-sphere test. The complementary
rows are independent random parameters, not an extra sample channel to a learner. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
variable {d n : ℕ}
namespace Test
variable (A : Test d n)

lemma measurable_point : Measurable A.point := by unfold point; fun_prop

lemma norm_point (s : Sphere A.space) : ‖A.point s‖ = 1 := by
  have hs : ‖(s.val : Vector d)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have ho : ⟪A.center, (s.val : Vector d)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hz : ‖A.point s‖^2 = 1 := by
    rw [point,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.point s)]

lemma project_point (s : Sphere A.space) : A.project (A.point s) = s.val := by
  simp [project,point,map_smul,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    smul_smul,A.radius_positive.ne']

lemma project_error (s : Sphere A.space) (y : Vector d) :
    ‖A.project y-s.val‖ ≤ ‖y-A.point s‖/A.radius := by
  rw [← A.project_point s]
  have he : A.project y - A.project (A.point s) =
      A.radius⁻¹ • A.space.orthogonalProjectionOnto (y-A.point s) := by
    simp only [project,← smul_sub,← map_sub]
    congr 2
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr A.radius_positive),div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left (A.space.norm_orthogonalProjectionOnto_apply_le _) (inv_nonneg.mpr A.radius_positive.le)).trans_eq (mul_comm _ _)

lemma angular_project_error {ε : ℝ} (s : Sphere A.space) (y : Vector d)
    (hy : ‖y‖ = 1) (h : Real.arccos ⟪y,A.point s⟫ ≤ ε) :
    ‖A.project y-s.val‖ ≤ ε/A.radius := by
  apply (A.project_error s y).trans
  apply div_le_div_of_nonneg_right _ A.radius_positive.le
  have hc : ‖y-A.point s‖ ≤ Real.arccos ⟪y,A.point s⟫ := by
    simpa only [dist_eq_norm] using (SubsphereRegression.chord_le_arccos
      (⟨y,mem_sphere_zero_iff_norm.mpr hy⟩ : Sphere (Vector d))
      ⟨A.point s,mem_sphere_zero_iff_norm.mpr (A.norm_point s)⟩)
  exact hc.trans h

end Test

namespace Simulation
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (A : Test d n) (L : Fixed.Stream (Vector d) J T)

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Fixed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Stream
variable {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ}
end Stream
end SubsphereCurrent.Fixed
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Affine
namespace Simulation
attribute [local instance] OAI.SubsphereCurrent.Affine.Simulation.affineSimulationSphereLaw_probability
variable {d n : ℕ} (A : Test d n) [Nontrivial A.space]
  {J : Type*} [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
  {T : ℕ} (L : Fixed.Stream (Vector d) J T)

end Simulation
end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted
variable {d n m : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
variable {V : Type*} [Fintype V]

end SubsphereCurrent.Weighted
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.Weighted ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

section
universe v

end

lemma terminal_test {d n : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    (u : Sphere d) {ε : ℝ} (hε : 0 < ε) (hsmall : ε/A.radius ≤ 1)
    {a : ℝ} (ha : a ≤ (n-1 : ℕ)) :
    Affine.sphereLaw A.space {s : Affine.Sphere A.space |
      Real.arccos ⟪u.val,A.point s⟫ ≤ ε} ≤
        ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^a := by
  have hsub : {s : Affine.Sphere A.space | Real.arccos ⟪u.val,A.point s⟫ ≤ ε} ⊆
      {s : Affine.Sphere A.space | dist s.val (A.project u.val) ≤ ε/A.radius} := by
    intro s hs
    simpa only [Set.mem_ofPred_eq,dist_eq_norm,norm_sub_rev] using
      A.angular_project_error s u.val (mem_sphere_zero_iff_norm.mp u.property) hs
  have hb := SubsphereRegression.sphereLaw_cap_raw (A.project u.val)
    (div_pos hε A.radius_positive) hsmall (Module.finrank_pos (R := ℝ) (M := A.space))
  rw [A.dimension] at hb
  calc
    _ ≤ SubsphereRegression.sphereLaw {s : Affine.Sphere A.space |
        dist s.val (A.project u.val) ≤ ε/A.radius} := measure_mono hsub
    _ ≤ _ := hb.trans (mul_le_mul' le_rfl (by
      rw [ENNReal.ofReal_pow (div_nonneg hε.le A.radius_positive.le),← ENNReal.rpow_natCast]
      exact ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr hsmall) ha))

lemma terminal_average {d n : ℕ} (A : Affine.Test d n) [Nontrivial A.space]
    (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    {ε : ℝ} (hε : 0 < ε) (hsmall : ε/A.radius ≤ 1)
    {a : ℝ} (ha : a ≤ (n-1 : ℕ)) :
    (∫⁻ s : Affine.Sphere A.space, terminalInput π ε (onTest A s)
      ∂Affine.sphereLaw A.space) ≤
        ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^a := by
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := Fixed.sphereLaw_probability
  have he : ∀ s : Affine.Sphere A.space, terminalInput π ε (onTest A s) =
      ∫⁻ u : Sphere d, (if Real.arccos ⟪u.val,A.point s⟫ ≤ ε then (1 : ℝ≥0∞) else 0) ∂π := by
    intro s
    have hm : MeasurableSet {u : Sphere d | Real.arccos ⟪u.val,A.point s⟫ ≤ ε} :=
      measurableSet_le (by fun_prop) measurable_const
    simp only [terminalInput,onTest]
    rw [← one_mul (π _),← lintegral_indicator_const hm 1]
    rfl
  simp_rw [he]
  have hm : Measurable (fun z : Affine.Sphere A.space × Sphere d =>
      if Real.arccos ⟪z.2.val,A.point z.1⟫ ≤ ε then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_le (Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp measurable_snd).inner
        (A.measurable_point.comp measurable_fst))) measurable_const)
      measurable_const measurable_const
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ _ : Sphere d, ENNReal.ofReal ((3 : ℝ)*4^n)*
        (ENNReal.ofReal (ε/A.radius))^a ∂π := by
      apply lintegral_mono
      intro u
      have hs : MeasurableSet {s : Affine.Sphere A.space |
          Real.arccos ⟪u.val,A.point s⟫ ≤ ε} :=
        measurableSet_le (Real.continuous_arccos.measurable.comp
          (measurable_const.inner A.measurable_point)) measurable_const
      have he' : (fun s : Affine.Sphere A.space => if Real.arccos ⟪u.val,A.point s⟫ ≤ ε
          then (1 : ℝ≥0∞) else 0) =
        {s : Affine.Sphere A.space | Real.arccos ⟪u.val,A.point s⟫ ≤ ε}.indicator (fun _ => 1) := rfl
      dsimp only
      rw [he',lintegral_indicator_const hs,one_mul]
      exact terminal_test A u hε hsmall ha
    _ = _ := by simp

lemma weighted_terminal {d n : ℕ} (hd : 4 ≤ d) (hn : (d : ℝ)/2 ≤ n) (hnd : n ≤ d)
    (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    {ε : ℝ} (hε : 0 < ε) :
    norm d n (terminalInput π ε) ≤
      ENNReal.ofReal ((16 : ℝ)^d)*(ENNReal.ofReal ε)^((d : ℝ)/16) := by
  unfold norm
  apply iSup_le
  intro A
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  let : Nontrivial A.space := Module.nontrivial_of_finrank_pos (A.dimension ▸ hnpos)
  let : IsProbabilityMeasure (Affine.sphereLaw A.space) := Fixed.sphereLaw_probability
  have ha0 : (0 : ℝ) ≤ d/16 := by positivity
  have ha : (d : ℝ)/16 ≤ (n-1 : ℕ) := by
    rw [Nat.cast_sub hnpos,Nat.cast_one]
    linarith
  have hc : (3 : ℝ)*4^n ≤ 16^d := by
    calc
      (3 : ℝ)*4^n ≤ 4*4^d := mul_le_mul (by norm_num) (pow_le_pow_right₀ (by norm_num) hnd)
        (by positivity) (by positivity)
      _ = 4^(d+1) := by rw [pow_succ]; ring
      _ ≤ 4^(2*d) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by norm_num [pow_mul]
  by_cases hsmall : ε/A.radius ≤ 1
  · calc
      _ ≤ (ENNReal.ofReal A.radius)^((d : ℝ)/16) *
          (ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal (ε/A.radius))^((d : ℝ)/16)) :=
        mul_le_mul' le_rfl (terminal_average A π hε hsmall ha)
      _ = ENNReal.ofReal ((3 : ℝ)*4^n)*(ENNReal.ofReal ε)^((d : ℝ)/16) := by
        rw [mul_left_comm,← ENNReal.mul_rpow_of_nonneg _ _ ha0,
          ← ENNReal.ofReal_mul A.radius_positive.le]
        rw [← mul_div_assoc,mul_div_cancel_left₀ ε A.radius_positive.ne']
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
  · have hr : A.radius ≤ ε := by
      simpa only [one_mul] using le_of_lt ((lt_div_iff₀ A.radius_positive).mp (lt_of_not_ge hsmall))
    calc
      _ ≤ (ENNReal.ofReal A.radius)^((d : ℝ)/16)*1 :=
        mul_le_mul' le_rfl (by simpa using (lintegral_mono (fun _ => prob_le_one) :
          (∫⁻ s : Affine.Sphere A.space, terminalInput π ε (onTest A s)
            ∂Affine.sphereLaw A.space) ≤ ∫⁻ _ : Affine.Sphere A.space, (1 : ℝ≥0∞)
            ∂Affine.sphereLaw A.space))
      _ ≤ (ENNReal.ofReal ε)^((d : ℝ)/16) := by
        rw [mul_one]; exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hr) ha0
      _ ≤ _ := le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr (one_le_pow₀ (by norm_num)))

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

end SubsphereCurrent.Weighted

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Weighted
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Weighted.weighted_terminal := @_root_.OAI.SubsphereCurrent.Weighted.weighted_terminal
