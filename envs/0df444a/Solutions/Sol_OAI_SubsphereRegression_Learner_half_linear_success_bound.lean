-- Prove2me | solution 1 for OAI.SubsphereRegression.Learner.half_linear_success_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:23:08.30883+00:00
-- url     : https://prove2.me/submissions/3e49a00b-7477-4164-b4f5-48fc7e3ecde9

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/HalfPrecision.lean:L126-L170
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.Learner.half_linear_success_bound. The node keeps its source
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
import Theorems.Thm_OAI_SubsphereRegression_prod_null_set_bound
import Theorems.Thm_OAI_SubsphereRegression_sphere_three_orbit_bound

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
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Regression.Blocks ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

end Learner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereRegression

end

end OAI

-- ---- from OAI.Probability.Subsphere.Geometry.Integration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

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

lemma twinTurn_inner (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : WithLp 2 (F × F)) : ⟪x,twinTurn F x⟫ = 0 := by
  simp only [twinTurn, LinearIsometryEquiv.trans_apply, WithLp.prod_inner_apply]
  change ⟪x.ofLp.1,-x.ofLp.2⟫ + ⟪x.ofLp.2,x.ofLp.1⟫ = 0
  rw [inner_neg_right,real_inner_comm x.ofLp.2 x.ofLp.1]
  ring

lemma twinTurn_square (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : WithLp 2 (F × F)) : twinTurn F (twinTurn F x) = -x := by
  apply WithLp.ofLp_injective
  change (-x.ofLp.1,-x.ofLp.2) = (-x).ofLp
  rfl

lemma exists_even_turn {k : ℕ} (hk : Module.finrank ℝ E = k+k) :
    ∃ e : E ≃ₗᵢ[ℝ] E, (∀ x, ⟪x,e x⟫ = 0) ∧ (∀ x, e (e x) = -x) := by
  let b := (stdOrthonormalBasis ℝ E).reindex ((finCongr hk).trans finSumFinEquiv.symm)
  let f : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    b.repr.trans (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin k ⊕ Fin k => ℝ))
  let e := (f.trans (twinTurn (EuclideanSpace ℝ (Fin k)))).trans f.symm
  refine ⟨e, ?_, ?_⟩
  · intro x
    rw [← f.inner_map_map]
    simpa [e] using twinTurn_inner (EuclideanSpace ℝ (Fin k)) (f x)
  · intro x
    apply f.injective
    simp [e, twinTurn_square]

omit [FiniteDimensional ℝ E] in
lemma subspace_dimension (U : Submodule ℝ E) {k : ℕ} (hk : k ≤ Module.finrank ℝ U) :
    ∃ F : Submodule ℝ E, F ≤ U ∧ Module.finrank ℝ F = k := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := U) hk
  let w : Fin k → E := fun i => v i
  have hw : LinearIndependent ℝ w := hv.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨Submodule.span ℝ (Set.range w), ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (v i).property)
  · simpa using finrank_span_eq_card hw

lemma exists_small_fixed (U : Submodule ℝ E) :
    ∃ F : Submodule ℝ E, F ≤ Uᗮ ∧
      Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ U + 1 ∧
      ∃ e : F ≃ₗᵢ[ℝ] F, (∀ x, ⟪x,e x⟫ = 0) ∧ (∀ x, e (e x) = -x) := by
  let k := Module.finrank ℝ Uᗮ / 2
  obtain ⟨F,hFU,hF⟩ := subspace_dimension Uᗮ (k := k+k) (by dsimp [k]; omega)
  refine ⟨F,hFU,?_,exists_even_turn hF⟩
  have hU := U.finrank_add_finrank_orthogonal
  have hF' := F.finrank_add_finrank_orthogonal
  dsimp [k] at hF
  omega

end SubsphereCurrent.Quarter
end
end

end OAI

-- ---- from OAI.Probability.Subsphere.Estimates.HalfPrecision ----
namespace OAI

noncomputable section

namespace SubsphereRegression
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace Learner
lemma half_linear_success_bound {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 32 ≤ d) (hT : 32*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (7/16 : ℝ) := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := ENNReal.ofReal (7/16 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  obtain ⟨F,hFU,hFdim,e,he,he2⟩ := SubsphereCurrent.Quarter.exists_small_fixed U
  have hUF : U ≤ Fᗮ := by
    have h := Submodule.orthogonal_le hFU
    simpa only [Submodule.orthogonal_orthogonal] using h
  have hF : 16 * Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ (Vector d) := by
    rw [finrank_euclideanSpace_fin]
    omega
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_three_orbit_bound F hF e he he2
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s t hlabel hs ht
    have hout : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      exact hlabel (z.2 i) (hUF (Submodule.subset_span (Set.mem_range_self i)))
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [hout, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith
end Learner
end SubsphereRegression
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
namespace Learner
end Learner

end SubsphereRegression
end
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereCurrent

end SubsphereCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression OAI.SubsphereRegression.Learner
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.SubsphereRegression.Learner.half_linear_success_bound := @_root_.OAI.SubsphereRegression.Learner.half_linear_success_bound
