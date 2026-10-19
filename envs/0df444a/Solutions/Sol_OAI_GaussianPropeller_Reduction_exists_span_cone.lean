-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.exists_span_cone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:20:53.461833+00:00
-- url     : https://prove2.me/submissions/4e920d03-16d3-4a6e-8e2d-4bae6202f478

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapReduction.lean:L61-L114
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.exists_span_cone. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem measurableSet_closedCell (z : Fin k → Space d) (i : Fin k) :
    MeasurableSet (closedCell z i) := by
  unfold closedCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    (by fun_prop) (by fun_prop))

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Gram ----
namespace OAI

universe uE uF uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace

open scoped RealInnerProductSpace

namespace GaussianPropeller.Gram

variable {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] [DecidableEq ι] in

theorem independent_omit (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (i : ι) :
    LinearIndependent ℝ (fun j : {j : ι // j ≠ i} => z j) := by
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ E)
    (fun x hx => real_inner_self_pos.mpr hx) (-(innerₗ E) (z i))
  · intro j
    change 0 < -⟪z i, z j⟫
    exact neg_pos.mpr (hneg (Ne.symm j.property))
  · intro j l hjl
    exact (hneg (fun h => hjl (Subtype.ext h))).le

theorem span_omit_eq (z : ι → E) (hsum : ∑ i, z i = 0) (i : ι) :
    Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j)) =
      Submodule.span ℝ (Set.range z) := by
  classical
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hji : j ≠ i
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
    · have hji' : j = i := not_ne_iff.mp hji
      subst j
      let V := Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j))
      have hi : z i = -(∑ j ∈ Finset.univ.erase i, z j) := by
        have h := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
        rw [hsum] at h
        exact eq_neg_of_add_eq_zero_right h
      rw [hi]
      apply V.neg_mem
      apply V.sum_mem
      intro j hj
      exact Submodule.subset_span ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, rfl⟩

theorem finrank_span (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : Module.finrank ℝ (Submodule.span ℝ (Set.range z)) =
      Fintype.card ι - 1 := by
  rw [← span_omit_eq z hsum i, finrank_span_eq_card (independent_omit z hneg i)]
  simp [Fintype.card_subtype_compl (fun j : ι => j = i)]

end GaussianPropeller.Gram

end OAI

-- ---- from OAI.Probability.GaussianPropeller.GaussianCoordinates ----
namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic
section FamilyLaw
variable {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u,x⟫, fun x => ⟪v,x⟫; stdGaussian E] = ⟪u,v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

lemma hasGaussianLaw_innerFamily (v : ι → E) :
    HasGaussianLaw (fun x : E => fun i => ⟪v i,x⟫) (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => InnerProductSpace.toDual ℝ E (v i)))

lemma indep_innerFamily (v : ι → E) (hv : Pairwise (fun i j => ⟪v i,v j⟫ = 0)) :
    iIndepFun (fun i x => ⟪v i,x⟫) (stdGaussian E) := by
  exact (hasGaussianLaw_innerFamily v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => (covariance_inner_stdGaussian _ _).trans (hv hij))

lemma map_inner_stdGaussian (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map]

lemma map_orthonormal_stdGaussian (v : ι → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i,x⟫) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  rw [hi.map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [map_inner_stdGaussian, hv.1 i]
  norm_num

end FamilyLaw

end GaussianPropeller.Analytic

namespace GaussianPropeller.Analytic

open scoped ENNReal

section TripleLaw
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end TripleLaw
end GaussianPropeller.Analytic

end OAI

-- ---- from OAI.Probability.GaussianPropeller.PairBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.PairGeometry

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end GaussianPropeller.PairGeometry

namespace GaussianPropeller.Pair

-- [generator] trimmed: open GaussianPropeller.Analytic GaussianPropeller.PairIntegral GaussianPropeller.PairGeometry
open GaussianPropeller.Analytic GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianPropeller.Pair

namespace GaussianPropeller.Pair

open GaussianPropeller.Analytic GaussianPropeller.PairIntegral

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma integral_inner_eq_inner_integral (K : Set E) (w : E) :
    ∫ x in K, ⟪w,x⟫ ∂stdGaussian E = ⟪w, ∫ x in K, x ∂stdGaussian E⟫ := by
  exact (InnerProductSpace.toDual ℝ E w).integral_comp_comm
    IsGaussian.integrable_id.integrableOn

end GaussianPropeller.Pair

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Coordinates ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords
lemma exists_basis_zero {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E=n+1)
    (e : E) (he : ‖e‖=1) :
    ∃ b : OrthonormalBasis (Fin (n+1)) ℝ E, b 0=e := by
  have ho : Orthonormal ℝ (({0}:Set (Fin (n+1))).domRestrict (fun _ => e)) := by
    constructor
    · intro i; exact he
    · intro i j hij
      have hi : (i:Fin (n+1))=0 := i.2
      have hj : (j:Fin (n+1))=0 := j.2
      exact (hij (Subtype.ext (hi.trans hj.symm))).elim
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (ι:=Fin (n+1)) (by simpa using hn)
  exact ⟨b,hb 0 (by simp)⟩

end GaussianPropeller.Coords

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapReduction ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
open Coords
variable {d k n : ℕ} [NeZero k]

omit [NeZero k] in
lemma closedCell_cone [NeZero k] (z : Fin k → Space d) (i : Fin k) (r:ℝ) (hr:0<r)
    (x:Space d) : r•x ∈ closedCell z i ↔ x∈closedCell z i := by
  simp only [closedCell, mem_ofPred_eq,inner_smul_right]
  exact forall_congr' (fun j => mul_le_mul_iff_right₀ hr)

lemma coordinates_law {V : Submodule ℝ (Space d)}
    (b : OrthonormalBasis (Fin (n+1)) ℝ V) :
    (gaussian d).map (fun x => b.repr (V.orthogonalProjectionOnto x)) = gaussian (n+1) := by
  have ho : Orthonormal ℝ (fun j => (b j : Space d)) := by
    constructor
    · intro j; exact b.orthonormal.1 j
    · intro j l hjl; exact b.orthonormal.2 hjl
  have he : (fun x => b.repr (V.orthogonalProjectionOnto x)) =
      WithLp.toLp 2 ∘ (fun x => fun j => ⟪(b j:Space d),x⟫) := by
    funext x; ext j
    simp only [Function.comp_apply,WithLp.ofLp_toLp,OrthonormalBasis.repr_apply_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold gaussian
  rw [he,← Measure.map_map (PiLp.continuous_toLp 2 _).measurable (by fun_prop),
    Analytic.map_orthonormal_stdGaussian _ ho,map_pi_eq_stdGaussian]

lemma exists_span_cone {z : Fin k → Space d} (hsum : ∑ j,z j=0)
    (hneg : Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hzi:z i≠0)
    (hdim : k-1=n+1) (hcen : centroid (closedCell z i)=z i) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (closedCell z i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖z i‖ := by
  let V := Submodule.span ℝ (range z)
  let zv : Fin k → V := fun j=>⟨z j,Submodule.subset_span (mem_range_self j)⟩
  have hnorm : 0<‖z i‖ := norm_pos_iff.mpr hzi
  let e : V := ‖z i‖⁻¹ • zv i
  have he : ‖e‖=1 := by simp [e,zv,norm_smul,hnorm.ne']
  obtain ⟨b,hb⟩ := exists_basis_zero
    (show Module.finrank ℝ V=n+1 by rw [Gram.finrank_span z hneg hsum i,Fintype.card_fin,hdim]) e he
  let T : Space d → Space (n+1) := fun x=> b.repr (V.orthogonalProjectionOnto x)
  let w : Fin k → Space (n+1) := fun j=>b.repr (zv j)
  let K := closedCell w i
  have hT : Continuous T := b.repr.continuous.comp V.orthogonalProjectionOnto.continuous
  have hm : (gaussian d).map T=gaussian (n+1) := coordinates_law b
  have hs : ∀ j x, ⟪w j,T x⟫=⟪z j,x⟫ := by
    intro j x
    dsimp [w,T]
    rw [b.repr.inner_map_map,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hp : T ⁻¹' K=closedCell z i := by
    ext x
    simp only [K,closedCell,mem_preimage,mem_ofPred_eq,hs]
  refine ⟨K,measurableSet_closedCell w i,closedCell_cone w i,?_,?_⟩
  · rw [← hm,measureReal_def,Measure.map_apply hT.measurable (measurableSet_closedCell w i),hp]
    rfl
  have ht0 : ∀ x, T x 0=‖z i‖⁻¹*⟪z i,x⟫ := by
    intro x
    dsimp [T]
    rw [b.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,hb]
    simp only [e,Submodule.coe_smul,zv,real_inner_smul_left]
  have hi := integral_map (μ:=gaussian d) (φ:=T)
    (f:=K.indicator (fun x:Space (n+1)=>x 0)) hT.aemeasurable
    (((by fun_prop : Continuous (fun x:Space (n+1)=>x 0)).stronglyMeasurable.indicator
      (measurableSet_closedCell w i)).aestronglyMeasurable)
  rw [hm] at hi
  rw [hi]
  have heq : (fun x => K.indicator (fun x:Space (n+1)=>x 0) (T x)) =
      (closedCell z i).indicator (fun x=>‖z i‖⁻¹*⟪z i,x⟫) := by
    funext x
    have hh : T x∈K ↔ x∈closedCell z i := Set.ext_iff.mp hp x
    by_cases hx : x∈closedCell z i
    · simp only [indicator_of_mem hx,indicator_of_mem (hh.mpr hx),ht0]
    · simp only [indicator_of_notMem hx,indicator_of_notMem (mt hh.mp hx)]
  rw [heq,integral_indicator (measurableSet_closedCell z i),integral_const_mul]
  have hinner : (∫ x in closedCell z i, ⟪z i,x⟫ ∂gaussian d) =
      ⟪z i,centroid (closedCell z i)⟫ := Pair.integral_inner_eq_inner_integral _ _
  rw [hinner]
  change ‖z i‖⁻¹*⟪z i,centroid (closedCell z i)⟫=‖z i‖
  rw [hcen,real_inner_self_eq_norm_sq]
  field_simp

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open Coords


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.exists_span_cone := @_root_.OAI.GaussianPropeller.Reduction.exists_span_cone
