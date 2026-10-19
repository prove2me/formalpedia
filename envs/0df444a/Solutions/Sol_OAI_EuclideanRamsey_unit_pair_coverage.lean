-- Prove2me | solution 1 for OAI.EuclideanRamsey.unit_pair_coverage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:47:17.838817+00:00
-- url     : https://prove2.me/submissions/e7aa520b-acb8-404c-827e-4de0a4738c02

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean:L142-L164
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.unit_pair_coverage. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Theorems.Thm_OAI_EuclideanRamsey_augmentation_kernel_le

-- ---- from OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean ----
-- Lean 4.34 name of Finsupp.mapDomain_apply (same arguments) in Mathlib 0df444a.
namespace OAI

universe uValue

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped BigOperators RealInnerProductSpace
namespace EuclideanRamsey

namespace FiniteEuclidean
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

lemma norm_unit (n : ℕ) : ‖unit n‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_sq]
  simp [unit,coords]
lemma inner_unit (x : FiniteEuclidean) (n : ℕ) : ⟪x,unit n⟫=coords x n := by
  rw [real_inner_comm]
  change product (unit n) x=coords x n
  simp [product,unit,coords]

lemma common_vertex (r : ℝ) (hr : 0 < r) (x y : FiniteEuclidean) (hxy : ‖y-x‖≤2*r) :
    ∃ z : FiniteEuclidean,‖z-x‖=r ∧ ‖z-y‖=r := by
  classical
  let v := y-x
  obtain ⟨n,hn⟩ := (coords v).support.exists_notMem
  have hz : coords v n=0 := Finsupp.notMem_support_iff.mp hn
  let e := unit n
  have he : ‖e‖=1 := norm_unit n
  have hv : ⟪v,e⟫=0 := by simpa [e] using (inner_unit v n).trans hz
  let t := Real.sqrt (r^2-‖v‖^2/4)
  have ht0 : 0≤r^2-‖v‖^2/4 := by
    have hv0 := norm_nonneg v
    change ‖v‖≤2*r at hxy
    nlinarith [sq_nonneg (2*r-‖v‖)]
  have ht : t^2=r^2-‖v‖^2/4 := Real.sq_sqrt ht0
  refine ⟨x+(1/2:ℝ)•v+t•e,?_,?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-x=(1/2:ℝ)•v+t•e := by abel
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,sq_abs,mul_pow]
    nlinarith
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-y=(-(1/2):ℝ)•v+t•e := by
      have : y=x+v := by dsimp [v]; abel
      rw [this]
      module
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith

lemma unit_distance_constant {Y : Type uValue} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y,‖x-y‖=r → f x=f y) (x y : FiniteEuclidean) :
    f x=f y := by
  have hsmall (x y : FiniteEuclidean) (h : ‖y-x‖≤2*r) : f x=f y := by
    obtain ⟨z,hz,hz'⟩ := common_vertex r hr x y h
    exact (hf z x hz).symm.trans (hf z y hz')
  have hl : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro x
    refine ⟨Metric.ball x (2*r),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro y hy
    exact (hsmall x y (by exact (show ‖y-x‖<2*r by simpa only [Metric.mem_ball,dist_eq_norm] using hy).le)).symm
  exact hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
end FiniteEuclidean
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathWords ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex}

lemma pairLeft_edge (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j)
    (x y : FiniteEuclidean) (hxy : ‖x-y‖=‖a i-a j‖) :
    FreeGroup.of x*(FreeGroup.of y)⁻¹∈pairLeft a i j hij := by
  obtain ⟨b,hbi,hbj,hb⟩ := extend_pair_E a i j x y (by
    simpa only [norm_sub_rev y x,norm_sub_rev (a j) (a i)] using hxy)
  have hcopy : (FreeGroup.of x,FreeGroup.of y)∈pairGroup a i j hij := by
    refine ⟨(fun k => FreeGroup.of (b k)),⟨1,UnitWords.copy b hb⟩,?_⟩
    exact Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)
  have h := (pairGroup a i j hij).mul_mem hcopy (pairGroup_diag a i j hij (FreeGroup.of y)⁻¹)
  simpa [pairLeft,MonoidHom.inl_apply] using h

lemma unit_pair_coverage (a : ι → FiniteEuclidean) (ha : Function.Injective a) :
    PairCoverage (unitGraded a).monoid (AugKernel FiniteEuclidean) := by
  intro i j hij g hg h hh
  have hr : 0<‖a i-a j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hij (ha he)))
  have hle : AugKernel FiniteEuclidean≤pairLeft a i j hij := by
    apply augmentation_kernel_le 0
    intro x y
    apply FiniteEuclidean.unit_distance_constant _ hr
      (fun z => (QuotientGroup.mk' (pairLeft a i j hij)) (FreeGroup.of z))
    intro x y hxy
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using pairLeft_edge a i j hij x y hxy
  have hleft : (g,1)∈pairGroup a i j hij := hle hg
  have hright : (1,h)∈pairGroup a i j hij := by
    have h := (pairGroup a i j hij).mul_mem (pairGroup_diag a i j hij h)
      (hle ((AugKernel FiniteEuclidean).inv_mem hh))
    simpa using h
  have hp := (pairGroup a i j hij).mul_mem hleft hright
  have hp' : (g,h)∈(unitGraded a).monoid.map (pairHom i j) := by
    change (g,h)∈pairGroup a i j hij
    simpa using hp
  obtain ⟨v,hv,hv'⟩ := hp'
  exact ⟨v,hv,congrArg Prod.fst hv',congrArg Prod.snd hv'⟩
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex}
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.unit_pair_coverage.{uIndex} := @_root_.OAI.EuclideanRamsey.unit_pair_coverage.{uIndex}
