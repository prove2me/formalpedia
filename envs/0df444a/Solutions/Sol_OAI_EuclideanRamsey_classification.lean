-- Prove2me | solution 1 for OAI.EuclideanRamsey.classification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:19:42.718956+00:00
-- url     : https://prove2.me/submissions/85c989a3-a457-43d1-816c-79c777f34785

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Main.lean:L69-L73
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EuclideanRamsey.classification.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EuclideanRamsey_classification) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths
import Theorems.Thm_OAI_EuclideanRamsey_fieldCriterion_realCriterion
import Theorems.Thm_OAI_EuclideanRamsey_finite_coloring_compactness
import Theorems.Thm_OAI_EuclideanRamsey_paths_monochromatic
import Theorems.Thm_OAI_EuclideanRamsey_permutation_equal_endpoints
import Theorems.Thm_OAI_EuclideanRamsey_ramsey_realCriterion
import Theorems.Thm_OAI_EuclideanRamsey_realCriterion_two_scale

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorDescent ----
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

section Descent
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)

lemma tensorCoordinates_tmul (x y : ℝ) (k : ι × ι) :
    tensorCoordinates F b (x ⊗ₜ[ℚ] y) k = b.repr x k.1 ⊗ₜ[ℚ] b.repr y k.2 := by
  rcases k with ⟨l, m⟩
  simp [tensorCoordinates]

lemma tensorCoordinates_symm_single_tmul (x y : F) (k : ι × ι) :
    (tensorCoordinates F b).symm (Finsupp.single k (x ⊗ₜ[ℚ] y)) =
      (x • b k.1) ⊗ₜ[ℚ] (y • b k.2) := by
  simp [tensorCoordinates, finsuppTensorFinsupp_symm_single]

lemma repr_mul (x : F) (u : ℝ) :
    b.repr ((x : ℝ) * u) = x • b.repr u := by
  simpa only [Algebra.smul_def, IntermediateField.algebraMap_apply] using b.repr.map_smul x u

lemma tensorCoordinates_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorCoordinates F b (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] y) • tensorCoordinates F b T := by
  ext k
  induction T using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      tensorCoordinates_tmul, Finsupp.smul_apply, smul_eq_mul]
    rw [repr_mul, mul_comm v (y : ℝ), repr_mul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
  | add U V hU hV =>
    simpa only [mul_add, add_mul, map_add, Finsupp.add_apply, smul_add,
      Finsupp.smul_apply] using congrArg₂ (· + ·) hU hV

variable (φ : ℝ →ₗ[F] F)

attribute [local instance] OAI.EuclideanRamsey.tensorRing
lemma tensorDescent_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorDescent F b φ (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] (1 : F)) * tensorDescent F b φ T * ((1 : F) ⊗ₜ[ℚ] y) := by
  change coefficientTrace F b φ (tensorCoordinates F b _) = _
  rw [tensorCoordinates_sandwich, map_smul]
  change (x ⊗ₜ[ℚ] y) * tensorDescent F b φ T = _
  rw [mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma coefficientTrace_multiply (z : ι × ι →₀ (F ⊗[ℚ] F)) :
    Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ z) =
      φ (Algebra.TensorProduct.lmul' ℚ ((tensorCoordinates F b).symm z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single k z =>
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [Finsupp.single_add, map_add, hz, hw]
    | tmul x y =>
      simp only [coefficientTrace, Finsupp.linearCombination_single, smul_eq_mul,
        map_mul, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
        tensorCoordinates_symm_single_tmul]
      have hmul : (x • b k.1) * (y • b k.2) = (x * y) • (b k.1 * b k.2) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [hmul, map_smul, smul_eq_mul]

lemma tensorDescent_multiply (T : ℝ ⊗[ℚ] ℝ) :
    Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ T) =
      φ (Algebra.TensorProduct.lmul' ℚ T) := by
  change Algebra.TensorProduct.lmul' ℚ (coefficientTrace F b φ (tensorCoordinates F b T)) = _
  rw [coefficientTrace_multiply, LinearEquiv.symm_apply_apply]

end Descent

theorem realCriterion_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : RealCriterion a) : FieldCriterion a := by
  classical
  let F := coordinateField a
  let b := Module.Free.chooseBasis F ℝ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : ℝ) ≠ 0)
  let δ := tensorDescent F b φ
  obtain ⟨P, he, hm⟩ := h
  refine ⟨fun α β => δ (P α β), ?_, ?_⟩
  · intro i
    have haug (α : Option (Fin d)) : ((augmented a i α : F) : ℝ) = realAugmented a i α := by
      cases α <;> rfl
    have hd := congrArg δ (he i)
    change δ (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
      ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = δ 0 at hd
    simp only [map_sum, map_zero] at hd
    simpa only [δ, ← haug, tensorDescent_sandwich] using hd
  · intro α β
    change Algebra.TensorProduct.lmul' ℚ (tensorDescent F b φ (P (some α) (some β))) = _
    rw [tensorDescent_multiply]
    have hab := congrFun (congrFun hm α) β
    change Algebra.TensorProduct.lmul' ℚ (P (some α) (some β)) = _ at hab
    rw [hab]
    by_cases heq : α = β
    · simp only [Matrix.one_apply, heq, ite_true, hφ]
    · simp only [Matrix.one_apply, heq, ite_false, map_zero]

theorem ramsey_fieldCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : FieldCriterion a :=
  realCriterion_fieldCriterion a (ramsey_realCriterion a hs hspan hR)

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Main ----
namespace OAI

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
open Filter
open Set

namespace EuclideanRamsey

theorem fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by
  have hreal := fieldCriterion_realCriterion a h
  have hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,
      Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ) := by
    intro n hn
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hs' : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
    let η : ℝ := 1/(4*n)
    let δ : ℝ := 1/(4*n*s)
    have hη : 0<η := by dsimp [η]; positivity
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨ℓ,hℓ,f,g,hf,hg,hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η hη
    have hq : 0<η/(1+η) := div_pos hη (by linarith)
    obtain ⟨w,lmb,μ,hp,hm,hlmb,hμ,hr⟩ :=
      permutation_equal_endpoints a ha f g (η/(1+η)) δ hq hδ hf hg hperm
    refine ⟨w,lmb,μ,hp,hm,hlmb,lt_of_le_of_lt hr ?_⟩
    have hq' : η/(1+η)<η := (div_lt_iff₀ (by linarith : 0<1+η)).mpr (by nlinarith)
    have he : η+(s:ℝ)*δ=1/(2*n) := by
      dsimp [η,δ]
      field_simp
      ring
    have hhalf : (1:ℝ)/(2*n)<1/n := by
      apply one_div_lt_one_div_of_lt hn'
      nlinarith
    rw [← he] at hhalf
    linarith
  intro r hr
  obtain ⟨D,hD,hmono⟩ := finite_coloring_compactness
    (fun i => FiniteEuclidean.embed d (a i)) r
    (fun c => paths_monochromatic _ hpaths c)
  refine ⟨D,hD,?_⟩
  intro c
  obtain ⟨b,hb,k,hk⟩ := hmono c
  refine ⟨b,?_,k,hk⟩
  intro i j
  rw [dist_eq_norm,dist_eq_norm,hb,← map_sub,LinearIsometry.norm_map]

theorem classification {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    Ramsey a ↔ FieldCriterion a :=
  ⟨ramsey_fieldCriterion a (by omega) hspan,fieldCriterion_ramsey a hs hd ha⟩
end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI

-- ---- mission target ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace OAI
namespace EuclideanRamsey
theorem _root_.solution {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (hspan : affineSpan ℝ (Set.range a) = ⊤) :
    Ramsey a ↔ FieldCriterion a := by
  first
    | exact OAI.EuclideanRamsey.classification a hs hd ha hspan
    | exact OAI.EuclideanRamsey.classification
    | (apply OAI.EuclideanRamsey.classification <;> assumption)
    | (intros; apply OAI.EuclideanRamsey.classification <;> assumption)
end EuclideanRamsey
end OAI
