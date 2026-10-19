-- Prove2me | solution 1 for OAI.EuclideanRamsey.realCriterion_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:32:05.481155+00:00
-- url     : https://prove2.me/submissions/3bac1098-054d-4638-b873-020f87da68db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean:L227-L258
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.realCriterion_lattice. The node keeps its source
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

variable (φ : ℝ →ₗ[F] F)

attribute [local instance] OAI.EuclideanRamsey.tensorRing
end Descent

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorPresentation ----
-- TensorProduct.inductionOn (the Lean 4.34 two-case eliminator) is already backported in the imported
-- module OAI.Combinatorics.EuclideanRamsey.TensorDescent.

namespace OAI

universe uVector

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

open scoped TensorProduct RealInnerProductSpace
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct BigOperators

lemma arrayEvaluation_affineArray {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray T) = TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) T := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    simp only [arrayEvaluation,LinearMap.coe_mk,AddHom.coe_mk,affineArray_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,TensorProduct.map_tmul,
      rowEvaluation,TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  | add x y hx hy => simp [hx,hy]

lemma affineArray_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) (α β : Option (Fin d)) :
    affineArray (TensorProduct.comm ℚ _ _ T) α β = TensorProduct.comm ℚ ℝ ℝ (affineArray T β α) := by
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]

lemma arrayEvaluation_comm {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray (TensorProduct.comm ℚ _ _ T)) =
      TensorProduct.comm ℚ ℝ ℝ (arrayEvaluation a i (affineArray T)) := by
  simp only [arrayEvaluation_affineArray]
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]

lemma spatialMultiply_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) :
    spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ T)) =
      (spatialMultiply (affineArray T)).transpose := by
  ext α β
  change Algebra.TensorProduct.lmul' ℚ (affineArray (TensorProduct.comm ℚ _ _ T) (some α) (some β)) =
    Algebra.TensorProduct.lmul' ℚ (affineArray T (some β) (some α))
  rw [affineArray_comm]
  generalize affineArray T (some β) (some α) = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx,hy]

end EuclideanRamsey

open scoped TensorProduct BigOperators
namespace EuclideanRamsey

theorem exists_symmetric_tensor_presentation {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (T : W ⊗[ℚ] W) :
    ∃ (k : ℕ) (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ), C.IsSymm ∧
      (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
        (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
  classical
  obtain ⟨S,hS⟩ := TensorProduct.exists_finset T
  let w : (↥S ⊕ ↥S) → W := Sum.elim (fun z : ↥S => z.val.1) (fun z : ↥S => z.val.2)
  let C : (↥S ⊕ ↥S) → (↥S ⊕ ↥S) → ℚ := fun j l => match j,l with
    | .inl i,.inr j => if i=j then 1/2 else 0
    | .inr i,.inl j => if i=j then 1/2 else 0
    | _,_ => 0
  have hC : Matrix.IsSymm C := by
    ext j l
    change C l j = C j l
    cases j <;> cases l <;> dsimp only [C]
    all_goals simp only [eq_comm]
  have hs : (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
      (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
    simp only [Fintype.sum_sum_type,C,w,zero_smul,Finset.sum_const_zero,zero_add,add_zero,
      ite_smul,Sum.elim_inl,Sum.elim_inr,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [hS]
    simp only [map_sum,TensorProduct.comm_tmul,smul_add,Finset.smul_sum]
    rw [Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.1 ⊗ₜ[ℚ] z.2)),
      Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.2 ⊗ₜ[ℚ] z.1))]
  let e := Fintype.equivFin (↥S ⊕ ↥S)
  refine ⟨Fintype.card (↥S ⊕ ↥S), fun j => w (e.symm j), fun j l => C (e.symm j) (e.symm l),?_,?_⟩
  · ext j l
    exact congrFun (congrFun hC (e.symm j)) (e.symm l)
  · change (∑ j,∑ l,C (e.symm j) (e.symm l) • (w (e.symm j) ⊗ₜ[ℚ] w (e.symm l))) = _
    calc
      _ = ∑ j : Fin (Fintype.card (↥S ⊕ ↥S)),∑ l : ↥S ⊕ ↥S,
          C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Equiv.sum_comp e.symm (fun l => C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l))
      _ = _ := (Equiv.sum_comp e.symm (fun j => ∑ l,C j l • (w j ⊗ₜ[ℚ] w l))).trans hs

end EuclideanRamsey

open scoped TensorProduct
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct

lemma rational_lattice_kernel {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ) :
    latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) = f.ker := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨γ,hγ,rfl⟩
    exact hγ
  · intro x hx
    let A : Matrix Unit (Fin k) ℚ := fun _ j => x j
    let γ : Lattice k := fun j => A.num () j
    have hden : (A.den:ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    have he : (rationalize γ : RationalSpace k) = (A.den:ℚ) • x := by
      ext j
      have hm := A.num_div_den () j
      change (A.num () j:ℚ)/(A.den:ℚ) = x j at hm
      change (A.num () j:ℚ) = (A.den:ℚ)*x j
      exact ((div_eq_iff hden).mp hm).trans (mul_comm _ _)
    have hγ : γ ∈ AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize) := by
      change f (rationalize γ) = 0
      rw [he,map_smul]
      exact smul_eq_zero_of_right _ hx
    have hm : rationalize γ ∈ latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) :=
      Submodule.subset_span ⟨γ,hγ,rfl⟩
    have := Submodule.smul_mem (latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)))
      (A.den:ℚ)⁻¹ hm
    simpa only [he,smul_smul,inv_mul_cancel₀ hden,one_smul] using this

lemma quotientTensor_zero_of_evaluation {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ)
    (T : RationalSpace k ⊗[ℚ] RationalSpace k) (hT : TensorProduct.map f f T = 0) :
    quotientTensor (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) T = 0 := by
  classical
  change TensorProduct.map _ _ T = 0
  rw [rational_lattice_kernel]
  let e := f.quotKerEquivRange
  let j : (RationalSpace k ⧸ f.ker) →ₗ[ℚ] ℝ := f.range.subtype.comp e.toLinearMap
  have hj : Function.Injective j := f.range.subtype_injective.comp e.injective
  obtain ⟨r,hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hpre : j.comp f.ker.mkQ = f := by
    ext x
    rfl
  have htmp : TensorProduct.map j j (TensorProduct.map f.ker.mkQ f.ker.mkQ T) = 0 := by
    rw [← LinearMap.comp_apply,← TensorProduct.map_comp,hpre,hT]
  have hback := congrArg (TensorProduct.map r r) htmp
  simpa only [map_zero,← LinearMap.comp_apply,← TensorProduct.map_comp,← LinearMap.comp_assoc,hr,LinearMap.id_comp,TensorProduct.map_id,
    LinearMap.id_apply] using hback

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

lemma matrixTensor_map_family {k : ℕ} {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ) :
    TensorProduct.map (Fintype.linearCombination ℚ w) (Fintype.linearCombination ℚ w) (matrixTensor C) =
      ∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l) := by
  simp [matrixTensor,Fintype.linearCombination_apply,TensorProduct.map_tmul]

lemma spatialMultiply_family {k d : ℕ} (w : Fin k → AffineVector d)
    (C : Matrix (Fin k) (Fin k) ℚ) :
    spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) =
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose := by
  ext α β
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,spatialMultiply,
    LinearMap.coe_mk]
  change (∑ j, ∑ l, (C j l:ℝ)*(w j (some α)*w l (some β))) = _
  change _ = ∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realCriterion_lattice {s d : ℕ} (a : Fin s → Space d) (hd : 1 ≤ d)
    (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      1 ≤ k ∧ C.IsSymm ∧
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ i,quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let T : AffineVector d ⊗[ℚ] AffineVector d := affineArray.symm P
  have hT : affineArray T = P := affineArray.apply_symm_apply P
  obtain ⟨k,w,C,hC,hrep⟩ := exists_symmetric_tensor_presentation T
  have hs : spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
    rw [hrep,map_smul,map_add,map_smul,map_add,spatialMultiply_comm,hT,hG]
    ext α β
    simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hh : α = β <;> norm_num [hh,eq_comm,Rat.smul_def]
  have hU := (spatialMultiply_family w C).symm.trans hs
  have hk : 1 ≤ k := by
    by_contra hh
    have hk : k = 0 := by omega
    subst k
    have he := congrFun (congrFun hU ⟨0,by omega⟩) ⟨0,by omega⟩
    simp [Matrix.mul_apply] at he
  refine ⟨k,w,C,hk,hC,hU,?_⟩
  intro i
  apply quotientTensor_zero_of_evaluation
  rw [TensorProduct.map_comp,LinearMap.comp_apply,matrixTensor_map_family]
  rw [← arrayEvaluation_affineArray,hrep,map_smul,map_add,map_smul,map_add,
    arrayEvaluation_comm,hT,hP,map_zero,add_zero,smul_zero]

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
open scoped TensorProduct RealInnerProductSpace
open scoped TensorProduct BigOperators
open scoped TensorProduct
open scoped TensorProduct BigOperators


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.realCriterion_lattice := @_root_.OAI.EuclideanRamsey.realCriterion_lattice
