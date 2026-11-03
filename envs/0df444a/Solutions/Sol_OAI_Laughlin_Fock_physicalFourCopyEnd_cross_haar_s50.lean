-- Prove2me | solution 1 for OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:03:58.472927+00:00
-- url     : https://prove2.me/submissions/ee01a6ba-bd00-4dc9-afbf-dd4e4b1ceff4

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Fock_contractionForm_haar_s50
import Theorems.Thm_OAI_Laughlin_Fock_physicalFourCopyEnd_column_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation_s50
import Theorems.Thm_OAI_Laughlin_Spin_fourBody_cross_orbit_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TensorAction
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceHaar_isHaar _root_.OAI.Laughlin.Rotation.sourceHaar_isProbability _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_compactSpace _root_.OAI.Laughlin.Rotation.sourceSU2_continuousInv _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace _root_.OAI.Laughlin.Rotation.sourceSU2_topologicalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem tensorMatrix_conjTranspose (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorMatrix N Aᴴ = (tensorMatrix N A)ᴴ := by
  ext a b
  simp [tensorMatrix,Matrix.conjTranspose_apply]

theorem tensorMatrix_unitary (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorMatrix N A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose,← tensorMatrix_conjTranspose,← tensorMatrix_mul]
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h,tensorMatrix_one]

 theorem sourceTensorRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceTensorRepresentation Q g ∈ Matrix.unitaryGroup (Fin Q → Fin 2) ℂ :=
  tensorMatrix_unitary Q g.val g.property.1

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Compact
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceHaar_isHaar _root_.OAI.Laughlin.Rotation.sourceHaar_isProbability _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceTensorRepresentation_continuous (Q : ℕ) (a b : Fin Q → Fin 2) :
    Continuous (fun g : SourceSU2 => sourceTensorRepresentation Q g a b) := by
  change Continuous (fun g : SourceSU2 => ∏ i, g.val (a i) (b i))
  exact continuous_finsetProd _ (fun i hi => (continuous_apply (b i)).comp
    ((continuous_apply (a i)).comp continuous_subtype_val))

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceSpinRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g ∈ Matrix.unitaryGroup (Fin (Q+1)) ℂ := by
  have he := congrArg (fun M => Mᴴ*M) (tensor_spin_intertwining Q g)
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceTensorRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  simp only [Matrix.conjTranspose_mul] at he
  have hleft : (sourceSpinMatrix Q g)ᴴ*(symmetricTensorInclusion Q)ᴴ*
      (symmetricTensorInclusion Q*sourceSpinMatrix Q g) = (sourceSpinMatrix Q g)ᴴ*sourceSpinMatrix Q g := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (symmetricTensorInclusion Q)ᴴ,
      symmetricTensorInclusion_isometry,Matrix.one_mul]
  have hright : (symmetricTensorInclusion Q)ᴴ*(sourceTensorRepresentation Q g)ᴴ*
      (sourceTensorRepresentation Q g*symmetricTensorInclusion Q) = 1 := by
    rw [Matrix.mul_assoc,← Matrix.mul_assoc (sourceTensorRepresentation Q g)ᴴ,hu,
      Matrix.one_mul,symmetricTensorInclusion_isometry]
  rw [hleft,hright] at he
  exact Matrix.mem_unitaryGroup_iff'.mpr he

 theorem sourceSpinRepresentation_continuous (Q : ℕ) (p q : Fin (Q+1)) :
    Continuous (fun g => sourceSpinRepresentation Q g p q) := by
  change Continuous (fun g : SourceSU2 =>
    ((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q) p q)
  simp only [Matrix.mul_apply]
  have h := sourceTensorRepresentation_continuous Q
  fun_prop

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Disjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix ComplexOrder

 theorem sourceSpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    sourceSpinRepresentation Q g⁻¹=(sourceSpinRepresentation Q g)ᴴ := by
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  calc
    _ = 1*sourceSpinRepresentation Q g⁻¹ := by rw [Matrix.one_mul]
    _ = ((sourceSpinRepresentation Q g)ᴴ*sourceSpinRepresentation Q g)*sourceSpinRepresentation Q g⁻¹ := by rw [hu]
    _ = _ := by rw [Matrix.mul_assoc,← map_mul,mul_inv_cancel,map_one,Matrix.mul_one]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem wedgePairRepresentation_continuous (Q : ℕ) (i j : WedgePairIndex Q) :
    Continuous (fun g => wedgePairRepresentation Q g i j) :=
  ((sourceSpinRepresentation_continuous Q i.val.1 j.val.1).mul
    (sourceSpinRepresentation_continuous Q i.val.2 j.val.2)).sub
    ((sourceSpinRepresentation_continuous Q i.val.1 j.val.2).mul
      (sourceSpinRepresentation_continuous Q i.val.2 j.val.1))

theorem wedgePairRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    wedgePairRepresentation Q g⁻¹ = (wedgePairRepresentation Q g)ᴴ := by
  ext i j
  simp only [wedgePairRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,wedgePairMatrix,
    Matrix.conjTranspose_apply,sourceSpinRepresentation_inv,star_sub,star_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem fourBodySpinRepresentation_continuous (Q : ℕ) (i j : FourWedgeIndex Q) :
    Continuous (fun g => fourBodySpinRepresentation Q g i j) :=
  (sourceSpinRepresentation_continuous (2*Q-2) i.1 j.1).mul
    (wedgePairRepresentation_continuous Q i.2 j.2)

theorem fourBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    fourBodySpinRepresentation Q g⁻¹ = (fourBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,wedgePairRepresentation_inv]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_smul {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (c : ℂ) (M : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (c • M) x = c * contractionForm Q minus M x := by
  simp only [contractionForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_outer_cross {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v w : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v w) x =
      occupationInner Q (∑ i, star (v i) • minus i x) (∑ j, star (w j) • minus j x) := by
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrix_cross_sandwich_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (V W : Matrix I J ℂ) (p : J) :
    V*diagonalUnit p*Wᴴ = complexOuter (fun i => V i p) (fun i => W i p) := by
  ext i j
  simp [diagonalUnit,Matrix.mul_apply,complexOuter,Matrix.conjTranspose_apply,ite_and]

theorem physicalFourCopyEnd_cross_haar_s50_oai (Q D : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, occupationInner Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x))
      (physicalFourCopyEnd Q (oddPairDeficit s) D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ s)ᴴ) x := by
  let M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ := diagonalUnit 0
  have h := contractionForm_haar_s50 Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (fourBodySpinRepresentation_continuous Q)
    (sourceFourFamilyEnd Q) (sourceFourFamilyEnd_rotation_s50 Q (by omega))
    (retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ) x
  rw [fourBody_cross_orbit_s50,contractionForm_smul] at h
  have ht : Matrix.trace M=1 := by simp [M,diagonalUnit,Matrix.trace,Matrix.diag]
  rw [ht] at h
  have he := matrix_cross_sandwich_single (retainedFourInclusion Q D hQ r)
    (retainedFourInclusion Q D hQ s) (0 : Fin (fourSpinWeight Q D+1))
  change retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ = _ at he
  simp_rw [he,contractionForm_outer_cross,physicalFourCopyEnd_column_s50] at h
  rw [h]
  have hd : ((4*Q-1-2*D : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50_oai := @OAI.Laughlin.Fock.physicalFourCopyEnd_cross_haar_s50_oai
