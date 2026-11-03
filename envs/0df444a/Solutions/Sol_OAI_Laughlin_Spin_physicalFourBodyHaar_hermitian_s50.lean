-- Prove2me | solution 1 for OAI.Laughlin.Spin.physicalFourBodyHaar_hermitian_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:51.546196+00:00
-- url     : https://prove2.me/submissions/5898a503-f410-4889-b269-0de201c65293

import Mathlib
import Definitions.Def_OAIQ050L024

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

theorem fourBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    fourBodySpinRepresentation Q g⁻¹ = (fourBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,wedgePairRepresentation_inv]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Hermitian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem list_double_sum_swap {I A : Type*} [AddCommMonoid A]
    (l k : List I) (f : I → I → A) :
    (l.map (fun i => (k.map (f i)).sum)).sum =
      (k.map (fun j => (l.map (fun i => f i j)).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,ih,List.sum_map_add]

theorem fourBodyTermMatrix_transpose (Q t : ℕ) (e f : ℕ × ℕ × ℤ) :
    (fourBodyTermMatrix Q t e f)ᵀ = fourBodyTermMatrix Q t f e := by
  ext i j
  simp only [fourBodyTermMatrix,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,realOuter]
  ring

theorem physicalFourBodyMatrix_transpose (Q : ℕ) :
    (physicalFourBodyMatrix Q)ᵀ = physicalFourBodyMatrix Q := by
  unfold physicalFourBodyMatrix
  simp only [Matrix.transpose_list_sum,List.map_map,Function.comp_def,fourBodyTermMatrix_transpose]
  congr 1
  apply List.map_congr_left
  intro row hrow
  exact list_double_sum_swap row.2.2 row.2.2 (fun e f => fourBodyTermMatrix Q row.1 f e)

theorem physicalFourBodyMatrix_hermitian (Q : ℕ) :
    ((physicalFourBodyMatrix Q).map Complex.ofReal)ᴴ = (physicalFourBodyMatrix Q).map Complex.ofReal := by
  rw [real_matrix_adjoint,physicalFourBodyMatrix_transpose]

theorem physicalFourBodyHaar_hermitian_s50_oai (Q : ℕ) :
    (matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)))ᴴ =
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) := by
  have he (g : SourceSU2) :
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g)ᴴ =
      conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g := by
    simp only [conjugateOrbit,Matrix.conjTranspose_mul,fourBodySpinRepresentation_inv,
      Matrix.conjTranspose_conjTranspose,physicalFourBodyMatrix_hermitian,Matrix.mul_assoc]
  ext i j
  change star (∫ g, conjugateOrbit (fourBodySpinRepresentation Q)
    ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i ∂sourceHaar) = _
  calc
    _ = ∫ g, star (conjugateOrbit (fourBodySpinRepresentation Q)
      ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i) ∂sourceHaar := integral_conj.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact congrFun (congrFun (he g) i) j

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physicalFourBodyHaar_hermitian_s50_oai := @OAI.Laughlin.Spin.physicalFourBodyHaar_hermitian_s50_oai
