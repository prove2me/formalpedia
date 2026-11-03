-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourcePairEnd_rotation_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:30:49.406877+00:00
-- url     : https://prove2.me/submissions/65281a10-2295-45e2-8aff-f0ddc606f396

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L013
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_exteriorFamily_contraction_rotation_s50
import Theorems.Thm_OAI_Laughlin_Fock_pairCreate_pair_adjoint_s50
import Theorems.Thm_OAI_Laughlin_Rotation_physicalPairInclusion_SU2_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TensorAction
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_compactSpace _root_.OAI.Laughlin.Rotation.sourceSU2_continuousInv _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace _root_.OAI.Laughlin.Rotation.sourceSU2_topologicalGroup
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

theorem create_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    exteriorRotation Q g (create i x) =
      ∑ j, sourceSpinRepresentation Q g j i • create j (exteriorRotation Q g x) := by
  change ExteriorAlgebra.map (orbitalRotation Q g) (ExteriorAlgebra.ι ℂ (mode i)*x) = _
  rw [map_mul,ExteriorAlgebra.map_apply_ι,orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  have he : orbitalRotation Q g (mode i) j = sourceSpinRepresentation Q g j i := by
    simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [he]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix Kronecker

theorem exteriorRotation_pair_basis (Q : ℕ) (g : SourceSU2) (i j : Fin (Q+1)) :
    exteriorRotation Q g (create i (create j (1 : Space Q))) =
      ∑ k : Spin.SpinIndex Q Q, (sourceSpinRepresentation Q g k.1 i * sourceSpinRepresentation Q g k.2 j) •
        create k.1 (create k.2 (1 : Space Q)) := by
  rw [create_exteriorRotation,create_exteriorRotation]
  simp only [map_one,map_sum,map_smul,Finset.smul_sum,smul_smul,Fintype.sum_prod_type]

theorem pairExterior_rotation (Q : ℕ) (g : SourceSU2) (v : Spin.SpinIndex Q Q → ℂ) :
    exteriorRotation Q g (pairExterior Q v) =
      pairExterior Q ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ v) := by
  simp only [pairExterior,map_sum,map_smul,exteriorRotation_pair_basis,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairExterior_sum {I : Type*} [Fintype I] (Q : ℕ) (v : I → Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (∑ a, v a) = ∑ a, pairExterior Q (v a) := by
  simp only [pairExterior,Finset.sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem pairExterior_smul (Q : ℕ) (c : ℂ) (v : Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (c • v) = c • pairExterior Q v := by
  simp only [pairExterior,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem sourcePairVector_pairExterior (Q p : ℕ) :
    sourcePairVector Q p = (Real.sqrt 2 : ℂ)⁻¹ •
      pairExterior Q (fun i => (pairCoefficient Q p i.1 i.2 : ℂ)) := by
  simp only [sourcePairVector,pairExterior,Fintype.sum_prod_type,Finset.smul_sum,smul_smul,
    div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,mul_comm]

theorem sourcePairVector_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) :
    exteriorRotation Q g (sourcePairVector Q p.val) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p • sourcePairVector Q q.val := by
  have hc : ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
      (fun i => (pairCoefficient Q p.val i.1 i.2 : ℂ))) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p •
        (fun i : Spin.SpinIndex Q Q => (pairCoefficient Q q.val i.1 i.2 : ℂ)) := by
    funext i
    have h := congrFun (congrFun (physicalPairInclusion_SU2_s50 Q hQ g) i) p
    simpa only [physicalPairInclusion,Spin.pairInclusion,Matrix.map_apply,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using h
  rw [sourcePairVector_pairExterior,map_smul,pairExterior_rotation,hc,pairExterior_sum]
  simp only [pairExterior_smul,Finset.smul_sum,sourcePairVector_pairExterior]
  apply Finset.sum_congr rfl
  intro q hq
  exact smul_comm _ _ _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourcePairCreateEnd_mul (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = sourcePairVector Q p*x := by
  simp only [sourcePairCreateEnd,pairCreateEnd,sourcePairVector,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,Finset.sum_mul,smul_mul_assoc,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*x) =
    (ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*1))*x
  simp only [mul_one,mul_assoc]

theorem sourcePairVector_adjoint (Q p : ℕ) (x y : Space Q) :
    occupationInner Q (sourcePairVector Q p*x) y = occupationInner Q x (sourcePairEnd Q p y) := by
  rw [← sourcePairCreateEnd_mul]
  exact pairCreate_pair_adjoint_s50 Q _ x y

theorem sourcePairEnd_rotation_s50_oai (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) (x : Space Q) :
    sourcePairEnd Q p.val (exteriorRotation Q g x) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g p q •
        exteriorRotation Q g (sourcePairEnd Q q.val x) := by
  exact exteriorFamily_contraction_rotation_s50 Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2))
    (fun p : Fin (2*Q-2+1) => sourcePairVector Q p.val)
    (fun p => sourcePairEnd Q p.val)
    (fun p => sourcePairVector_adjoint Q p.val)
    (fun g p => sourcePairVector_rotation Q hQ g p) g p x

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourcePairEnd_rotation_s50_oai := @OAI.Laughlin.Fock.sourcePairEnd_rotation_s50_oai
