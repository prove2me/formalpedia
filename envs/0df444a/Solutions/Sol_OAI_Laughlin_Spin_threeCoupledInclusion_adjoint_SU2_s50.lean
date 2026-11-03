-- Prove2me | solution 1 for OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:03:35.63076+00:00
-- url     : https://prove2.me/submissions/187f1e14-1990-4806-a245-fed527bf864a

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Specializations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem genericUnitDescendant_threeBody (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    genericUnitDescendant (2*Q-2) Q z (by omega) hz n =
      normalizedCoupledDescendant Q z hQ hz n := by rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem threeCoupledInclusion_SU2 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : Rotation.SourceSU2) :
    (Rotation.sourceSpinRepresentation (2*Q-2) g ⊗ₖ Rotation.sourceSpinRepresentation Q g)*
      threeCoupledInclusion Q hQ z =
      threeCoupledInclusion Q hQ z*Rotation.sourceSpinRepresentation (coupledWeight Q z.val) g := by
  have hw : genericCoupledWeight (2*Q-2) Q z.val = coupledWeight Q z.val := by
    unfold genericCoupledWeight coupledWeight
    omega
  have h := genericCoupledInclusion_SU2 (2*Q-2) Q z.val (by omega) (by omega) g
  unfold genericCoupledInclusion at h
  simp only [genericUnitDescendant_threeBody Q z.val _ hQ] at h
  rw [hw] at h
  exact h

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HaarBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker
open Rotation MeasureTheory

theorem threeBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    threeBodySpinRepresentation Q g⁻¹=(threeBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,sourceSpinRepresentation_inv]

theorem threeCoupledInclusion_adjoint_SU2_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : SourceSU2) :
    (threeCoupledInclusion Q hQ z)ᴴ * threeBodySpinRepresentation Q g =
      sourceSpinRepresentation (coupledWeight Q z.val) g * (threeCoupledInclusion Q hQ z)ᴴ := by
  have h : threeBodySpinRepresentation Q g⁻¹ * threeCoupledInclusion Q hQ z =
    threeCoupledInclusion Q hQ z * sourceSpinRepresentation (coupledWeight Q z.val) g⁻¹ :=
    threeCoupledInclusion_SU2 Q hQ z g⁻¹
  have ht := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul,threeBodySpinRepresentation_inv,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using ht

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50_oai := @OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50_oai
