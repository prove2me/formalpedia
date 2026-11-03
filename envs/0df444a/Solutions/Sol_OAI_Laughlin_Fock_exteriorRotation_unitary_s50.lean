-- Prove2me | solution 1 for OAI.Laughlin.Fock.exteriorRotation_unitary_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:16:04.65567+00:00
-- url     : https://prove2.me/submissions/8f14dccc-404f-4410-a4f3-50279f780b77

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_occupationInner_scalar_wedge_zero_s50
import Theorems.Thm_OAI_Laughlin_Fock_vectorCreate_adjoint_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

end Laughlin.Fock

end OAI
end

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_VectorAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbitalDual_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) :
    (orbitalDual Q (orbitalRotation Q g v)).comp (orbitalRotation Q g) = orbitalDual Q v := by
  apply LinearMap.ext
  intro w
  simp only [orbitalDual,LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  change star (sourceSpinRepresentation Q g *ᵥ v) ⬝ᵥ (sourceSpinRepresentation Q g *ᵥ w) = star v ⬝ᵥ w
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [hu,Matrix.vecMul_one]

theorem vectorAnnihilate_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q (orbitalRotation Q g v) (exteriorRotation Q g x) =
      exteriorRotation Q g (vectorAnnihilate Q v x) := by
  unfold vectorAnnihilate exteriorRotation
  rw [contraction_map,orbitalDual_rotation]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_left (Q : ℕ) (x y z : Space Q) :
    occupationInner Q (x+y) z = occupationInner Q x z+occupationInner Q y z := by
  simp [occupationInner,add_mul,Finset.sum_add_distrib]

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

theorem exteriorRotation_ι_mul (Q : ℕ) (g : SourceSU2) (v : Orbital Q) (x : Space Q) :
    exteriorRotation Q g (ExteriorAlgebra.ι ℂ v*x) =
      ExteriorAlgebra.ι ℂ (orbitalRotation Q g v)*exteriorRotation Q g x := by
  simp [exteriorRotation]

theorem occupationInner_scalar_rotation (Q : ℕ) (g : SourceSU2) (r : ℂ) (y : Space Q) :
    occupationInner Q (algebraMap ℂ (Space Q) r) (exteriorRotation Q g y) =
      occupationInner Q (algebraMap ℂ (Space Q) r) y := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap s => simp
  | add x y hx hy => simp only [map_add,occupationInner_add_right,hx,hy]
  | ι_mul x v hx => rw [exteriorRotation_ι_mul,occupationInner_scalar_wedge_zero_s50,occupationInner_scalar_wedge_zero_s50]

theorem exteriorRotation_unitary_s50_oai (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g x) (exteriorRotation Q g y) = occupationInner Q x y := by
  revert y
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp only [AlgHom.commutes]
    exact occupationInner_scalar_rotation Q g r y
  | add x z hx hz =>
    intro y
    simp only [map_add,occupationInner_add_left,hx,hz]
  | ι_mul x v hx =>
    intro y
    rw [exteriorRotation_ι_mul,vectorCreate_adjoint_s50,vectorAnnihilate_rotation,hx,vectorCreate_adjoint_s50]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.exteriorRotation_unitary_s50_oai := @OAI.Laughlin.Fock.exteriorRotation_unitary_s50_oai
