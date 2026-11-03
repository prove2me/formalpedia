-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:49:11.492522+00:00
-- url     : https://prove2.me/submissions/3b2080fe-86b4-4ddd-8130-4aa99b29c8f0

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021
import Theorems.Thm_OAI_Laughlin_Fock_contractionForm_haar_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourcePairEnd_rotation_s50
import Theorems.Thm_OAI_Laughlin_Spin_physical_threeBody_certificate_haar_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem projection_orbitalRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalRotation Q g) =
      ∑ j, sourceSpinRepresentation Q g i j • LinearMap.proj j := by
  ext v
  simp [orbitalRotation,Matrix.mulVec,dotProduct,LinearMap.proj]

theorem annihilate_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorRotation Q g x) =
      ∑ j, sourceSpinRepresentation Q g i j • exteriorRotation Q g (annihilate j x) := by
  unfold annihilate exteriorRotation
  rw [contraction_map,projection_orbitalRotation]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]

end Laughlin.Fock

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

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

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

theorem threeBodySpinRepresentation_continuous (Q : ℕ) (i j : PairOrbitalIndex Q) :
    Continuous (fun g => threeBodySpinRepresentation Q g i j) :=
  (sourceSpinRepresentation_continuous (2*Q-2) i.1 j.1).mul
    (sourceSpinRepresentation_continuous Q i.2 j.2)

theorem threeBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    threeBodySpinRepresentation Q g⁻¹=(threeBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,sourceSpinRepresentation_inv]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

theorem sourceThreeEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (i : PairOrbitalIndex Q) (x : Space Q) :
    sourceThreeEnd Q i (exteriorRotation Q g x) =
      ∑ j, threeBodySpinRepresentation Q g i j • exteriorRotation Q g (sourceThreeEnd Q j x) := by
  simp only [sourceThreeEnd,Module.End.mul_apply,sourcePairEnd_rotation_s50 Q hQ g,
    map_sum,map_smul,annihilate_exteriorRotation,Finset.smul_sum,smul_smul]
  simp only [threeBodySpinRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,
    Matrix.kroneckerMap,Matrix.of_apply,Fintype.sum_prod_type]

theorem physical_threeBody_Fock_haar (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      ∑ z : Fin (Q+1),
        ((physicalThreeBodyTraceFormula Q z.val : ℂ)/(coupledWeight Q z.val+1 : ℕ)) *
          contractionForm Q (sourceThreeEnd Q)
            ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x := by
  rw [contractionForm_haar_s50 Q (threeBodySpinRepresentation Q)
    (threeBodySpinRepresentation_inv Q) (threeBodySpinRepresentation_continuous Q)
    _ (sourceThreeEnd_rotation Q (by omega)),physical_threeBody_certificate_haar_s50 Q hQ,
    contractionForm_sum]
  simp only [contractionForm_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_FockComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem physical_threeBody_Fock_haar_real_s50_oai (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re =
      ∑ z : Fin (Q+1), (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) *
        (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re := by
  rw [physical_threeBody_Fock_haar Q hQ,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Complex.ofReal_natCast,← Complex.ofReal_div]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50_oai := @OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50_oai
