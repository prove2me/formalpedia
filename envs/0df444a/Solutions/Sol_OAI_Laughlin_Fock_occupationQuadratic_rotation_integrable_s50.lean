-- Prove2me | solution 1 for OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:19:24.007426+00:00
-- url     : https://prove2.me/submissions/ff8cf195-80b5-44ff-968d-3fd1825d0768

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Tensor_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbitalRotation_mode (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) :
    orbitalRotation Q g (mode i) = ∑ j, sourceSpinRepresentation Q g j i • mode j := by
  rw [orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]

theorem exteriorRotation_basis_wedge (N Q : ℕ) (g : SourceSU2) (a : Configuration N Q) :
    exteriorRotation Q g (ExteriorAlgebra.ιMulti ℂ N (fun k => mode (a k))) =
      ∑ b : Configuration N Q, (∏ k, sourceSpinRepresentation Q g (b k) (a k)) •
        ExteriorAlgebra.ιMulti ℂ N (fun k => mode (b k)) := by
  unfold exteriorRotation
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ N (fun k => orbitalRotation Q g (mode (a k))) = _
  simp_rw [orbitalRotation_mode]
  change (ExteriorAlgebra.ιMulti ℂ N).toMultilinearMap
    (fun k => ∑ j, sourceSpinRepresentation Q g j (a k) • mode j) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact (ExteriorAlgebra.ιMulti ℂ N).map_smul_univ _ _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_SpinContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationBasis_wedge (Q : ℕ) (A : Finset (Fin (Q+1))) :
    occupationBasis Q A = ExteriorAlgebra.ιMulti ℂ A.card
      (fun k => mode (Set.powersetCard.ofFinEmbEquiv.symm (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) k)) := by
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card).val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family,Function.comp_def,Pi.basisFun_apply,mode]

theorem exteriorRotation_basis_continuous (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr
      (exteriorRotation Q g (occupationBasis Q B)) A) := by
  simp only [occupationBasis_wedge Q B,exteriorRotation_basis_wedge,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  apply continuous_finsetSum
  intro b hb
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro k hk
  exact sourceSpinRepresentation_continuous Q _ _

theorem exteriorRotation_coordinate_continuous (Q : ℕ) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr (exteriorRotation Q g x) A) := by
  have hx := (occupationBasis Q).sum_repr x
  conv in exteriorRotation Q _ x => rw [← hx]
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul (exteriorRotation_basis_continuous Q A b)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_OrbitIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators

theorem linearMap_rotation_coordinate_continuous (Q : ℕ) (L : Module.End ℂ (Space Q))
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A) := by
  have he (g : SourceSU2) : (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A =
      ∑ B, (occupationBasis Q).repr (exteriorRotation Q g⁻¹ x) B *
        (occupationBasis Q).repr (L (occupationBasis Q B)) A := by
    conv_lhs => rw [← (occupationBasis Q).sum_repr (exteriorRotation Q g⁻¹ x)]
    simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro B hB
  exact ((exteriorRotation_coordinate_continuous Q x B).comp continuous_inv).mul continuous_const

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HaarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem occupationQuadratic_rotation_integrable_s50_oai {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (L : I → Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationQuadratic Q R
      (fun i => L i (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (isClosed_tsupport _).isCompact
  unfold occupationQuadratic occupationInner
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  apply continuous_const.mul
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q (L i) x A).star.mul
    (linearMap_rotation_coordinate_continuous Q (L j) x A)

end Laughlin.Fock

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50_oai.{u_1} := @OAI.Laughlin.Fock.occupationQuadratic_rotation_integrable_s50_oai.{u_1}
