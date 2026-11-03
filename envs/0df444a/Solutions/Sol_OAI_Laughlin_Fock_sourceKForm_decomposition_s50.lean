-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceKForm_decomposition_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:51:23.105516+00:00
-- url     : https://prove2.me/submissions/a3ccc48f-8e28-4ecd-a95b-8fac205f3eb3

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Theorems.Thm_OAI_Laughlin_Fock_physical_twoBody_certificate_haar_s50
import Theorems.Thm_OAI_Laughlin_Fock_source_seven_squares_normal_form_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyOperatorHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem linearMap_rotation_inner_integrable (Q : ℕ) (L R : Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationInner Q
      (L (exteriorRotation Q g⁻¹ x)) (R (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (isClosed_tsupport _).isCompact
  unfold occupationInner
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q L x A).star.mul
    (linearMap_rotation_coordinate_continuous Q R x A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_SevenSquareAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_rotation_integrable {I : Type*} [Fintype I]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ) (x : Space Q) :
    Integrable (fun g : SourceSU2 => contractionForm Q L M (exteriorRotation Q g⁻¹ x)) sourceHaar := by
  unfold contractionForm
  exact integrable_finsetSum _ (fun i hi => integrable_finsetSum _
    (fun j hj => (linearMap_rotation_inner_integrable Q (L i) (L j) x).const_mul _))

theorem sourceKForm_decomposition_s50_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceKForm Q (by omega) x = (93527408868499/10^14 : ℝ)*sourceFockEnergy Q x +
      sourceA3Form Q x + sourceA4Form Q x := by
  let L2 := fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val
  let M2 := physicalTwoBodyMatrix Q
  let M3 := (physicalThreeBodyMatrix Q).map Complex.ofReal
  let M4 := (physicalFourBodyMatrix Q).map Complex.ofReal
  have hp (y : Space Q) :
      (Certificate.rows.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum =
      (contractionForm Q L2 M2 y + contractionForm Q (sourceThreeEnd Q) M3 y +
        contractionForm Q (sourceFourFamilyEnd Q) M4 y).re := by
    have h := congrArg Complex.re (source_seven_squares_normal_form_s50 Q hQ y)
    have hs (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
        (l.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q (by omega) row y) : ℂ))).sum.re =
          (l.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum := by
      induction l with
      | nil => simp
      | cons row l ih => simp only [List.map_cons,List.sum_cons,Complex.add_re,Complex.ofReal_re,ih]
    rw [hs] at h
    exact h
  have hi2 := contractionForm_rotation_integrable Q L2 M2 x
  have hi3 := contractionForm_rotation_integrable Q (sourceThreeEnd Q) M3 x
  have hi4 := contractionForm_rotation_integrable Q (sourceFourFamilyEnd Q) M4 x
  have h2 := congrArg Complex.re (physical_twoBody_certificate_haar_s50 Q (by omega) x)
  norm_num [Complex.mul_re] at h2
  rw [sourceKForm]
  simp_rw [hp]
  have hre := integral_re ((hi2.add hi3).add hi4)
  change (∫ g, (contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x)).re ∂sourceHaar) =
    (∫ g, contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re at hre
  have hi23 : Integrable (fun g : SourceSU2 =>
      contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x)) sourceHaar := hi2.add hi3
  rw [hre,integral_add hi23 hi4,
    integral_add hi2 hi3,Complex.add_re,Complex.add_re]
  change _ = _ + ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceThreeEnd Q) M3
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re +
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceFourFamilyEnd Q) M4
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re
  rw [mul_add,mul_add]
  congr 2
  norm_num [L2,M2]
  exact h2

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceKForm_decomposition_s50_oai := @OAI.Laughlin.Fock.sourceKForm_decomposition_s50_oai
