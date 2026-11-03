-- Prove2me | solution 1 for OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:53.033507+00:00
-- url     : https://prove2.me/submissions/97d57495-73d5-42e1-951f-2d6f93d092fc

import Mathlib
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyMatrix_high_wedge_copy_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourBodyCopy_coordinate (Q r D n : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q) :
    fourBodyCopy Q r D hr hA hB n (p,i) =
      ∑ b : Fin (genericCoupledWeight Q Q r+1), pairCoupledWedge Q r hr b.val i *
        ((-1 : ℝ)^(D-r) * genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
          (D-r) hA hB n (p,b)) := by
  simp only [fourBodyCopy,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensorPairInclusion,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,ite_mul,
    one_mul,zero_mul,pairCoupledInclusion,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_CompactAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory MeasureTheory.Measure

variable {G I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype I] [DecidableEq I]

 theorem conjugateOrbit_continuous (ρ : G →* Matrix I I ℂ)
    (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (M : Matrix I I ℂ) (i j : I) :
    Continuous (fun g => conjugateOrbit ρ M g i j) := by
  simp only [conjugateOrbit,Matrix.mul_apply]
  fun_prop

variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]

 theorem compact_conjugateOrbit_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : G →* Matrix I I ℂ) (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (M : Matrix I I ℂ) :
    ∀ i j, Integrable (fun g => conjugateOrbit ρ M g i j) μ := by
  intro i j
  exact (conjugateOrbit_continuous ρ hρ M i j).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

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

theorem fourWedgeInclusion_factor (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    fourWedgeInclusion Q r D hr hA hB =
      ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
        (pairCoupledInclusion Q r hr).map Complex.ofReal) *
        physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB := by
  ext i n
  rw [fourWedgeInclusion,fourBodyCopy_coordinate]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_one,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,ite_mul,one_mul,zero_mul,physicalCoupledInclusion,
    Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,genericCoupledInclusion,pairCoupledInclusion]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem fourWedgeInclusion_SU2 (Q r D : ℕ) (hr : r ≤ Q) (hor : Odd r)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (g : SourceSU2) :
    fourBodySpinRepresentation Q g * fourWedgeInclusion Q r D hr hA hB =
      fourWedgeInclusion Q r D hr hA hB * sourceSpinRepresentation
        (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)) g := by
  rw [fourWedgeInclusion_factor]
  change (_ ⊗ₖ wedgePairMatrix Q g) * ((_ ⊗ₖ _) * _) = _
  rw [← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,Matrix.mul_one,
    pairCoupledInclusion_SU2 Q r hr hor]
  have he : sourceSpinRepresentation (2*Q-2) g ⊗ₖ
      ((pairCoupledInclusion Q r hr).map Complex.ofReal *
        sourceSpinRepresentation (genericCoupledWeight Q Q r) g) =
      ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
        (pairCoupledInclusion Q r hr).map Complex.ofReal) *
        (sourceSpinRepresentation (2*Q-2) g ⊗ₖ
          sourceSpinRepresentation (genericCoupledWeight Q Q r) g) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [he,Matrix.mul_assoc,physicalCoupledInclusion_SU2,Matrix.mul_assoc]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory

variable {G I J K L : Type*} [MeasurableSpace G]
  [Fintype I] [Fintype J] [Fintype K] [Fintype L]

omit [Fintype K] [Fintype L] in
theorem integral_matrix_sandwich (μ : Measure G) (f : G → Matrix I J ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ)
    (A : Matrix K I ℂ) (B : Matrix J L ℂ) :
    (fun k l => ∫ g, (A*f g*B) k l ∂μ) =
      A*entrywiseIntegral μ f*B := by
  funext k l
  simp only [Matrix.mul_apply,entrywiseIntegral,Finset.sum_mul]
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _
    (fun i hi => ((hf i j).const_mul (A k i)).mul_const (B j l)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun i hi => ((hf i j).const_mul (A k i)).mul_const (B j l))]
  simp only [integral_mul_const,integral_const_mul]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_high_copy (Q r D : ℕ) (hr : r ≤ Q) (hor : Odd r) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *
      fourWedgeInclusion Q r D hr hA hB = 0 := by
  have hz (g : SourceSU2) :
      conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g *
        fourWedgeInclusion Q r D hr hA hB = 0 := by
    unfold conjugateOrbit
    rw [Matrix.mul_assoc, fourWedgeInclusion_SU2 Q r D hr hor hA hB, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((physicalFourBodyMatrix Q).map Complex.ofReal),
      physicalFourBodyMatrix_high_wedge_copy_s50 Q r D hr hrD hA hB hD,Matrix.zero_mul,Matrix.mul_zero]
  have hi := integral_matrix_sandwich sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal))
    (compact_conjugateOrbit_integrable sourceHaar _ (fourBodySpinRepresentation_continuous Q) _)
    (1 : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) (fourWedgeInclusion Q r D hr hA hB)
  simp only [Matrix.one_mul,hz,Matrix.zero_apply,integral_zero] at hi
  exact hi.symm

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_high_column_s50_oai (Q : ℕ) (s : FourCoupledIndex Q)
    (hs : 23 < fourCoupledDeficit s) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *ᵥ
        (fun i => (fourCoupledBasis Q i s : ℂ)) = 0 := by
  let r := oddPairDeficit s.1
  let D := r+s.2.1.val
  have he := physicalFourBodyHaar_high_copy Q r D (oddPairDeficit_le s.1)
    (oddPairDeficit_odd s.1) (by dsimp [D,r]; omega)
    (by have := s.2.1.isLt; dsimp [D,r]; omega)
    (by have := s.2.1.isLt; dsimp [D,r]; omega) hs
  let n : Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1) :=
    ⟨s.2.2.val,by simpa only [D,Nat.add_sub_cancel_left] using s.2.2.isLt⟩
  funext i
  exact congrFun (congrFun he i) n

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50_oai := @OAI.Laughlin.Spin.physicalFourBodyHaar_high_column_s50_oai
