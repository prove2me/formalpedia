-- Prove2me | solution 1 for OAI.Laughlin.Spin.fourBody_cross_orbit_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:06:36.2962+00:00
-- url     : https://prove2.me/submissions/91088f9d-b068-4450-9b40-d7bfb8884c68

import Mathlib
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50
import Theorems.Thm_OAI_Laughlin_Spin_retainedFourInclusion_adjoint_SU2_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem castSpinColumns_SU2 {I : Type*} [Fintype I]
    (m n : ℕ) (h : m=n) (W : Matrix I (Fin (m+1)) ℂ)
    (R : Matrix I I ℂ) (g : SourceSU2)
    (hW : R*W=W*sourceSpinRepresentation m g) :
    R*castSpinColumns m n h W = castSpinColumns m n h W*sourceSpinRepresentation n g := by
  subst n
  exact hW

theorem fourSpinWeight_dimension (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourSpinWeight Q D+1=4*Q-1-2*D := by unfold fourSpinWeight; omega

theorem retainedFourInclusion_SU2 (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (g : SourceSU2) :
    fourBodySpinRepresentation Q g * retainedFourInclusion Q D hQ r =
      retainedFourInclusion Q D hQ r * sourceSpinRepresentation (fourSpinWeight Q D) g := by
  unfold retainedFourInclusion
  apply castSpinColumns_SU2
  exact fourWedgeInclusion_SU2 Q (oddPairDeficit r) D _ (oddPairDeficit_odd r) _ _ g

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MultiplicityHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourBody_cross_orbit_s50_oai (Q D : ℕ) (hD : D+2 ≤ Q) (r s : OddPairLabel D)
    (M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (fourBodySpinRepresentation Q)
      (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ)) =
      (Matrix.trace M / (4*Q-1-2*D : ℕ)) •
        (retainedFourInclusion Q D hD r * (retainedFourInclusion Q D hD s)ᴴ) := by
  have he (g : SourceSU2) : conjugateOrbit (fourBodySpinRepresentation Q)
      (retainedFourInclusion Q D hD r * M * (retainedFourInclusion Q D hD s)ᴴ) g =
      retainedFourInclusion Q D hD r *
        conjugateOrbit (sourceSpinRepresentation (fourSpinWeight Q D)) M g *
        (retainedFourInclusion Q D hD s)ᴴ := by
    unfold conjugateOrbit
    calc
      _ = (fourBodySpinRepresentation Q g*retainedFourInclusion Q D hD r)*M*
        ((retainedFourInclusion Q D hD s)ᴴ*fourBodySpinRepresentation Q g⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [retainedFourInclusion_SU2,retainedFourInclusion_adjoint_SU2_s50]
        simp only [Matrix.mul_assoc]
  unfold matrixIntegral
  simp_rw [he]
  rw [integral_matrix_sandwich sourceHaar _ (compact_conjugateOrbit_integrable sourceHaar _
    (sourceSpinRepresentation_continuous (fourSpinWeight Q D)) M)]
  change retainedFourInclusion Q D hD r * matrixIntegral sourceHaar
    (conjugateOrbit (sourceSpinRepresentation (fourSpinWeight Q D)) M) *
      (retainedFourInclusion Q D hD s)ᴴ = _
  rw [source_spin_haar_schur_s50,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.fourBody_cross_orbit_s50_oai := @OAI.Laughlin.Spin.fourBody_cross_orbit_s50_oai
