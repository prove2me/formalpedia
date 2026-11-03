-- Prove2me | solution 1 for OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:02:28.464206+00:00
-- url     : https://prove2.me/submissions/5f9058c0-8f1f-4f86-891d-087ba6fdc9c2

import Mathlib
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50
import Theorems.Thm_OAI_Laughlin_Spin_threeCoupledInclusion_adjoint_SU2_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HaarOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped Matrix

theorem source_equal_spin_haar_trace (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation Q) (sourceSpinRepresentation Q) M)=
      (Matrix.trace M/(Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :=
  source_spin_haar_schur_s50 Q M

end Laughlin.Rotation

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

theorem threeSpinProjector_complex_factor (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeSpinProjector Q hQ z).map Complex.ofReal =
      threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ := by
  funext i j
  change (↑(∑ s, (coupledBasisMatrix Q hQ * coupledSelector Q z) i s *
    coupledBasisMatrix Q hQ j s) : ℂ) = _
  simp only [coupledSelector,Matrix.mul_diagonal]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,threeCoupledInclusion,
    Complex.star_def,Complex.conj_ofReal]
  rw [Fintype.sum_sigma]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Complex.ofReal_sum,
    Complex.ofReal_mul,coupledBasisMatrix]

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

theorem threeBodySpinRepresentation_continuous (Q : ℕ) (i j : PairOrbitalIndex Q) :
    Continuous (fun g => threeBodySpinRepresentation Q g i j) :=
  (sourceSpinRepresentation_continuous (2*Q-2) i.1 j.1).mul
    (sourceSpinRepresentation_continuous Q i.2 j.2)

theorem threeBody_haar_compressed (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w =
    rectangularIntegral sourceHaar (rectangularOrbit
      (sourceSpinRepresentation (coupledWeight Q z.val))
      (sourceSpinRepresentation (coupledWeight Q w.val))
      ((threeCoupledInclusion Q hQ z)ᴴ*M*threeCoupledInclusion Q hQ w)) := by
  change (threeCoupledInclusion Q hQ z)ᴴ * entrywiseIntegral sourceHaar
    (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = _
  rw [← integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (threeBodySpinRepresentation_continuous Q) M)]
  funext i j
  apply integral_congr_ae
  filter_upwards [] with g
  have hw : threeBodySpinRepresentation Q g⁻¹*threeCoupledInclusion Q hQ w =
    threeCoupledInclusion Q hQ w*sourceSpinRepresentation (coupledWeight Q w.val) g⁻¹ :=
    threeCoupledInclusion_SU2 Q hQ w g⁻¹
  simp only [conjugateOrbit,rectangularOrbit]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,threeCoupledInclusion_adjoint_SU2_s50,
    Matrix.mul_assoc,Matrix.mul_assoc,hw]
  simp only [Matrix.mul_assoc]

theorem threeBody_haar_diagonal_block_s50_oai (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ z =
      (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/
        (coupledWeight Q z.val+1 : ℕ)) • 1 := by
  rw [threeBody_haar_compressed,source_equal_spin_haar_trace]
  congr 2
  rw [threeSpinProjector_complex_factor]
  calc
    _ = Matrix.trace (threeCoupledInclusion Q hQ z*((threeCoupledInclusion Q hQ z)ᴴ*M)) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50_oai := @OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50_oai
