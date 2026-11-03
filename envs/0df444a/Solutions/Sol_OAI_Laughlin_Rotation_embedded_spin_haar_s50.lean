-- Prove2me | solution 1 for OAI.Laughlin.Rotation.embedded_spin_haar_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:37:05.914809+00:00
-- url     : https://prove2.me/submissions/08e784c7-5297-4c2d-93af-694289ccf477

import Mathlib
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_EmbeddedSpinHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory
open scoped BigOperators Matrix

theorem embedded_spin_haar_s50_oai {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : SourceSU2 →* Matrix I I ℂ) (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (m : ℕ) (W : Matrix I (Fin (m+1)) ℂ)
    (hW : ∀ g, ρ g*W=W*sourceSpinRepresentation m g)
    (M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit ρ (W*M*Wᴴ)) =
      (Matrix.trace M/(m+1 : ℕ)) • (W*Wᴴ) := by
  have ha (g : SourceSU2) : Wᴴ*ρ g⁻¹=sourceSpinRepresentation m g⁻¹*Wᴴ := by
    have h := congrArg Matrix.conjTranspose (hW g)
    simpa only [Matrix.conjTranspose_mul,← hρ,← sourceSpinRepresentation_inv] using h
  have he (g : SourceSU2) : conjugateOrbit ρ (W*M*Wᴴ) g =
      W*conjugateOrbit (sourceSpinRepresentation m) M g*Wᴴ := by
    unfold conjugateOrbit
    calc
      _ = (ρ g*W)*M*(Wᴴ*ρ g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW,ha]; simp only [Matrix.mul_assoc]
  unfold matrixIntegral
  simp_rw [he]
  rw [integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (sourceSpinRepresentation_continuous m) M)]
  change W*matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation m) M)*Wᴴ = _
  rw [source_spin_haar_schur_s50,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]

end Laughlin.Rotation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Rotation.embedded_spin_haar_s50_oai.{u_1} := @OAI.Laughlin.Rotation.embedded_spin_haar_s50_oai.{u_1}
