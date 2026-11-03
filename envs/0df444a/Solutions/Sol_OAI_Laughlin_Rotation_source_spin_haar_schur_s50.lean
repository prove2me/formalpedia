-- Prove2me | solution 1 for OAI.Laughlin.Rotation.source_spin_haar_schur_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:38:34.562502+00:00
-- url     : https://prove2.me/submissions/b44337f6-913e-4e9e-9317-0d6e3eed167c

import Mathlib
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_commutant_scalar_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_MatrixAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure

variable {G I : Type*} [MeasurableSpace G] [Fintype I]

theorem matrixIntegral_mul_left (μ : Measure G) (f : G → Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix I I ℂ) :
    matrixIntegral μ (fun g => A*f g) = A*matrixIntegral μ f := by
  ext i j
  simp only [matrixIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf k j).const_mul (A i k))]
  simp only [integral_const_mul]

theorem matrixIntegral_mul_right (μ : Measure G) (f : G → Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix I I ℂ) :
    matrixIntegral μ (fun g => f g*A) = matrixIntegral μ f*A := by
  ext i j
  simp only [matrixIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf i k).mul_const (A k j))]
  simp only [integral_mul_const]

theorem matrixIntegral_trace (μ : Measure G) (f : G → Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) :
    Matrix.trace (matrixIntegral μ f) = ∫ g, Matrix.trace (f g) ∂μ := by
  simp only [Matrix.trace,Matrix.diag,matrixIntegral]
  rw [integral_finsetSum _ (fun i hi => hf i i)]

variable [DecidableEq I]

omit [MeasurableSpace G] in
theorem conjugateOrbit_mul [Group G] (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ) (g h : G) :
    conjugateOrbit ρ M (g*h) = ρ g*conjugateOrbit ρ M h*ρ g⁻¹ := by
  simp only [conjugateOrbit,map_mul,mul_inv_rev,Matrix.mul_assoc]

omit [MeasurableSpace G] in
theorem conjugateOrbit_trace [Group G] (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ) (g : G) :
    Matrix.trace (conjugateOrbit ρ M g) = Matrix.trace M := by
  unfold conjugateOrbit
  rw [Matrix.trace_mul_cycle]
  rw [← map_mul,inv_mul_cancel,map_one,Matrix.one_mul]

theorem haar_average_invariant [Group G] [MeasurableMul G] (μ : Measure G) [IsMulLeftInvariant μ]
    (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => conjugateOrbit ρ M g i j) μ) (h : G) :
    ρ h*matrixIntegral μ (conjugateOrbit ρ M)*ρ h⁻¹ = matrixIntegral μ (conjugateOrbit ρ M) := by
  have hl : ∀ i j, Integrable (fun g => (ρ h*conjugateOrbit ρ M g) i j) μ := by
    intro i j
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ (fun k hk => (hf k j).const_mul _)
  rw [← matrixIntegral_mul_left μ _ hf,← matrixIntegral_mul_right μ _ hl]
  ext i j
  simp only [matrixIntegral,← conjugateOrbit_mul]
  exact integral_mul_left_eq_self (fun g => conjugateOrbit ρ M g i j) h

theorem haar_average_commutes [Group G] [MeasurableMul G] (μ : Measure G) [IsMulLeftInvariant μ]
    (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => conjugateOrbit ρ M g i j) μ) (h : G) :
    ρ h*matrixIntegral μ (conjugateOrbit ρ M) = matrixIntegral μ (conjugateOrbit ρ M)*ρ h := by
  have hh := congrArg (fun A : Matrix I I ℂ => A*ρ h) (haar_average_invariant μ ρ M hf h)
  simpa only [Matrix.mul_assoc,← map_mul,inv_mul_cancel,map_one,Matrix.mul_one] using hh

theorem haar_average_trace [Group G] (μ : Measure G) [IsProbabilityMeasure μ]
    (ρ : G →* Matrix I I ℂ) (M : Matrix I I ℂ)
    (hf : ∀ i j, Integrable (fun g => conjugateOrbit ρ M g i j) μ) :
    Matrix.trace (matrixIntegral μ (conjugateOrbit ρ M)) = Matrix.trace M := by
  rw [matrixIntegral_trace μ _ hf]
  simp [conjugateOrbit_trace]

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

theorem compact_haar_average_commutes (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ]
    (ρ : G →* Matrix I I ℂ) (hρ : ∀ i j, Continuous (fun g => ρ g i j))
    (M : Matrix I I ℂ) (g : G) :
    ρ g*matrixIntegral μ (conjugateOrbit ρ M) = matrixIntegral μ (conjugateOrbit ρ M)*ρ g := by
  exact haar_average_commutes μ ρ M (compact_conjugateOrbit_integrable μ ρ hρ M) g

theorem compact_haar_average_trace (μ : Measure G) [IsProbabilityMeasure μ]
    (ρ : G →* Matrix I I ℂ) (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (M : Matrix I I ℂ) :
    Matrix.trace (matrixIntegral μ (conjugateOrbit ρ M)) = Matrix.trace M := by
  exact haar_average_trace μ ρ M (compact_conjugateOrbit_integrable μ ρ hρ M)

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

 theorem source_spin_haar_average_commutes (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) (g : SourceSU2) :
    sourceSpinRepresentation Q g * matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) * sourceSpinRepresentation Q g := by
  exact compact_haar_average_commutes sourceHaar (sourceSpinRepresentation Q)
    (sourceSpinRepresentation_continuous Q) M g

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem source_spin_haar_schur_s50_oai (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      (Matrix.trace M / (Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) := by
  let H := matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M)
  have hc := source_spin_commutant_scalar_s50 Q H (source_spin_haar_average_commutes Q M)
  have ht := compact_haar_average_trace sourceHaar (sourceSpinRepresentation Q)
    (sourceSpinRepresentation_continuous Q) M
  have he := congrArg Matrix.trace hc
  simp only [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at he
  have hdim : ((Q+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero Q
  have hs : Matrix.trace M / ((Q+1 : ℕ) : ℂ) = H 0 0 := by
    rw [← ht]
    change Matrix.trace H / ((Q+1 : ℕ) : ℂ)=H 0 0
    rw [he]
    field_simp
  rw [hs]
  exact hc

end Laughlin.Rotation

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Rotation.source_spin_haar_schur_s50_oai := @OAI.Laughlin.Rotation.source_spin_haar_schur_s50_oai
