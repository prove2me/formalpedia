-- Prove2me | solution 1 for OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:39:18.151128+00:00
-- url     : https://prove2.me/submissions/c2e637d6-3131-4bfc-9282-c97455fe2aac

import Mathlib
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_commutant_scalar_s50

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

 theorem source_spin_intertwiner_adjoint (m n : ℕ)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation m g*M=M*sourceSpinRepresentation n g) :
    ∀ g : SourceSU2, sourceSpinRepresentation n g*Mᴴ=Mᴴ*sourceSpinRepresentation m g := by
  intro g
  have h := congrArg Matrix.conjTranspose (hM g⁻¹)
  simpa only [Matrix.conjTranspose_mul,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using h.symm

theorem source_spin_intertwiner_zero (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation m g*M=M*sourceSpinRepresentation n g) : M=0 := by
  have hA := source_spin_intertwiner_adjoint m n M hM
  have hl := source_spin_commutant_scalar_s50 m (M*Mᴴ) (by
    intro g
    rw [← Matrix.mul_assoc,hM,Matrix.mul_assoc,hA,← Matrix.mul_assoc])
  have hr := source_spin_commutant_scalar_s50 n (Mᴴ*M) (by
    intro g
    rw [← Matrix.mul_assoc,hA,Matrix.mul_assoc,hM,← Matrix.mul_assoc])
  by_contra h0
  obtain ⟨i,j,hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    apply h0
    ext i j
    simpa using not_exists.mp (not_exists.mp h i) j
  let c := (M*Mᴴ) 0 0
  let d := (Mᴴ*M) 0 0
  have hc : c ≠ 0 := by
    intro hc
    have hz : M*Mᴴ=0 := by rw [hl]; change c • _=0; rw [hc,zero_smul]
    exact h0 (Matrix.self_mul_conjTranspose_eq_zero.mp hz)
  have hd : c=d := by
    have h := Matrix.mul_assoc M Mᴴ M
    rw [hl,hr,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one] at h
    have he := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply,smul_eq_mul] at he
    exact mul_right_cancel₀ hij he
  have ht := Matrix.trace_mul_comm M Mᴴ
  rw [hl,hr] at ht
  simp only [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul] at ht
  change c*((m+1 : ℕ) : ℂ)=d*((n+1 : ℕ) : ℂ) at ht
  rw [← hd] at ht
  have he : m+1=n+1 := by exact_mod_cast mul_left_cancel₀ hc ht
  omega

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_RectangularAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
variable {G I J : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace G] in
theorem rectangularOrbit_mul (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (M : Matrix I J ℂ) (g h : G) :
    rectangularOrbit ρ σ M (g*h)=ρ g*rectangularOrbit ρ σ M h*σ g⁻¹ := by
  simp only [rectangularOrbit,map_mul,mul_inv_rev,Matrix.mul_assoc]

theorem compact_rectangularOrbit_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (hσ : ∀ i j, Continuous (fun g => σ g i j))
    (M : Matrix I J ℂ) (i : I) (j : J) : Integrable (fun g => rectangularOrbit ρ σ M g i j) μ := by
  have hc : Continuous (fun g => rectangularOrbit ρ σ M g i j) := by
    simp only [rectangularOrbit,Matrix.mul_apply]
    fun_prop
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
  [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem rectangularIntegral_mul_left (μ : Measure G) (f : G → Matrix I J ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix I I ℂ) :
    rectangularIntegral μ (fun g => A*f g)=A*rectangularIntegral μ f := by
  ext i j
  simp only [rectangularIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf k j).const_mul (A i k))]
  simp only [integral_const_mul]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [CompactSpace G]
  [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem rectangularIntegral_mul_right (μ : Measure G) (f : G → Matrix I J ℂ)
    (hf : ∀ i j, Integrable (fun g => f g i j) μ) (A : Matrix J J ℂ) :
    rectangularIntegral μ (fun g => f g*A)=rectangularIntegral μ f*A := by
  ext i j
  simp only [rectangularIntegral,Matrix.mul_apply]
  rw [integral_finsetSum _ (fun k hk => (hf i k).mul_const (A k j))]
  simp only [integral_mul_const]

theorem compact_rectangular_average_intertwines (μ : Measure G) [IsProbabilityMeasure μ]
    [IsMulLeftInvariant μ] (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (hρ : ∀ i j, Continuous (fun g => ρ g i j)) (hσ : ∀ i j, Continuous (fun g => σ g i j))
    (M : Matrix I J ℂ) (h : G) :
    ρ h*rectangularIntegral μ (rectangularOrbit ρ σ M)=
      rectangularIntegral μ (rectangularOrbit ρ σ M)*σ h := by
  have hf := compact_rectangularOrbit_integrable μ ρ σ hρ hσ M
  have hl : ∀ i j, Integrable (fun g => (ρ h*rectangularOrbit ρ σ M g) i j) μ := by
    intro i j
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ (fun k hk => (hf k j).const_mul _)
  have he : ρ h*rectangularIntegral μ (rectangularOrbit ρ σ M)*σ h⁻¹ =
      rectangularIntegral μ (rectangularOrbit ρ σ M) := by
    rw [← rectangularIntegral_mul_left μ _ hf,← rectangularIntegral_mul_right μ _ hl]
    ext i j
    simp only [rectangularIntegral,← rectangularOrbit_mul]
    exact integral_mul_left_eq_self (fun g => rectangularOrbit ρ σ M g i j) h
  have hh := congrArg (fun A : Matrix I J ℂ => A*σ h) he
  simpa only [Matrix.mul_assoc,← map_mul,inv_mul_cancel,map_one,Matrix.mul_one] using hh

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

theorem source_unequal_spin_haar_zero_s50_oai (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation m) (sourceSpinRepresentation n) M)=0 := by
  exact source_spin_intertwiner_zero m n hmn _
    (compact_rectangular_average_intertwines sourceHaar _ _
      (sourceSpinRepresentation_continuous m) (sourceSpinRepresentation_continuous n) M)

end Laughlin.Rotation

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50_oai := @OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50_oai
