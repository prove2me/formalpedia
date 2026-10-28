-- Prove2me | solution 1 for OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:46:46.203367+00:00
-- url     : https://prove2.me/submissions/23aa898a-e2e3-4145-a550-fdce61fde838

import Mathlib
import Definitions.Def_OAIQ047L004

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_CoupledIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledInclusion_isometry (Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q r hr = 1 := by
  ext n m
  simp only [Matrix.mul_apply,Matrix.transpose_apply,pairCoupledInclusion,Matrix.one_apply]
  by_cases h : n=m
  · subst m
    rw [ite_eq_left rfl]
    simpa only [pow_two,vectorNormSq] using pairCoupledWedge_norm Q r n.val hr ho (by omega)
  · rw [ite_eq_right h]
    exact pairCoupledWedge_orthogonal Q r r n.val m.val hr hr ho ho
      (Or.inr (fun he => h (Fin.ext he)))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tensorPairInclusion_isometry (A Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q r hr = 1 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,pairCoupledInclusion_isometry Q r hr ho,
    Matrix.one_kronecker_one]

theorem isometry_vectorNormSq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix I J ℝ) (hW : Wᵀ*W=1) (f : J → ℝ) :
    vectorNormSq (W *ᵥ f) = vectorNormSq f := by
  unfold vectorNormSq
  simp only [pow_two]
  have hp (v : J → ℝ) (w : I → ℝ) :
      (∑ i, (W *ᵥ v) i*w i) = ∑ i, v i*(Wᵀ *ᵥ w) i := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj; ring
  rw [hp,Matrix.mulVec_mulVec,hW,Matrix.one_mulVec]

theorem phased_generic_norm (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    vectorNormSq ((-1 : ℝ)^z • genericUnitDescendant A B z hA hB n) = 1 := by
  unfold vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  have h : ((-1 : ℝ)^z)^2 = 1 := by rw [← pow_mul,mul_comm z 2,pow_mul]; norm_num
  rw [h,one_mul]
  exact genericUnitDescendant_norm A B z n hA hB hn

theorem fourBodyCopy_norm (Q r D n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hn : n ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)) :
    vectorNormSq (fourBodyCopy Q r D hr hA hB n) = 1 := by
  rw [fourBodyCopy,isometry_vectorNormSq _ (tensorPairInclusion_isometry _ Q r hr ho)]
  exact phased_generic_norm _ _ _ _ hA hB hn

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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairCoupledWedge_off (Q r n : ℕ) (hr : r ≤ Q) (i : WedgePairIndex Q)
    (hi : i.val.1.val+i.val.2.val ≠ r+n) :
    pairCoupledWedge Q r hr n i = 0 := by
  simp only [pairCoupledWedge,tensorToWedgePair,pairCoupledTensor,Pi.smul_apply,smul_eq_mul,
    genericUnitDescendant_off Q Q r n hr hr i.val hi,mul_zero]

theorem genericUnitDescendant_transport_right (A B B' z n : ℕ) (he : B=B')
    (hA : z ≤ A) (hB : z ≤ B) (hB' : z ≤ B') (i : SpinIndex A B) :
    genericUnitDescendant A B z hA hB n i =
      genericUnitDescendant A B' z hA hB' n (i.1,Fin.cast (congrArg (fun k => k+1) he) i.2) := by
  subst B'; rfl

theorem fourBodyCopy_source_coefficient (Q r D T : ℕ) (hrD : r ≤ D) (hDT : D ≤ T)
    (hQT : T+2 ≤ Q) (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hT : p.val+i.val.1.val+i.val.2.val=T) :
    fourBodyCopy Q r D (by omega) (by omega) (by unfold genericCoupledWeight; omega)
      (T-D) (p,i) = fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val := by
  have hcw : genericCoupledWeight Q Q r = 2*Q-2*r := by unfold genericCoupledWeight; omega
  rw [fourBodyCopy_coordinate]
  by_cases hri : r ≤ i.val.1.val+i.val.2.val
  · let b : Fin (genericCoupledWeight Q Q r+1) := ⟨i.val.1.val+i.val.2.val-r,by
      rw [hcw]; omega⟩
    rw [Finset.sum_eq_single b]
    · unfold fourBodyCoefficient
      rw [ite_eq_left hri]
      have hI : r ≤ i.val.1.val+i.val.2.val ∧ i.val.1.val ≤ i.val.1.val+i.val.2.val ∧
          i.val.1.val+i.val.2.val ≤ Q ∧ i.val.1.val+i.val.2.val ≤ Q := by omega
      have hO : D-r ≤ T-r ∧ p.val ≤ T-r ∧ T-r ≤ 2*Q-2 ∧ T-r ≤ 2*Q-2*r := by omega
      rw [physicalCouplingCoefficient,dite_eq_left hI,physicalCouplingCoefficient,dite_eq_left hO]
      simp only [pairCoupledWedge,tensorToWedgePair,pairCoupledTensor,Pi.smul_apply,smul_eq_mul]
      have hi2 : i.val.1.val+i.val.2.val-i.val.1.val=i.val.2.val := by omega
      have hb : T-r-p.val=b.val := by dsimp [b]; omega
      have hn : T-r-(D-r)=T-D := by omega
      try simp only [hi2,hn]
      have hbfin : (⟨T-r-p.val,by omega⟩ : Fin (2*Q-2*r+1)) =
          ⟨b.val,by rw [← hcw]; exact b.isLt⟩ := by apply Fin.ext; exact hb
      rw [hbfin]
      have hout := genericUnitDescendant_transport_right (2*Q-2) (genericCoupledWeight Q Q r)
        (2*Q-2*r) (D-r) (T-D) hcw (by omega) (by unfold genericCoupledWeight; omega)
        (by omega) (p,b)
      rw [hout]
      rfl
    · intro c hc hcb
      rw [pairCoupledWedge_off Q r c.val (by omega) i (by
        intro he; apply hcb; apply Fin.ext; dsimp [b]; omega),zero_mul]
    · simp
  · rw [fourBodyCoefficient,ite_eq_right hri]
    apply Finset.sum_eq_zero
    intro c hc
    rw [pairCoupledWedge_off Q r c.val (by omega) i (by omega),zero_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourBodyCopy_off (Q r D n : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hi : p.val+i.val.1.val+i.val.2.val ≠ D+n) :
    fourBodyCopy Q r D hr hA hB n (p,i) = 0 := by
  rw [fourBodyCopy_coordinate]
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hi' : i.val.1.val+i.val.2.val=r+b.val
  · rw [genericUnitDescendant_off _ _ _ _ hA hB (p,b) (by dsimp; omega),mul_zero,mul_zero]
  · rw [pairCoupledWedge_off Q r b.val hr i hi',zero_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_TensorAction
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Compact
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_MatrixAverage
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_CompactAverage
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Representation
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

 theorem source_spin_haar_average_commutes (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) (g : SourceSU2) :
    sourceSpinRepresentation Q g * matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) * sourceSpinRepresentation Q g := by
  exact compact_haar_average_commutes sourceHaar (sourceSpinRepresentation Q)
    (sourceSpinRepresentation_continuous Q) M g

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_WeightProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

 theorem tensorWeight_zero_iff (Q : ℕ) (a : Fin Q → Fin 2) :
    tensorWeight Q a=0 ↔ a=fun _ => 0 := by
  constructor
  · intro h
    have he : tensorBits Q a=∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : a i ≠ 1 := by
      intro hi
      have hm : i ∈ tensorBits Q a := by simp [tensorBits,hi]
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    apply Fin.ext
    have ha := (a i).isLt
    have hn' : (a i).val ≠ 1 := by intro he; exact hn (Fin.ext he)
    simp only [Fin.val_zero]
    omega
  · rintro rfl
    simp [tensorWeight,tensorBits]

 theorem symmetricTensor_zero_column (Q : ℕ) (a : Fin Q → Fin 2) :
    symmetricTensorInclusion Q a 0 = if a=(fun _ => 0) then 1 else 0 := by
  simp [symmetricTensorInclusion,symmetricTensorInclusionReal,tensorWeight_zero_iff,apply_ite]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Torus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem sourceSpinRepresentation_torus (Q : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    sourceSpinRepresentation Q (sourceTorus z hz) =
      Matrix.diagonal (fun p : Fin (Q+1) => (star z)^p.val*z^(Q-p.val)) := by
  change (symmetricTensorInclusion Q)ᴴ * tensorMatrix Q
    (Matrix.diagonal (fun i : Fin 2 => if i=0 then z else star z)) * symmetricTensorInclusion Q = _
  rw [tensorMatrix_diagonal,Matrix.mul_assoc,symmetricTensor_diagonal_intertwining Q (fun k => (star z)^k*z^(Q-k)),
    ← Matrix.mul_assoc,symmetricTensorInclusion_isometry,Matrix.one_mul]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Basis2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericCoupledIndex_card (A B : ℕ) :
    Fintype.card (GenericCoupledIndex A B) = Fintype.card (SpinIndex A B) := by
  have hr : (Fintype.card (GenericCoupledIndex A B) : ℝ) =
      (Fintype.card (SpinIndex A B) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (min A B+1)) :
        ((genericCoupledWeight A B z.val+1 : ℕ) : ℝ) = A+B+1-2*(z.val : ℝ) := by
      have hz := z.isLt
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z.val ≤ A+B)]
      push_cast
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rcases le_total A B with h | h
    · rw [Nat.min_eq_left h]; ring
    · rw [Nat.min_eq_right h]; ring
  exact_mod_cast hr

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CopyOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem pairCoupledInclusion_cross (Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q s hs = 0 := by
  ext n m
  exact pairCoupledWedge_orthogonal Q r s n.val m.val hr hs hor hos (Or.inl hne)

theorem tensorPairInclusion_cross (A Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q s hs = 0 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,pairCoupledInclusion_cross Q r s hr hs hor hos hne]
  simp

theorem fourBodyCopy_orthogonal_pair (Q r s D E n m : ℕ)
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s) (hne : r ≠ s)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-s ≤ 2*Q-2) (hD : E-s ≤ genericCoupledWeight Q Q s) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q s E hs hC hD m i) = 0 := by
  have hp {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
      (A : Matrix I J ℝ) (B : Matrix I K ℝ) (v : J → ℝ) (w : K → ℝ) :
      (∑ i, (A *ᵥ v) i * (B *ᵥ w) i) = ∑ j, v j * ((Aᵀ*B) *ᵥ w) j := by
    change (A *ᵥ v) ⬝ᵥ (B *ᵥ w) = v ⬝ᵥ ((Aᵀ*B) *ᵥ w)
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp,tensorPairInclusion_cross _ Q r s hr hs hor hos hne]
  simp

theorem fourBodyCopy_orthogonal_outer (Q r D E n m : ℕ)
    (hr : r ≤ Q) (hor : Odd r) (hrD : r ≤ D) (hrE : r ≤ E)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-r ≤ 2*Q-2) (hD : E-r ≤ genericCoupledWeight Q Q r)
    (hne : D ≠ E ∨ n ≠ m) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q r E hr hC hD m i) = 0 := by
  have hp {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
      (A : Matrix I J ℝ) (h : Aᵀ*A=1) (v w : J → ℝ) :
      (∑ i, (A *ᵥ v) i * (A *ᵥ w) i) = ∑ j, v j*w j := by
    change (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w
    rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp _ (tensorPairInclusion_isometry _ Q r hr hor)]
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((-1 : ℝ)^(D-r) * (-1 : ℝ)^(E-r)) *
      (∑ i, genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB n i *
        genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (E-r) hC hD m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by
      rw [genericUnitDescendant_orthogonal _ _ _ _ _ _ hA hB hC hD (by
        rcases hne with h | h
        · left; omega
        · exact Or.inr h),mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem fourCoupledIndex_card (Q : ℕ) :
    Fintype.card (FourCoupledIndex Q) = Fintype.card (Fin (2*Q-2+1) × WedgePairIndex Q) := by
  rw [Fintype.card_sigma]
  simp_rw [genericCoupledIndex_card,Fintype.card_prod,Fintype.card_fin]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [Fintype.card_sigma,Fintype.card_fin] using pairCoupledIndex_card Q

theorem fourCoupledBasis_isometry (Q : ℕ) :
    (fourCoupledBasis Q)ᵀ * fourCoupledBasis Q = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,fourCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      fourBodyCopy_norm Q (oddPairDeficit s.1) (oddPairDeficit s.1+s.2.1.val)
        s.2.2.val (oddPairDeficit_le s.1) (oddPairDeficit_odd s.1) _ _
        (by have := s.2.2.isLt; simpa only [Nat.add_sub_cancel_left] using Nat.le_of_lt_succ this)
  · rw [ite_eq_right h]
    rcases s with ⟨r,⟨z,n⟩⟩
    rcases t with ⟨s,⟨w,m⟩⟩
    dsimp only at *
    by_cases hrs : r=s
    · subst s
      apply fourBodyCopy_orthogonal_outer _ _ _ _ _ _ _ (oddPairDeficit_odd r)
        (by omega) (by omega)
      by_cases hzw : z=w
      · subst w
        right
        intro he
        exact h (by have hn : n=m := Fin.ext he; subst m; rfl)
      · left
        intro he
        exact hzw (Fin.ext (by omega))
    · apply fourBodyCopy_orthogonal_pair _ _ _ _ _ _ _ _ _
        (oddPairDeficit_odd r) (oddPairDeficit_odd s)
      intro he
      exact hrs (Fin.ext (by dsimp [oddPairDeficit] at he; omega))

theorem fourCoupledBasis_complete (Q : ℕ) :
    fourCoupledBasis Q * (fourCoupledBasis Q)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := FourCoupledIndex Q)
    (n := Fin (2*Q-2+1) × WedgePairIndex Q) (R := ℝ)
    (fourCoupledIndex_card Q)).mp (fourCoupledBasis_isometry Q)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Mixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem tensorWeight_sum_const (Q p : ℕ) (c : ℂ) :
    (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then c else 0) = (Q.choose p : ℂ)*c := by
  have he (a : Fin Q → Fin 2) : (if tensorWeight Q a=p then c else 0) =
      ((if tensorWeight Q a=p then (1 : ℝ) else 0) : ℂ)*c := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hc := congrArg Complex.ofReal (tensorWeight_count Q p)
  simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,Complex.ofReal_natCast] at hc
  simpa only [Complex.ofReal_one] using congrArg (fun z : ℂ => z*c) hc

 theorem symmetricTensorInclusion_column_sum (Q : ℕ) (p : Fin (Q+1)) :
    (∑ a, symmetricTensorInclusion Q a p) = (Real.sqrt (Q.choose p.val : ℝ) : ℂ) := by
  simp only [symmetricTensorInclusion,Matrix.map_apply,symmetricTensorInclusionReal,apply_ite,
    Complex.ofReal_zero]
  rw [tensorWeight_sum_const]
  have hs : (Real.sqrt (Q.choose p.val : ℝ) : ℂ)^2=(Q.choose p.val : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose p.val by positivity)
  have hn : (Real.sqrt (Q.choose p.val : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  rw [Complex.ofReal_inv,← hs]
  field_simp

 theorem tensorMatrix_uniform_first_column (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (h0 : A 0 0=c) (h1 : A 1 0=c) (a : Fin Q → Fin 2) :
    (tensorMatrix Q A*symmetricTensorInclusion Q) a 0=c^Q := by
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single (fun _ => (0 : Fin 2))]
  · rw [symmetricTensor_zero_column,ite_eq_left rfl,mul_one]
    have he (i : Fin Q) : A (a i) 0=c := by
      have h : a i=0 ∨ a i=1 := by omega
      rcases h with h | h
      · rw [h]; exact h0
      · rw [h]; exact h1
    simp [tensorMatrix,he]
  · intro b hb hne
    rw [symmetricTensor_zero_column,ite_eq_right hne,mul_zero]
  · simp

theorem sourceSpinRepresentation_mixer_column (Q : ℕ) (p : Fin (Q+1)) :
    sourceSpinRepresentation Q sourceMixer p 0 =
      (Real.sqrt (Q.choose p.val : ℝ) : ℂ)*(Real.sqrt (1/2) : ℂ)^Q := by
  change ((symmetricTensorInclusion Q)ᴴ*tensorMatrix Q sourceMixer.val*symmetricTensorInclusion Q) p 0 = _
  rw [Matrix.mul_assoc,Matrix.mul_apply]
  have he (a : Fin Q → Fin 2) : (tensorMatrix Q sourceMixer.val*symmetricTensorInclusion Q) a 0 =
      (Real.sqrt (1/2) : ℂ)^Q := tensorMatrix_uniform_first_column Q _ _ rfl rfl a
  simp_rw [he,Matrix.conjTranspose_apply]
  have hr (a : Fin Q → Fin 2) : star (symmetricTensorInclusion Q a p)=symmetricTensorInclusion Q a p := by
    simp [symmetricTensorInclusion]
  simp_rw [hr]
  rw [← Finset.sum_mul,symmetricTensorInclusion_column_sum]

 theorem sourceSpinRepresentation_mixer_column_ne_zero (Q : ℕ) (p : Fin (Q+1)) :
    sourceSpinRepresentation Q sourceMixer p 0 ≠ 0 := by
  rw [sourceSpinRepresentation_mixer_column]
  apply mul_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (by omega : p.val ≤ Q)
  · apply pow_ne_zero
    exact Complex.ofReal_ne_zero.mpr (by positivity)

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem spinSeparatingRoot_primitive (Q : ℕ) : IsPrimitiveRoot (spinSeparatingRoot Q) (2*Q+1) :=
  Complex.isPrimitiveRoot_exp _ (by omega)
 theorem spinSeparatingRoot_norm (Q : ℕ) : ‖spinSeparatingRoot Q‖=1 := by
  simp [spinSeparatingRoot,Complex.norm_exp,Complex.div_re]

 theorem torus_weight_fraction (Q : ℕ) (z : ℂ) (hz : ‖z‖=1) (p : Fin (Q+1)) :
    (star z)^p.val*z^(Q-p.val) = z^Q/z^(2*p.val) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hinv : star z=z⁻¹ := by
    simp [Complex.inv_def,Complex.normSq_eq_norm_sq,hz]
  rw [hinv,inv_pow]
  have hQ : Q=(Q-p.val)+p.val := by omega
  have hp : z^Q=z^(Q-p.val)*z^p.val := by rw [← pow_add,← hQ]
  rw [hp,show 2*p.val=p.val+p.val by omega,pow_add]
  field_simp

 theorem spinSeparatingRoot_weights_injective (Q : ℕ) : Function.Injective
    (fun p : Fin (Q+1) => (star (spinSeparatingRoot Q))^p.val*(spinSeparatingRoot Q)^(Q-p.val)) := by
  intro p q hpq
  dsimp only at hpq
  let z := spinSeparatingRoot Q
  have hz := spinSeparatingRoot_norm Q
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  rw [torus_weight_fraction Q _ hz p,torus_weight_fraction Q _ hz q] at hpq
  have he := (div_eq_div_iff (pow_ne_zero (2*p.val) hz0) (pow_ne_zero (2*q.val) hz0)).mp hpq
  have hpows : z^(2*p.val)=z^(2*q.val) := (mul_left_cancel₀ (pow_ne_zero Q hz0) he).symm
  have h := (spinSeparatingRoot_primitive Q).pow_inj (by omega : 2*p.val < 2*Q+1)
    (by omega : 2*q.val < 2*Q+1) hpows
  exact Fin.ext (by omega)

theorem source_spin_commutant_scalar (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ)
    (hM : ∀ g : SourceSU2, sourceSpinRepresentation Q g*M=M*sourceSpinRepresentation Q g) :
    M=M 0 0 • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) := by
  have ht := hM (sourceTorus (spinSeparatingRoot Q) (spinSeparatingRoot_norm Q))
  rw [sourceSpinRepresentation_torus] at ht
  have hd : M=Matrix.diagonal (fun p => M p p) := by
    ext p q
    by_cases hpq : p=q
    · subst q; simp
    · rw [Matrix.diagonal_apply_ne _ hpq]
      have he := congrFun (congrFun ht p) q
      simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he
      have hn := (spinSeparatingRoot_weights_injective Q).ne hpq
      exact (mul_eq_zero.mp (show
        ((star (spinSeparatingRoot Q))^p.val*(spinSeparatingRoot Q)^(Q-p.val)-
         (star (spinSeparatingRoot Q))^q.val*(spinSeparatingRoot Q)^(Q-q.val))*M p q=0 by
          linear_combination he)).resolve_left (sub_ne_zero.mpr hn)
  have hm := hM sourceMixer
  rw [hd] at hm
  have hc (p : Fin (Q+1)) : M p p=M 0 0 := by
    have he := congrFun (congrFun hm p) 0
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] at he
    apply (mul_left_cancel₀ (sourceSpinRepresentation_mixer_column_ne_zero Q p))
    calc
      _ = M p p*sourceSpinRepresentation Q sourceMixer p 0 := by ring
      _ = _ := he.symm
  rw [hd]
  ext p q
  by_cases hpq : p=q
  · subst q; simp [hc]
  · simp [hpq]

theorem source_spin_haar_schur (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M) =
      (Matrix.trace M / (Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) := by
  let H := matrixIntegral sourceHaar (conjugateOrbit (sourceSpinRepresentation Q) M)
  have hc := source_spin_commutant_scalar Q H (source_spin_haar_average_commutes Q M)
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

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Disjoint
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
  have hl := source_spin_commutant_scalar m (M*Mᴴ) (by
    intro g
    rw [← Matrix.mul_assoc,hM,Matrix.mul_assoc,hA,← Matrix.mul_assoc])
  have hr := source_spin_commutant_scalar n (Mᴴ*M) (by
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_RectangularAverage
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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Sandwich
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
-- module Solutions.OAIQ047_LA.Laughlin_Operators_WedgePairRepresentation
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

theorem wedgePairRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    wedgePairRepresentation Q g⁻¹ = (wedgePairRepresentation Q g)ᴴ := by
  ext i j
  simp only [wedgePairRepresentation,MonoidHom.coe_mk,OneHom.coe_mk,wedgePairMatrix,
    Matrix.conjTranspose_apply,sourceSpinRepresentation_inv,star_sub,star_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_GroupIntertwining
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

theorem fourBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    fourBodySpinRepresentation Q g⁻¹ = (fourBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,wedgePairRepresentation_inv]

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

theorem fourCoupledBasis_complex_complete (Q : ℕ) :
    (fourCoupledBasis Q).map Complex.ofReal * ((fourCoupledBasis Q).map Complex.ofReal)ᴴ = 1 := by
  rw [real_matrix_adjoint]
  exact real_matrix_inverse_complex _ _ (fourCoupledBasis_complete Q)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RetainedInclusions
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

theorem retainedFourInclusion_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D)
    (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    retainedFourInclusion Q D hQ r i n =
      (fourBodyCopy Q (oddPairDeficit r) D
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; omega)
        (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i : ℂ) := rfl

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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_HaarOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped Matrix

theorem source_unequal_spin_haar_zero (m n : ℕ) (hmn : m ≠ n)
    (M : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation m) (sourceSpinRepresentation n) M)=0 := by
  exact source_spin_intertwiner_zero m n hmn _
    (compact_rectangular_average_intertwines sourceHaar _ _
      (sourceSpinRepresentation_continuous m) (sourceSpinRepresentation_continuous n) M)

theorem source_equal_spin_haar_trace (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation Q) (sourceSpinRepresentation Q) M)=
      (Matrix.trace M/(Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :=
  source_spin_haar_schur Q M

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MultiplicityHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem retainedFourInclusion_adjoint_SU2 (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (g : SourceSU2) :
    (retainedFourInclusion Q D hQ r)ᴴ * fourBodySpinRepresentation Q g =
      sourceSpinRepresentation (fourSpinWeight Q D) g * (retainedFourInclusion Q D hQ r)ᴴ := by
  have h := congrArg Matrix.conjTranspose (retainedFourInclusion_SU2 Q D hQ r g⁻¹)
  simpa only [Matrix.conjTranspose_mul,fourBodySpinRepresentation_inv,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using h

theorem fourBody_haar_compressed (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (r : OddPairLabel D) (s : OddPairLabel E) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s =
    rectangularIntegral sourceHaar (rectangularOrbit
      (sourceSpinRepresentation (fourSpinWeight Q D)) (sourceSpinRepresentation (fourSpinWeight Q E))
      ((retainedFourInclusion Q D hD r)ᴴ * M * retainedFourInclusion Q E hE s)) := by
  change (retainedFourInclusion Q D hD r)ᴴ * entrywiseIntegral sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s = _
  rw [← integral_matrix_sandwich sourceHaar _
    (compact_conjugateOrbit_integrable sourceHaar _ (fourBodySpinRepresentation_continuous Q) M)]
  funext i j
  apply integral_congr_ae
  filter_upwards [] with g
  have hs := retainedFourInclusion_SU2 Q E hE s g⁻¹
  simp only [conjugateOrbit,rectangularOrbit]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,retainedFourInclusion_adjoint_SU2,
    Matrix.mul_assoc,Matrix.mul_assoc,hs]
  simp only [Matrix.mul_assoc]

theorem fourBody_haar_multiplicity_block (Q D : ℕ) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q D hD s =
      (Matrix.trace ((retainedFourInclusion Q D hD r)ᴴ*M*retainedFourInclusion Q D hD s) /
        (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_compressed,source_equal_spin_haar_trace]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

theorem fourBody_haar_unequal_spin (Q D E : ℕ) (hD : D+2 ≤ Q) (hE : E+2 ≤ Q)
    (hDE : D ≠ E) (r : OddPairLabel D) (s : OddPairLabel E)
    (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q E hE s = 0 := by
  rw [fourBody_haar_compressed]
  apply source_unequal_spin_haar_zero
  unfold fourSpinWeight
  omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_SignedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCouplingCoefficient_pair_swap (Q r j k : ℕ) (hr : r ≤ Q)
    (hor : Odd r) (hjk : j+k ≤ Q) :
    physicalCouplingCoefficient Q Q r (j+k) k = -physicalCouplingCoefficient Q Q r (j+k) j := by
  by_cases h : r ≤ j+k
  · rw [physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩,
      physicalCouplingCoefficient,dite_eq_left ⟨h,by omega,hjk,hjk⟩]
    have hp := pairCoupledTensor_antisymmetric Q r (j+k-r) hr hor ⟨j,by omega⟩ ⟨k,by omega⟩
    simpa only [pairCoupledTensor,Pi.smul_apply,smul_eq_mul,Nat.add_sub_cancel,Nat.add_sub_cancel_left] using hp
  · simp [physicalCouplingCoefficient,h]

theorem fourBodyCoefficient_swap (Q r D T p j k : ℕ) (hr : r ≤ Q) (hor : Odd r)
    (hjk : j+k ≤ Q) :
    fourBodyCoefficient Q r D T p k j = -fourBodyCoefficient Q r D T p j k := by
  unfold fourBodyCoefficient
  rw [Nat.add_comm k j]
  split_ifs
  · rw [physicalCouplingCoefficient_pair_swap Q r j k hr hor hjk]
    ring
  · simp

theorem fourWedgeUnit_dot (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (hjk : j < k) (v : Fin (2*Q-2+1) × WedgePairIndex Q → ℝ) :
    dotProduct v (fourWedgeUnit Q p j k) = v (⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
  classical
  simp only [dotProduct,fourWedgeUnit,mul_ite,mul_one,mul_zero]
  have he (i : Fin (2*Q-2+1) × WedgePairIndex Q) :
      (i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k) ↔
        i=(⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h3)))
    · intro h; subst i; exact ⟨rfl,rfl,rfl⟩
  simp_rw [he]
  simp

theorem fourWedgeUnit_zero (Q p j k : ℕ) (hkj : k ≤ j) : fourWedgeUnit Q p j k=0 := by
  funext i
  have h := i.2.property
  simp only [fourWedgeUnit,Pi.zero_apply]
  rw [ite_eq_right (by rintro ⟨_,hj,hk⟩; change i.2.val.1.val < i.2.val.2.val at h; omega)]

theorem fourBodyCopy_signed_at_level (Q r D T p j k : ℕ) (hor : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQ : T+2 ≤ Q) (hT : p+j+k=T) :
    dotProduct (fourBodyCopy Q r D (by omega) (by omega)
      (by unfold genericCoupledWeight; omega) (T-D)) (fourSignedUnit Q p j k) =
      fourBodyCoefficient Q r D T p j k := by
  rw [fourSignedUnit,dotProduct_sub]
  rcases lt_trichotomy j k with h | h | h
  · rw [fourWedgeUnit_dot Q p j k (by omega) (by omega) (by omega) h,
      fourWedgeUnit_zero Q p k j (by omega),dotProduct_zero,sub_zero]
    exact fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ hT
  · subst k
    rw [sub_self]
    have he := fourBodyCoefficient_swap Q r D T p j j (by omega) hor (by omega)
    linarith
  · rw [fourWedgeUnit_zero Q p j k (by omega),dotProduct_zero,zero_sub,
      fourWedgeUnit_dot Q p k j (by omega) (by omega) (by omega) h,
      fourBodyCopy_source_coefficient Q r D T hrD hDT hQ _ _ (by dsimp; omega),
      fourBodyCoefficient_swap Q r D T p j k (by omega) hor (by omega),neg_neg]

theorem fourBodyCopy_signed_off (Q r D n p j k : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hT : p+j+k ≠ D+n) :
    dotProduct (fourBodyCopy Q r D hr hA hB n) (fourSignedUnit Q p j k) = 0 := by
  have hz (j k : ℕ) (hT : p+j+k ≠ D+n) :
      dotProduct (fourBodyCopy Q r D hr hA hB n) (fourWedgeUnit Q p j k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [fourWedgeUnit]
    split_ifs with he
    · rw [fourBodyCopy_off Q r D n hr hrD hA hB i.1 i.2 (by omega),zero_mul]
    · exact mul_zero _
  rw [fourSignedUnit,dotProduct_sub,hz j k hT,hz k j (by omega),sub_self]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem trace_cross_outer {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (u v : I → ℝ) :
    Matrix.trace (Vᵀ * realOuter u v * W) =
      ∑ n, dotProduct (fun i => V i n) u * dotProduct (fun i => W i n) v := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,realOuter,
    dotProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourReal_complex (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    (retainedFourReal Q D hQ r).map Complex.ofReal = retainedFourInclusion Q D hQ r := rfl

theorem retainedFourReal_outer_trace (Q D T p j k q l i : ℕ) (hQ : D+2 ≤ Q)
    (hTQ : T+2 ≤ Q) (r s : OddPairLabel D) (hp : p+j+k=T) (hq : q+l+i=T) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ *
      realOuter (fourSignedUnit Q p j k) (fourSignedUnit Q q l i) * retainedFourReal Q D hQ s) =
      if D ≤ T then fourBodyCoefficient Q (oddPairDeficit r) D T p j k *
        fourBodyCoefficient Q (oddPairDeficit s) D T q l i else 0 := by
  rw [trace_cross_outer]
  by_cases hDT : D ≤ T
  · rw [ite_eq_left hDT]
    let n : Fin (fourSpinWeight Q D+1) := ⟨T-D,by unfold fourSpinWeight; omega⟩
    rw [Finset.sum_eq_single n]
    · change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ (T-D)) (fourSignedUnit Q p j k) *
        dotProduct (fourBodyCopy Q (oddPairDeficit s) D _ _ _ (T-D)) (fourSignedUnit Q q l i) = _
      rw [fourBodyCopy_signed_at_level Q (oddPairDeficit r) D T p j k
        (oddPairDeficit_odd r) (oddPairDeficit_le r) hDT hTQ hp,
        fourBodyCopy_signed_at_level Q (oddPairDeficit s) D T q l i
        (oddPairDeficit_odd s) (oddPairDeficit_le s) hDT hTQ hq]
    · intro m hm hmn
      change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ m.val) (fourSignedUnit Q p j k) * _ = 0
      rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D m.val p j k _ (oddPairDeficit_le r) _ _ (by
        intro he; apply hmn; apply Fin.ext; dsimp [n]; omega),zero_mul]
    · simp
  · rw [ite_eq_right hDT]
    apply Finset.sum_eq_zero
    intro n hn
    change dotProduct (fourBodyCopy Q (oddPairDeficit r) D _ _ _ n.val) (fourSignedUnit Q p j k) * _ = 0
    rw [fourBodyCopy_signed_off Q (oddPairDeficit r) D n.val p j k _ (oddPairDeficit_le r) _ _ (by omega),zero_mul]

theorem fourBodyTermMatrix_trace (Q D t : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hTQ : e.1+e.2.1+(f.1+f.2.1-t)+2 ≤ Q) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ * fourBodyTermMatrix Q t e f *
      retainedFourReal Q D hQ s) = -fourErrorEntry Q D (oddPairDeficit r) (oddPairDeficit s) t e f := by
  rw [fourBodyTermMatrix,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,
    retainedFourReal_outer_trace Q D (e.1+e.2.1+(f.1+f.2.1-t)) _ _ _ _ _ _ hQ hTQ r s rfl (by omega)]
  unfold fourErrorEntry
  dsimp only
  split_ifs <;> simp only [smul_eq_mul] <;> ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem trace_sandwich_list_sum {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (l : List (Matrix I I ℝ)) :
    Matrix.trace (Vᵀ*l.sum*W) = (l.map (fun M => Matrix.trace (Vᵀ*M*W))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.add_mul,Matrix.trace_add,ih]

theorem negative_list_sum {I : Type*} (l : List I) (a b : I → ℝ)
    (h : ∀ i ∈ l, a i = -b i) : (l.map a).sum = -(l.map b).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,h i (by simp),ih (fun j hj => h j (by simp [hj]))]
    ring

theorem source_fourBody_rows_support : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
    e.1+e.2.1+(f.1+f.2.1-row.1) ≤ 23 := by decide

theorem source_physical_fourBody_trace_identity (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    Matrix.trace ((retainedFourReal Q D hD r)ᵀ * physicalFourBodyMatrix Q * retainedFourReal Q D hD s) =
      physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) := by
  unfold physicalFourBodyMatrix physicalFourError
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro row hrow
  unfold fourErrorRow
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro e he
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro f hf
  exact fourBodyTermMatrix_trace Q D row.1 hD r s e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem trace_real_sandwich_complex {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (M : Matrix I I ℝ) :
    Matrix.trace ((V.map Complex.ofReal)ᴴ*M.map Complex.ofReal*W.map Complex.ofReal) =
      Complex.ofReal (Matrix.trace (Vᵀ*M*W)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.transpose_apply,Matrix.map_apply,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem physical_fourBody_haar_multiplicity (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *
        retainedFourInclusion Q D hD s =
      ((physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) : ℂ) / (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_multiplicity_block,← retainedFourReal_complex Q D hD r,
    ← retainedFourReal_complex Q D hD s,trace_real_sandwich_complex,
    source_physical_fourBody_trace_identity Q D hQ hD]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem realOuter_mulVec_row {I : Type*} [Fintype I] (u v w : I → ℝ) (i : I) :
    (realOuter u v *ᵥ w) i = u i * dotProduct w v := by
  simp only [Matrix.mulVec,dotProduct,realOuter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fourBodyTermMatrix_high_copy (Q r D t : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hT : e.1+e.2.1+(f.1+f.2.1-t) < D) :
    fourBodyTermMatrix Q t e f * fourBodyInclusion Q r D hr hA hB = 0 := by
  ext i n
  change (fourBodyTermMatrix Q t e f *ᵥ fourBodyCopy Q r D hr hA hB n.val) i=0
  rw [fourBodyTermMatrix,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [realOuter_mulVec_row,fourBodyCopy_signed_off Q r D n.val f.1 f.2.1
    (e.1+e.2.1-t) hr hrD hA hB (by omega),mul_zero,mul_zero]

theorem list_sum_mul_zero {I J K : Type*} [Fintype J]
    (l : List (Matrix I J ℝ)) (W : Matrix J K ℝ) (h : ∀ M ∈ l, M*W=0) : l.sum*W=0 := by
  induction l with
  | nil => simp
  | cons M l ih =>
    rw [List.sum_cons,Matrix.add_mul,h M (by simp),ih (fun A hA => h A (by simp [hA])),zero_add]

theorem physicalFourBodyMatrix_high_copy (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    physicalFourBodyMatrix Q * fourBodyInclusion Q r D hr hA hB = 0 := by
  unfold physicalFourBodyMatrix
  apply list_sum_mul_zero
  intro M hM
  rcases List.mem_map.mp hM with ⟨row,hrow,rfl⟩
  apply list_sum_mul_zero
  intro A hA'
  rcases List.mem_map.mp hA' with ⟨e,he,rfl⟩
  apply list_sum_mul_zero
  intro B hB'
  rcases List.mem_map.mp hB' with ⟨f,hf,rfl⟩
  exact fourBodyTermMatrix_high_copy Q r D row.1 hr hrD hA hB e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem real_matrix_mul_zero_complex {I J K : Type*} [Fintype J]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) (h : A*B=0) :
    A.map Complex.ofReal * B.map Complex.ofReal=0 := by
  ext i k
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) k)
  simpa only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul,
    Matrix.zero_apply,Complex.ofReal_zero] using he

theorem physicalFourBodyMatrix_high_wedge_copy (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    (physicalFourBodyMatrix Q).map Complex.ofReal * fourWedgeInclusion Q r D hr hA hB = 0 :=
  real_matrix_mul_zero_complex _ _ (physicalFourBodyMatrix_high_copy Q r D hr hrD hA hB hD)

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
      physicalFourBodyMatrix_high_wedge_copy Q r D hr hrD hA hB hD,Matrix.zero_mul,Matrix.mul_zero]
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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Hermitian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem list_double_sum_swap {I A : Type*} [AddCommMonoid A]
    (l k : List I) (f : I → I → A) :
    (l.map (fun i => (k.map (f i)).sum)).sum =
      (k.map (fun j => (l.map (fun i => f i j)).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,ih,List.sum_map_add]

theorem fourBodyTermMatrix_transpose (Q t : ℕ) (e f : ℕ × ℕ × ℤ) :
    (fourBodyTermMatrix Q t e f)ᵀ = fourBodyTermMatrix Q t f e := by
  ext i j
  simp only [fourBodyTermMatrix,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,realOuter]
  ring

theorem physicalFourBodyMatrix_transpose (Q : ℕ) :
    (physicalFourBodyMatrix Q)ᵀ = physicalFourBodyMatrix Q := by
  unfold physicalFourBodyMatrix
  simp only [Matrix.transpose_list_sum,List.map_map,Function.comp_def,fourBodyTermMatrix_transpose]
  congr 1
  apply List.map_congr_left
  intro row hrow
  exact list_double_sum_swap row.2.2 row.2.2 (fun e f => fourBodyTermMatrix Q row.1 f e)

theorem physicalFourBodyMatrix_hermitian (Q : ℕ) :
    ((physicalFourBodyMatrix Q).map Complex.ofReal)ᴴ = (physicalFourBodyMatrix Q).map Complex.ofReal := by
  rw [real_matrix_adjoint,physicalFourBodyMatrix_transpose]

theorem physicalFourBodyHaar_hermitian (Q : ℕ) :
    (matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)))ᴴ =
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) := by
  have he (g : SourceSU2) :
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g)ᴴ =
      conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g := by
    simp only [conjugateOrbit,Matrix.conjTranspose_mul,fourBodySpinRepresentation_inv,
      Matrix.conjTranspose_conjTranspose,physicalFourBodyMatrix_hermitian,Matrix.mul_assoc]
  ext i j
  change star (∫ g, conjugateOrbit (fourBodySpinRepresentation Q)
    ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i ∂sourceHaar) = _
  calc
    _ = ∫ g, star (conjugateOrbit (fourBodySpinRepresentation Q)
      ((physicalFourBodyMatrix Q).map Complex.ofReal) g j i) ∂sourceHaar := integral_conj.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact congrFun (congrFun (he g) i) j

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RetainedIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourIndex_column (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) (i : FourWedgeIndex Q) :
    (fourCoupledBasis Q i (retainedFourIndex Q D hQ r n) : ℂ) =
      retainedFourInclusion Q D hQ r i n := by
  have hd := retainedFourIndex_deficit Q D hQ r n
  change (fourBodyCopy Q (oddPairDeficit r) _ _ _ _ n.val i : ℂ) = _
  rw [retainedFourInclusion_column]
  unfold fourCoupledDeficit at hd
  simp only [hd]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RetainedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem sum_fourCoupled_retained {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : 25 ≤ Q) (f : FourCoupledIndex Q → A)
    (hz : ∀ s, 23 < fourCoupledDeficit s → f s=0) :
    (∑ s, f s) = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      ∑ n : Fin (fourSpinWeight Q (d.val+1)+1),
        f (retainedFourIndex Q (d.val+1) (by have := d.isLt; omega) r n) := by
  classical
  rw [Finset.sum_congr_set (s := {s : FourCoupledIndex Q | fourCoupledDeficit s ≤ 23})
    f (fun s => f s.val) (fun _ _ => rfl) (by intro s hs; exact hz s (by simpa using hs))]
  have h := Fintype.sum_equiv (retainedFourColumnsEquiv Q hQ)
    (fun x => f (retainedFourIndex Q (x.1.val+1) (by have := x.1.isLt; omega) x.2.1 x.2.2))
    (fun s => f s.val) (fun _ => rfl)
  convert (by simpa only [Fintype.sum_sigma,Fintype.sum_prod_type] using h.symm) using 1
  all_goals try with_reducible_and_instances rfl
  apply Fintype.sum_equiv (Equiv.refl _)
  intro s
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RetainedReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem fourBody_retained_reconstruction (Q : ℕ) (hQ : 25 ≤ Q)
    (A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ)
    (hz : ∀ s : FourCoupledIndex Q, 23 < fourCoupledDeficit s →
      A *ᵥ (fun i => (fourCoupledBasis Q i s : ℂ)) = 0) :
    A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      A * retainedFourInclusion Q (d.val+1) (by omega) r *
        (retainedFourInclusion Q (d.val+1) (by omega) r)ᴴ := by
  classical
  have hc : A = (A * (fourCoupledBasis Q).map Complex.ofReal) *
      ((fourCoupledBasis Q).map Complex.ofReal)ᴴ := by
    rw [Matrix.mul_assoc,fourCoupledBasis_complex_complete,Matrix.mul_one]
  ext i j
  have he := congrFun (congrFun hc i) j
  simp only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply] at he
  rw [he]
  rw [sum_fourCoupled_retained Q hQ
    (fun s => (∑ k, A i k*(fourCoupledBasis Q k s : ℂ))*star (fourCoupledBasis Q j s : ℂ))
    (by intro s hs; have h := congrFun (hz s hs) i; change (∑ k, A i k*_) = 0 at h; rw [h,zero_mul])]
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,retainedFourIndex_column]

theorem physicalFourBodyHaar_high_column (Q : ℕ) (s : FourCoupledIndex Q)
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

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_GlobalHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation Fock
open scoped BigOperators Matrix

theorem physicalFourBodyHaar_retained_sum_oai (Q : ℕ) (hQ : 25 ≤ Q) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) •
      fourCopyOperator Q (d.val+1) (by omega)
        (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  let A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := matrixIntegral sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal))
  let U (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q (d.val+1)+1)) ℂ :=
    retainedFourInclusion Q (d.val+1) (by omega) r
  have hr : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), A*U d r*(U d r)ᴴ :=
    fourBody_retained_reconstruction Q hQ A (physicalFourBodyHaar_high_column Q)
  have hl : A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1), U d r*(U d r)ᴴ*A := by
    have ha : Aᴴ=A := physicalFourBodyHaar_hermitian Q
    have h := congrArg Matrix.conjTranspose hr
    simpa only [Matrix.conjTranspose_sum,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,ha,← Matrix.mul_assoc] using h
  have he (d : Fin 23) (r : OddPairLabel (d.val+1)) :
      U d r*(U d r)ᴴ*A = ∑ s : OddPairLabel (d.val+1),
        ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
          ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • (U d r*(U d s)ᴴ) := by
    calc
      _ = ∑ e : Fin 23, ∑ s : OddPairLabel (e.val+1),
          U d r*((U d r)ᴴ*A*U e s)*(U e s)ᴴ := by
        conv_lhs => rw [hr]
        simp only [Matrix.mul_sum,Matrix.mul_assoc]
      _ = ∑ s : OddPairLabel (d.val+1),
          U d r*((U d r)ᴴ*A*U d s)*(U d s)ᴴ := by
        apply Finset.sum_eq_single d
        · intro e he hed
          apply Finset.sum_eq_zero
          intro s hs
          have hz : (U d r)ᴴ*A*U e s=0 :=
            fourBody_haar_unequal_spin Q (d.val+1) (e.val+1) (by omega) (by omega)
              (by intro hv; exact hed (Fin.ext (by omega))) r s _
          rw [hz,Matrix.mul_zero,Matrix.zero_mul]
        · simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        have hb : (U d r)ᴴ*A*U d s =
            ((physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s) : ℂ) /
              ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) • 1 :=
          physical_fourBody_haar_multiplicity Q (d.val+1) hQ (by omega) r s
        rw [hb,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  change A = _
  rw [hl]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [he,fourCopyOperator,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  simp only [div_eq_mul_inv,one_mul,mul_comm]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_oai := @OAI.Laughlin.Spin.physicalFourBodyHaar_retained_sum_oai
