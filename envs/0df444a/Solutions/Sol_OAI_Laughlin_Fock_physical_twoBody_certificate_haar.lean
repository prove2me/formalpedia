-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_twoBody_certificate_haar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:33.671209+00:00
-- url     : https://prove2.me/submissions/bad742e1-4a3c-4aa2-b1ec-105dd7d481c2

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Definitions.Def_OAIQ047L003

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_Scaling
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

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

end Laughlin.Fock

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

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbitalRotation_mul (Q : ℕ) (g h : SourceSU2) :
    (orbitalRotation Q g).comp (orbitalRotation Q h) = orbitalRotation Q (g*h) := by
  apply LinearMap.ext
  intro v
  funext i
  change (sourceSpinRepresentation Q g *ᵥ (sourceSpinRepresentation Q h *ᵥ v)) i = _
  rw [Matrix.mulVec_mulVec,← map_mul]
  rfl

theorem orbitalRotation_one (Q : ℕ) : orbitalRotation Q 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext i
  simp [orbitalRotation]

theorem exteriorRotation_mul (Q : ℕ) (g h : SourceSU2) (x : Space Q) :
    exteriorRotation Q g (exteriorRotation Q h x) = exteriorRotation Q (g*h) x := by
  change ((ExteriorAlgebra.map (orbitalRotation Q g)).comp
    (ExteriorAlgebra.map (orbitalRotation Q h))) x = _
  rw [ExteriorAlgebra.map_comp_map,orbitalRotation_mul]
  rfl

theorem exteriorRotation_one (Q : ℕ) (x : Space Q) : exteriorRotation Q 1 x = x := by
  unfold exteriorRotation
  rw [orbitalRotation_one,ExteriorAlgebra.map_id]
  rfl

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

theorem create_exteriorRotation (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) (x : Space Q) :
    exteriorRotation Q g (create i x) =
      ∑ j, sourceSpinRepresentation Q g j i • create j (exteriorRotation Q g x) := by
  change ExteriorAlgebra.map (orbitalRotation Q g) (ExteriorAlgebra.ι ℂ (mode i)*x) = _
  rw [map_mul,ExteriorAlgebra.map_apply_ι,orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  have he : orbitalRotation Q g (mode i) j = sourceSpinRepresentation Q g j i := by
    simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [he]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_ScalingWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_product (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    (∏ a : Fin n, d (Set.powersetCard.ofFinEmbEquiv.symm A a)) = ∏ i ∈ A.val, d i := by
  apply Finset.prod_bij (fun a _ => Set.powersetCard.ofFinEmbEquiv.symm A a)
  · intro a ha
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A _).mp ⟨a,rfl⟩
  · intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm A).injective hab
  · intro b hb
    obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A b).mpr hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a ha
    rfl

theorem exteriorScaling_occupation_sector (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    exteriorScaling Q d (occupationBasis Q A.val) =
      (∏ i ∈ A.val, d i) • occupationBasis Q A.val := by
  have h := exteriorScaling_wedge Q n d (Set.powersetCard.ofFinEmbEquiv.symm A)
  rw [occupation_product Q n d A] at h
  simpa only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem exteriorScaling_occupation (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Finset (Fin (Q+1))) :
    exteriorScaling Q d (occupationBasis Q A) = (∏ i ∈ A, d i) • occupationBasis Q A := by
  exact exteriorScaling_occupation_sector Q A.card d ⟨A,rfl⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) : annihilate i (occupationBasis Q A) = 0 := by
  let d : Fin (Q+1) → ℂ := fun j => if j = i then 0 else 1
  have hd : (∏ j ∈ A, d j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [d, show j ≠ i by intro h; subst j; exact hi hj]
  have h := annihilate_scaling Q d i (occupationBasis Q A)
  rw [exteriorScaling_occupation,hd,one_smul] at h
  simpa [d] using h

theorem create_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) : create i (occupationBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q+1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint
    (Pi.basisFun ℂ (Fin (Q+1)))
    (⟨{i},Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q+1)) 1)
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) hd
  change occupationBasis Q {i} * occupationBasis Q A = 0 at h
  rw [occupation_singleton] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

theorem insertionSign_sq (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A * insertionSign Q i A = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    create i (occupationBasis Q A) = insertionSign Q i A • occupationBasis Q (insert i A) := by
  simpa [insertionSign,hi] using (create_unoccupied_sign Q i A hi).choose_spec.2

theorem annihilate_insert (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    annihilate i (occupationBasis Q (insert i A)) = insertionSign Q i A • occupationBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (occupationBasis Q A)
  change annihilate i (create i (occupationBasis Q A)) +
    create i (annihilate i (occupationBasis Q A)) = (if i = i then (1 : ℂ) else 0) • occupationBasis Q A at h
  rw [create_unoccupied Q i A hi, map_smul, annihilate_unoccupied Q i A hi, map_zero] at h
  simp only [add_zero, ite_true, one_smul] at h
  have he := congrArg (fun x => insertionSign Q i A • x) h
  simpa only [smul_smul, insertionSign_sq, one_smul] using he

theorem annihilate_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) :
    annihilate i (occupationBasis Q A) =
      insertionSign Q i (A.erase i) • occupationBasis Q (A.erase i) := by
  simpa only [Finset.insert_erase hi] using
    annihilate_insert Q i (A.erase i) (Finset.notMem_erase i A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (annihilate i x) A =
      if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A) := by
  let e : ℂ := if i ∈ A then 0 else insertionSign Q i A
  have h : ((occupationBasis Q).coord A).comp (annihilate i) =
      e • (occupationBasis Q).coord (insert i A) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (annihilate i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (insert i A)
    by_cases hiB : i ∈ B
    · rw [annihilate_occupied Q i B hiB, map_smul, Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · have hBA : B.erase i ≠ A := by intro h; rw [← h] at hiA; exact Finset.notMem_erase i B hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hBA]
      · by_cases hBA : B = insert i A
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have herase : B.erase i ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.insert_erase hiB]
          simp [e,hiA,Module.Basis.repr_self,herase,hBA]
    · rw [annihilate_unoccupied Q i B hiB]
      have hBA : B ≠ insert i A := by intro h; subst B; simp at hiB
      simp [e,Module.Basis.repr_self,hBA]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

theorem create_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (create i x) A =
      if i ∈ A then insertionSign Q i (A.erase i) * (occupationBasis Q).repr x (A.erase i) else 0 := by
  let e : ℂ := if i ∈ A then insertionSign Q i (A.erase i) else 0
  have h : ((occupationBasis Q).coord A).comp (create i) =
      e • (occupationBasis Q).coord (A.erase i) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (create i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (A.erase i)
    by_cases hiB : i ∈ B
    · rw [create_occupied Q i B hiB]
      have hBA : B ≠ A.erase i := by intro h; rw [h] at hiB; exact Finset.notMem_erase i A hiB
      simp [e,Module.Basis.repr_self,hBA]
    · rw [create_unoccupied Q i B hiB,map_smul,Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · by_cases hBA : B = A.erase i
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have hins : insert i B ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.erase_insert hiB]
          simp [e,hiA,Module.Basis.repr_self,hBA,hins]
      · have hins : insert i B ≠ A := by intro h; rw [← h] at hiA; simp at hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hins]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_ContractionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Adjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem insertionSign_star (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    star (insertionSign Q i A) = insertionSign Q i A := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_annihilate_adjoint (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q (create i x) y = occupationInner Q x (annihilate i y) := by
  let f : Finset (Fin (Q+1)) → ℂ := fun A =>
    insertionSign Q i (A.erase i) *
      (star ((occupationBasis Q).repr x (A.erase i)) * (occupationBasis Q).repr y A)
  have hl : occupationInner Q (create i x) y =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
    rw [Finset.sum_filter]
    unfold occupationInner
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hi : i ∈ A <;>
      simp only [f, create_coordinate, hi, ite_true, ite_false, star_mul,
        insertionSign_star, star_zero, zero_mul, mul_comm, mul_left_comm]
  rw [hl, ← sum_unoccupied_insert i f, Finset.sum_filter]
  unfold occupationInner
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hi : i ∈ A <;>
    simp only [f, hi, annihilate_coordinate, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, Finset.erase_insert, zero_mul, mul_assoc, mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Hamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairCreate_pair_adjoint (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y : Space Q) :
    occupationInner Q (pairCreateEnd Q c x) y = occupationInner Q x (pairEnd Q c y) := by
  simp only [pairCreateEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,create_annihilate_adjoint]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PositiveFockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_VectorAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem vectorAnnihilate_sum (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q v x = ∑ i, star (v i) • annihilate i x := by
  simp only [vectorAnnihilate,orbitalDual,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,annihilate]

theorem vectorCreate_sum (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    ExteriorAlgebra.ι ℂ v*x = ∑ i, v i • create i x := by
  conv_lhs => rw [orbital_sum_modes Q v]
  simp only [map_sum,map_smul,Finset.sum_mul,smul_mul_assoc]
  rfl

theorem vectorCreate_adjoint (Q : ℕ) (v : Orbital Q) (x y : Space Q) :
    occupationInner Q (ExteriorAlgebra.ι ℂ v*x) y =
      occupationInner Q x (vectorAnnihilate Q v y) := by
  rw [vectorCreate_sum,vectorAnnihilate_sum]
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,create_annihilate_adjoint]

theorem orbitalDual_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) :
    (orbitalDual Q (orbitalRotation Q g v)).comp (orbitalRotation Q g) = orbitalDual Q v := by
  apply LinearMap.ext
  intro w
  simp only [orbitalDual,LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  change star (sourceSpinRepresentation Q g *ᵥ v) ⬝ᵥ (sourceSpinRepresentation Q g *ᵥ w) = star v ⬝ᵥ w
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff'.mp (sourceSpinRepresentation_unitary Q g)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [hu,Matrix.vecMul_one]

theorem vectorAnnihilate_rotation (Q : ℕ) (g : SourceSU2) (v : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q (orbitalRotation Q g v) (exteriorRotation Q g x) =
      exteriorRotation Q g (vectorAnnihilate Q v x) := by
  unfold vectorAnnihilate exteriorRotation
  rw [contraction_map,orbitalDual_rotation]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_left (Q : ℕ) (x y z : Space Q) :
    occupationInner Q (x+y) z = occupationInner Q x z+occupationInner Q y z := by
  simp [occupationInner,add_mul,Finset.sum_add_distrib]

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

theorem occupationInner_scalar_wedge_zero (Q : ℕ) (r : ℂ) (v : Orbital Q) (x : Space Q) :
    occupationInner Q (algebraMap ℂ (Space Q) r) (ExteriorAlgebra.ι ℂ v*x) = 0 := by
  have h := congrArg star (vectorCreate_adjoint Q v x (algebraMap ℂ (Space Q) r))
  rw [occupationInner_star,occupationInner_star] at h
  simpa [vectorAnnihilate,occupationInner] using h

theorem exteriorRotation_ι_mul (Q : ℕ) (g : SourceSU2) (v : Orbital Q) (x : Space Q) :
    exteriorRotation Q g (ExteriorAlgebra.ι ℂ v*x) =
      ExteriorAlgebra.ι ℂ (orbitalRotation Q g v)*exteriorRotation Q g x := by
  simp [exteriorRotation]

theorem occupationInner_scalar_rotation (Q : ℕ) (g : SourceSU2) (r : ℂ) (y : Space Q) :
    occupationInner Q (algebraMap ℂ (Space Q) r) (exteriorRotation Q g y) =
      occupationInner Q (algebraMap ℂ (Space Q) r) y := by
  induction y using CliffordAlgebra.left_induction with
  | algebraMap s => simp
  | add x y hx hy => simp only [map_add,occupationInner_add_right,hx,hy]
  | ι_mul x v hx => rw [exteriorRotation_ι_mul,occupationInner_scalar_wedge_zero,occupationInner_scalar_wedge_zero]

theorem exteriorRotation_unitary (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g x) (exteriorRotation Q g y) = occupationInner Q x y := by
  revert y
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    intro y
    simp only [AlgHom.commutes]
    exact occupationInner_scalar_rotation Q g r y
  | add x z hx hz =>
    intro y
    simp only [map_add,occupationInner_add_left,hx,hz]
  | ι_mul x v hx =>
    intro y
    rw [exteriorRotation_ι_mul,vectorCreate_adjoint,vectorAnnihilate_rotation,hx,vectorCreate_adjoint]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_FamilyCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem occupationInner_basis_left (Q : ℕ) (A : Finset (Fin (Q+1))) (x : Space Q) :
    occupationInner Q (occupationBasis Q A) x = (occupationBasis Q).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_ext_right (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q z x = occupationInner Q z y) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  simpa only [occupationInner_basis_left] using h (occupationBasis Q A)

theorem occupationInner_rotation_left (Q : ℕ) (g : SourceSU2) (x y : Space Q) :
    occupationInner Q (exteriorRotation Q g⁻¹ x) y =
      occupationInner Q x (exteriorRotation Q g y) := by
  have h := exteriorRotation_unitary Q g (exteriorRotation Q g⁻¹ x) y
  rw [exteriorRotation_mul,mul_inv_cancel,exteriorRotation_one] at h
  exact h.symm

theorem exteriorFamily_contraction_rotation {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (v : I → Space Q) (minus : I → Module.End ℂ (Space Q))
    (ha : ∀ i x y, occupationInner Q (v i*x) y = occupationInner Q x (minus i y))
    (hv : ∀ g i, exteriorRotation Q g (v i) = ∑ j, ρ g j i • v j)
    (g : SourceSU2) (i : I) (x : Space Q) :
    minus i (exteriorRotation Q g x) = ∑ j, ρ g i j • exteriorRotation Q g (minus j x) := by
  apply occupationInner_ext_right Q
  intro y
  rw [← ha,← occupationInner_rotation_left,map_mul,hv]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,occupationInner_smul_left,
    ha,hρ,Matrix.conjTranspose_apply,star_star,occupationInner_sum_right,occupationInner_smul_right,
    occupationInner_rotation_left]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_LoweringAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem choose_lowering (Q i : ℕ) (hi : 0 < i) (hiQ : i ≤ Q+1) :
    ((Q : ℝ)-(i : ℝ)+1) * (Q.choose (i-1) : ℝ) =
      (i : ℝ) * (Q.choose i : ℝ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hk : k ≤ Q := by omega
  have h := Nat.choose_succ_right_eq Q k
  have hc := congrArg (fun x : ℕ => (x : ℝ)) h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at hc
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  nlinarith only [hc]

theorem pairPolynomialCoefficient_lowering (Q i j : ℕ)
    (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) +
    (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      ((i : ℝ)+(j : ℝ)-1)*pairPolynomialCoefficient Q i j := by
  have left : (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) =
      (i : ℝ)*((i : ℝ)-1-(j : ℝ))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hi : 0 < i
    · rw [ite_eq_left hi]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
      calc
        _ = ((i : ℝ)-1-(j : ℝ))*(Q.choose j : ℝ)*
          (((Q : ℝ)-(i : ℝ)+1)*(Q.choose (i-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q i hi (by omega)]; ring
    · have hz : i = 0 := by omega
      simp [hz]
  have right : (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      (j : ℝ)*((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hj : 0 < j
    · rw [ite_eq_left hj]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      calc
        _ = ((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*
          (((Q : ℝ)-(j : ℝ)+1)*(Q.choose (j-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q j hj (by omega)]; ring
    · have hz : j = 0 := by omega
      simp [hz]
  rw [left, right]
  unfold pairPolynomialCoefficient
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairCoefficient_choose (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairCoefficient Q p x y = if x.val+y.val = p+1 then
      ((x.val : ℝ)-(y.val : ℝ)) *
        Real.sqrt ((Q.choose x.val : ℝ)*(Q.choose y.val : ℝ) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))) else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs
  · have hr : (((Q.descFactorial x.val : ℝ)*(Q.descFactorial y.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(x.val.factorial : ℝ)*(y.val.factorial : ℝ))) / 2 =
      (Q.choose x.val : ℝ)*(Q.choose y.val : ℝ)/(2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
        simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
        field_simp
    have hs := congrArg Real.sqrt hr
    rw [Real.sqrt_div (by positivity) (2 : ℝ)] at hs
    rw [← hs]
    ring
  · rfl

theorem pairCoefficient_polynomial_weight (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    pairCoefficient Q p x y * Real.sqrt (Q.choose x.val : ℝ) *
      Real.sqrt (Q.choose y.val : ℝ) * Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) =
        if x.val+y.val = p+1 then pairPolynomialCoefficient Q x.val y.val else 0 := by
  have hd : Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
    positivity
  rw [pairCoefficient_choose Q p hQ hp]
  split_ifs
  · rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    unfold pairPolynomialCoefficient
    have hx := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose x.val by positivity)
    have hy := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose y.val by positivity)
    field_simp
    calc
      _ = ((x.val : ℝ)-(y.val : ℝ)) * (Real.sqrt (Q.choose x.val : ℝ))^2 *
        (Real.sqrt (Q.choose y.val : ℝ))^2 := by ring
      _ = _ := by rw [hx,hy]
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem rawPairState_lowering (Q p i j : ℕ) (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    lowerPair Q (rawPairState Q p) i j = (p+1 : ℕ)*rawPairState Q (p+1) i j := by
  by_cases h : i+j = p+2
  · have hx : 0 < i → i-1+j = p+1 := by omega
    have hy : 0 < j → i+(j-1) = p+1 := by omega
    have hr : ((i : ℝ)+(j : ℝ)-1) = (p+1 : ℕ) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at hc ⊢
      linarith
    have ha := pairPolynomialCoefficient_lowering Q i j hiQ hjQ
    rw [hr] at ha
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simpa [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc] using ha
  · have hx : 0 < i → i-1+j ≠ p+1 := by omega
    have hy : 0 < j → i+(j-1) ≠ p+1 := by omega
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simp [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_NormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairNormalization_pos (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    0 < pairNormalization Q p := by
  unfold pairNormalization
  apply Real.sqrt_pos.mpr
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
  positivity

theorem pairNormalization_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    ((p : ℝ)+1) / pairNormalization Q p =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ)) / pairNormalization Q (p+1) := by
  have hdn := pairNormalization_pos Q (p+1) hQ (by omega)
  have hd := pairNormalization_pos Q p hQ (by omega)
  apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hdn)).mpr
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq (2*Q-2) p)
  push_cast at hc
  have he : (((p : ℝ)+1)*pairNormalization Q (p+1))^2 =
      (Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p)^2 := by
    unfold pairNormalization
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    linear_combination (2*(Q : ℝ)*((p : ℝ)+1))*hc
  have hn₁ : 0 ≤ ((p : ℝ)+1)*pairNormalization Q (p+1) := by positivity
  have hn₂ : 0 ≤ Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p := by positivity
  nlinarith only [he,hn₁,hn₂]

theorem lowerPair_div (Q : ℕ) (f : ℕ → ℕ → ℝ) (d : ℝ) (i j : ℕ) :
    lowerPair Q (fun i j => f i j / d) i j = lowerPair Q f i j / d := by
  unfold lowerPair
  split_ifs <;> ring

theorem normalizedPairState_lowering (Q p i j : ℕ) (hQ : 0 < Q)
    (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q p) i j =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j := by
  unfold normalizedPairState
  rw [lowerPair_div, rawPairState_lowering Q p i j hi hj]
  push_cast
  calc
    _ = (((p : ℝ)+1)/pairNormalization Q p)*rawPairState Q (p+1) i j := by ring
    _ = _ := by rw [pairNormalization_ratio Q p hQ hp]; ring

theorem normalizedPairState_eq_coefficients (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    normalizedPairState Q p x.val y.val = pairCoefficient Q p x y *
      Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) := by
  unfold normalizedPairState rawPairState
  apply (div_eq_iff (ne_of_gt (pairNormalization_pos Q p hQ hp))).mpr
  exact (pairCoefficient_polynomial_weight Q p hQ hp x y).symm

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sqrt_choose_step (A p : ℕ) (hp : p < A) :
    ladder A p * Real.sqrt (A.choose (p+1) : ℝ) =
      (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose (p+1) : ℝ))^2 =
      ((A-p : ℕ)*Real.sqrt (A.choose p : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have h₁ : 0 ≤ ladder A p * Real.sqrt (A.choose (p+1) : ℝ) := by
    exact mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have h₂ : 0 ≤ (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by positivity
  nlinarith

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialRaising
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairPolynomialCoefficient_raising (Q i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    ((i : ℝ)+1)*pairPolynomialCoefficient Q (i+1) j +
      ((j : ℝ)+1)*pairPolynomialCoefficient Q i (j+1) =
    (2*(Q : ℝ)-i-j-1)*pairPolynomialCoefficient Q i j := by
  have hx := Spin.choose_step_real Q i hi
  have hy := Spin.choose_step_real Q j hj
  rw [Nat.cast_sub hi] at hx
  rw [Nat.cast_sub hj] at hy
  unfold pairPolynomialCoefficient
  push_cast
  linear_combination
    ((i : ℝ)+1-j)*(Q.choose j : ℝ)*hx +
    ((i : ℝ)-j-1)*(Q.choose i : ℝ)*hy

theorem rawPairState_raising (Q p i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (rawPairState Q (p+1)) i j =
      (2*(Q : ℝ)-2-p)*rawPairState Q p i j := by
  have hs : i+1+j = p+1+1 ↔ i+j=p+1 := by omega
  have ht : i+(j+1) = p+1+1 ↔ i+j=p+1 := by omega
  unfold raisePair rawPairState
  by_cases h : i+j=p+1
  · rw [ite_eq_left (hs.mpr h),ite_eq_left (ht.mpr h),ite_eq_left h]
    have hc : (i : ℝ)+j = (p : ℝ)+1 := by exact_mod_cast h
    rw [pairPolynomialCoefficient_raising Q i j hi hj]
    congr 1
    linarith
  · simp only [ite_eq_right h,ite_eq_right (mt hs.mp h),ite_eq_right (mt ht.mp h),mul_zero,add_zero]

theorem pairNormalization_raising_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    (2*(Q : ℝ)-2-p)/pairNormalization Q (p+1) =
      Spin.ladder (2*Q-2) p / pairNormalization Q p := by
  have h := Spin.sqrt_choose_step (2*Q-2) p hp
  have hc : ((2*Q-2-p : ℕ) : ℝ) = 2*(Q : ℝ)-2-p := by
    rw [Nat.cast_sub (by omega : p ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  rw [hc] at h
  have hn₀ := ne_of_gt (pairNormalization_pos Q p hQ (by omega))
  have hn₁ := ne_of_gt (pairNormalization_pos Q (p+1) hQ (by omega))
  apply (div_eq_div_iff hn₁ hn₀).mpr
  unfold pairNormalization
  simp only [Real.sqrt_mul (by positivity : 0 ≤ 2*(Q : ℝ))]
  linear_combination -(Real.sqrt (2*(Q : ℝ)))*h

theorem normalizedPairState_raising (Q p i j : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (normalizedPairState Q (p+1)) i j =
      Spin.ladder (2*Q-2) p * normalizedPairState Q p i j := by
  have hdiv : raisePair (normalizedPairState Q (p+1)) i j =
      raisePair (rawPairState Q (p+1)) i j / pairNormalization Q (p+1) := by
    unfold normalizedPairState raisePair
    ring
  rw [hdiv,rawPairState_raising Q p i j hi hj]
  unfold normalizedPairState
  calc
    _ = ((2*(Q : ℝ)-2-p)/pairNormalization Q (p+1))*rawPairState Q p i j := by ring
    _ = _ := by rw [pairNormalization_raising_ratio Q p hQ hp]; ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem ladder_weight_previous (Q : ℕ) (x : Fin (Q+1)) (hx : 0 < x.val) :
    ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ) =
      ((Q : ℝ)-x.val+1)*Real.sqrt (Q.choose (x.val-1) : ℝ) := by
  have h := sqrt_choose_step Q (x.val-1) (by omega)
  rw [show x.val-1+1=x.val by omega] at h
  have hc : ((Q-(x.val-1) : ℕ) : ℝ) = (Q : ℝ)-x.val+1 := by
    rw [Nat.cast_sub (by omega : x.val-1 ≤ Q),Nat.cast_sub (by omega : 1 ≤ x.val)]
    push_cast; ring
  rwa [hc] at h

theorem pairTensorLower_weight (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      lowerPair Q (normalizedPairState Q p) x.val y.val := by
  have hl :
      (if h : 0 < x.val then ladder Q (x.val-1)*pairCoefficient Q p ⟨x.val-1,by omega⟩ y else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < x.val then ((Q : ℝ)-x.val+1)*normalizedPairState Q p (x.val-1) y.val else 0) := by
    by_cases hx : 0 < x.val
    · rw [dite_eq_left hx,ite_eq_left hx,normalizedPairState_eq_coefficients Q p hQ hp ⟨x.val-1,by omega⟩ y]
      calc
        _ = pairCoefficient Q p ⟨x.val-1,by omega⟩ y * Real.sqrt (Q.choose y.val : ℝ)*
          (ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q x hx]; ring
    · simp only [dite_eq_right hx,ite_eq_right hx,zero_mul]
  have hr :
      (if h : 0 < y.val then ladder Q (y.val-1)*pairCoefficient Q p x ⟨y.val-1,by omega⟩ else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < y.val then ((Q : ℝ)-y.val+1)*normalizedPairState Q p x.val (y.val-1) else 0) := by
    by_cases hy : 0 < y.val
    · rw [dite_eq_left hy,ite_eq_left hy,normalizedPairState_eq_coefficients Q p hQ hp x ⟨y.val-1,by omega⟩]
      calc
        _ = pairCoefficient Q p x ⟨y.val-1,by omega⟩ * Real.sqrt (Q.choose x.val : ℝ)*
          (ladder Q (y.val-1)*Real.sqrt (Q.choose y.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q y hy]; ring
    · simp only [dite_eq_right hy,ite_eq_right hy,zero_mul]
  unfold pairTensorLower lowerPair
  rw [add_mul,add_mul,hl,hr]

theorem pairCoefficient_tensor_lowering (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y = ladder (2*Q-2) p * pairCoefficient Q (p+1) x y := by
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  apply (mul_right_cancel₀ hy)
  apply (mul_right_cancel₀ hx)
  have he := pairTensorLower_weight Q p hQ (by omega) x y
  rw [normalizedPairState_lowering Q p x.val y.val hQ hp (by omega) (by omega),
    normalizedPairState_eq_coefficients Q (p+1) hQ (by omega) x y] at he
  unfold ladder
  linear_combination he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorRaise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem ladder_weight_next (Q : ℕ) (x : Fin (Q+1)) (hx : x.val < Q) :
    ladder Q x.val*Real.sqrt (Q.choose x.val : ℝ) =
      ((x.val : ℝ)+1)*Real.sqrt (Q.choose (x.val+1) : ℝ) := by
  have h₀ : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have h₁ : Real.sqrt (Q.choose (x.val+1) : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val+1 ≤ Q)
  exact (div_eq_div_iff h₁ h₀).mp (ladder_div_sqrt_choose Q x.val hx)

theorem normalizedPairState_out_left (Q p i j : ℕ) (hi : Q < i) :
    normalizedPairState Q p i j = 0 := by
  simp [normalizedPairState,rawPairState,pairPolynomialCoefficient,Nat.choose_eq_zero_of_lt hi]

theorem normalizedPairState_out_right (Q p i j : ℕ) (hj : Q < j) :
    normalizedPairState Q p i j = 0 := by
  simp [normalizedPairState,rawPairState,pairPolynomialCoefficient,Nat.choose_eq_zero_of_lt hj]

theorem pairTensorRaise_weight (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorRaise Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      raisePair (normalizedPairState Q p) x.val y.val := by
  have hl :
      (if h : x.val < Q then ladder Q x.val*pairCoefficient Q p ⟨x.val+1,by omega⟩ y else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      ((x.val : ℝ)+1)*normalizedPairState Q p (x.val+1) y.val := by
    by_cases hx : x.val < Q
    · rw [dite_eq_left hx,normalizedPairState_eq_coefficients Q p hQ hp ⟨x.val+1,by omega⟩ y]
      calc
        _ = pairCoefficient Q p ⟨x.val+1,by omega⟩ y * Real.sqrt (Q.choose y.val : ℝ)*
          (ladder Q x.val*Real.sqrt (Q.choose x.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_next Q x hx]; ring
    · rw [dite_eq_right hx,normalizedPairState_out_left Q p (x.val+1) y.val (by omega)]
      ring
  have hr :
      (if h : y.val < Q then ladder Q y.val*pairCoefficient Q p x ⟨y.val+1,by omega⟩ else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      ((y.val : ℝ)+1)*normalizedPairState Q p x.val (y.val+1) := by
    by_cases hy : y.val < Q
    · rw [dite_eq_left hy,normalizedPairState_eq_coefficients Q p hQ hp x ⟨y.val+1,by omega⟩]
      calc
        _ = pairCoefficient Q p x ⟨y.val+1,by omega⟩ * Real.sqrt (Q.choose x.val : ℝ)*
          (ladder Q y.val*Real.sqrt (Q.choose y.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_next Q y hy]; ring
    · rw [dite_eq_right hy,normalizedPairState_out_right Q p x.val (y.val+1) (by omega)]
      ring
  unfold pairTensorRaise raisePair
  rw [add_mul,add_mul,hl,hr]

theorem pairCoefficient_tensor_raising (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorRaise Q (p+1) x y = ladder (2*Q-2) p * pairCoefficient Q p x y := by
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  apply (mul_right_cancel₀ hy)
  apply (mul_right_cancel₀ hx)
  have he := pairTensorRaise_weight Q (p+1) hQ (by omega) x y
  rw [normalizedPairState_raising Q p x.val y.val hQ hp (by omega) (by omega),
    normalizedPairState_eq_coefficients Q p hQ (by omega) x y] at he
  linear_combination he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem rawPairState_highest (Q i j : ℕ) :
    raisePair (rawPairState Q 0) i j = 0 := by
  by_cases h : i+j=0
  · have hi : i=0 := by omega
    have hj : j=0 := by omega
    simp [hi,hj,raisePair,rawPairState,pairPolynomialCoefficient]
  · have hi : i+1+j ≠ 0+1 := by omega
    have hj : i+(j+1) ≠ 0+1 := by omega
    simp [raisePair,rawPairState,hi,hj]

theorem normalizedPairState_highest (Q i j : ℕ) :
    raisePair (normalizedPairState Q 0) i j = 0 := by
  have he : raisePair (normalizedPairState Q 0) i j =
      raisePair (rawPairState Q 0) i j / pairNormalization Q 0 := by
    unfold raisePair normalizedPairState; ring
  rw [he,rawPairState_highest,zero_div]

theorem rawPairState_past_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    rawPairState Q (2*Q-2+1) i j = 0 := by
  by_cases h : i+j=2*Q-2+1+1
  · have he : i=j := by omega
    simp [rawPairState,pairPolynomialCoefficient,he]
  · simp [rawPairState,h]

theorem normalizedPairState_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q (2*Q-2)) i j = 0 := by
  unfold normalizedPairState
  rw [lowerPair_div,rawPairState_lowering Q (2*Q-2) i j hi hj,
    rawPairState_past_lowest Q i j hQ hi hj]
  simp

theorem pairCoefficient_tensor_highest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorRaise Q 0 x y = 0 := by
  have he := pairTensorRaise_weight Q 0 hQ (by omega) x y
  rw [normalizedPairState_highest] at he
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy)).resolve_right hx

theorem pairCoefficient_tensor_lowest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorLower Q (2*Q-2) x y = 0 := by
  have he := pairTensorLower_weight Q (2*Q-2) hQ (by omega) x y
  rw [normalizedPairState_lowest Q x.val y.val hQ (by omega) (by omega)] at he
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy)).resolve_right hx

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_LadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairInclusion_raising (Q : ℕ) (hQ : 0 < Q) :
    totalRaise Q Q * pairInclusion Q = pairInclusion Q * raiseMatrix (2*Q-2) := by
  ext i p
  change (∑ j, totalRaise Q Q i j*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) k p
  rw [totalRaise_apply,raiseMatrix_row,raiseMatrix_row,raiseMatrix_column]
  change pairTensorRaise Q p.val i.1 i.2 = _
  by_cases hp : 0 < p.val
  · rw [dite_eq_left hp]
    have he := pairCoefficient_tensor_raising Q (p.val-1) hQ (by omega) i.1 i.2
    rw [show p.val-1+1=p.val by omega] at he
    simpa only [mul_comm] using he
  · rw [dite_eq_right hp]
    have hz : p.val=0 := by omega
    rw [hz,pairCoefficient_tensor_highest Q hQ]

theorem pairInclusion_lowering (Q : ℕ) (hQ : 0 < Q) :
    (totalRaise Q Q)ᵀ * pairInclusion Q = pairInclusion Q * (raiseMatrix (2*Q-2))ᵀ := by
  ext i p
  change (∑ j, totalRaise Q Q j i*pairCoefficient Q p.val j.1 j.2) =
    ∑ k, pairCoefficient Q k.val i.1 i.2 * raiseMatrix (2*Q-2) p k
  conv_rhs => simp only [mul_comm (pairCoefficient Q _ _ _)]
  rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column,raiseMatrix_row]
  have heq :
      (if h : 0 < i.1.val then pairCoefficient Q p.val ⟨i.1.val-1,by omega⟩ i.2 *
        ladder Q (i.1.val-1) else 0) +
      (if h : 0 < i.2.val then pairCoefficient Q p.val i.1 ⟨i.2.val-1,by omega⟩ *
        ladder Q (i.2.val-1) else 0) = pairTensorLower Q p.val i.1 i.2 := by
    unfold pairTensorLower
    split_ifs <;> ring
  rw [heq]
  by_cases hp : p.val < 2*Q-2
  · rw [dite_eq_left hp,pairCoefficient_tensor_lowering Q p.val hQ hp]
  · rw [dite_eq_right hp]
    have hz : p.val=2*Q-2 := by omega
    rw [hz,pairCoefficient_tensor_lowest Q hQ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalPairRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix Kronecker

theorem physicalPairInclusion_SU2 (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2) :
    (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)*physicalPairInclusion Q =
      physicalPairInclusion Q*sourceSpinRepresentation (2*Q-2) g := by
  apply ladder_intertwiner_SU2 Q Q 1 (2*Q-2) (by omega)
  · intro i n hi
    have hn : i.1.val+i.2.val ≠ n.val+1 := by omega
    simp [physicalPairInclusion,Spin.pairInclusion,pairCoefficient,hn]
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (Spin.pairInclusion_raising Q hQ) i) n)
    simpa [physicalPairInclusion,totalRaiseComplex,spinRaiseComplex,Matrix.mul_apply] using h
  · ext i n
    have h := congrArg Complex.ofReal (congrFun (congrFun (Spin.pairInclusion_lowering Q hQ) i) n)
    simpa [physicalPairInclusion,totalRaiseComplex,spinRaiseComplex,Matrix.mul_apply,Matrix.transpose_apply] using h

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix Kronecker

theorem exteriorRotation_pair_basis (Q : ℕ) (g : SourceSU2) (i j : Fin (Q+1)) :
    exteriorRotation Q g (create i (create j (1 : Space Q))) =
      ∑ k : Spin.SpinIndex Q Q, (sourceSpinRepresentation Q g k.1 i * sourceSpinRepresentation Q g k.2 j) •
        create k.1 (create k.2 (1 : Space Q)) := by
  rw [create_exteriorRotation,create_exteriorRotation]
  simp only [map_one,map_sum,map_smul,Finset.smul_sum,smul_smul,Fintype.sum_prod_type]

theorem pairExterior_rotation (Q : ℕ) (g : SourceSU2) (v : Spin.SpinIndex Q Q → ℂ) :
    exteriorRotation Q g (pairExterior Q v) =
      pairExterior Q ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ v) := by
  simp only [pairExterior,map_sum,map_smul,exteriorRotation_pair_basis,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairExterior_sum {I : Type*} [Fintype I] (Q : ℕ) (v : I → Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (∑ a, v a) = ∑ a, pairExterior Q (v a) := by
  simp only [pairExterior,Finset.sum_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem pairExterior_smul (Q : ℕ) (c : ℂ) (v : Spin.SpinIndex Q Q → ℂ) :
    pairExterior Q (c • v) = c • pairExterior Q v := by
  simp only [pairExterior,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem sourcePairVector_pairExterior (Q p : ℕ) :
    sourcePairVector Q p = (Real.sqrt 2 : ℂ)⁻¹ •
      pairExterior Q (fun i => (pairCoefficient Q p i.1 i.2 : ℂ)) := by
  simp only [sourcePairVector,pairExterior,Fintype.sum_prod_type,Finset.smul_sum,smul_smul,
    div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,mul_comm]

theorem sourcePairVector_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) :
    exteriorRotation Q g (sourcePairVector Q p.val) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p • sourcePairVector Q q.val := by
  have hc : ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
      (fun i => (pairCoefficient Q p.val i.1 i.2 : ℂ))) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g q p •
        (fun i : Spin.SpinIndex Q Q => (pairCoefficient Q q.val i.1 i.2 : ℂ)) := by
    funext i
    have h := congrFun (congrFun (physicalPairInclusion_SU2 Q hQ g) i) p
    simpa only [physicalPairInclusion,Spin.pairInclusion,Matrix.map_apply,Matrix.mul_apply,
      Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using h
  rw [sourcePairVector_pairExterior,map_smul,pairExterior_rotation,hc,pairExterior_sum]
  simp only [pairExterior_smul,Finset.smul_sum,sourcePairVector_pairExterior]
  apply Finset.sum_congr rfl
  intro q hq
  exact smul_comm _ _ _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourcePairCreateEnd_mul (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = sourcePairVector Q p*x := by
  simp only [sourcePairCreateEnd,pairCreateEnd,sourcePairVector,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,Finset.sum_mul,smul_mul_assoc,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*x) =
    (ExteriorAlgebra.ι ℂ (mode i)*(ExteriorAlgebra.ι ℂ (mode j)*1))*x
  simp only [mul_one,mul_assoc]

theorem sourcePairVector_adjoint (Q p : ℕ) (x y : Space Q) :
    occupationInner Q (sourcePairVector Q p*x) y = occupationInner Q x (sourcePairEnd Q p y) := by
  rw [← sourcePairCreateEnd_mul]
  exact pairCreate_pair_adjoint Q _ x y

theorem sourcePairEnd_rotation (Q : ℕ) (hQ : 0 < Q) (g : SourceSU2)
    (p : Fin (2*Q-2+1)) (x : Space Q) :
    sourcePairEnd Q p.val (exteriorRotation Q g x) =
      ∑ q : Fin (2*Q-2+1), sourceSpinRepresentation (2*Q-2) g p q •
        exteriorRotation Q g (sourcePairEnd Q q.val x) := by
  exact exteriorFamily_contraction_rotation Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2))
    (fun p : Fin (2*Q-2+1) => sourcePairVector Q p.val)
    (fun p => sourcePairEnd Q p.val)
    (fun p => sourcePairVector_adjoint Q p.val)
    (fun g p => sourcePairVector_rotation Q hQ g p) g p x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_EnergyRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem sourceFockEnergy_eq_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockEnergy Q x = ∑ p : Fin (2*Q-2+1), occupationNormSq Q (sourcePairEnd Q p.val x) := by
  unfold sourceFockEnergy
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_MatrixQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem occupation_matrix_quadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (W : Matrix J I ℂ) (C : Matrix I I ℂ) (v : J → Space Q) :
    (∑ i, ∑ j, C i j * occupationInner Q
      (∑ a, star (W a i) • v a) (∑ b, star (W b j) • v b)) =
      ∑ a, ∑ b, (W*C*Wᴴ) a b * occupationInner Q (v a) (v b) := by
  simp_rw [occupationInner_sum_left,occupationInner_smul_left,star_star,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_HaarQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_rotation {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (minus : I → Module.End ℂ (Space Q))
    (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
      ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
    (M : Matrix I I ℂ) (g : SourceSU2) (x : Space Q) :
    contractionForm Q minus M (exteriorRotation Q g⁻¹ x) =
      contractionForm Q minus (conjugateOrbit ρ M g) x := by
  unfold contractionForm
  simp_rw [hm,hρ,Matrix.conjTranspose_apply]
  rw [occupation_matrix_quadratic_factor]
  simp_rw [exteriorRotation_unitary]
  simp only [conjugateOrbit,hρ]

theorem contractionForm_haar {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ)
    (hc : ∀ i j, Continuous (fun g => ρ g i j))
    (minus : I → Module.End ℂ (Space Q))
    (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
      ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
    (M : Matrix I I ℂ) (x : Space Q) :
    (∫ g, contractionForm Q minus M (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      contractionForm Q minus (matrixIntegral sourceHaar (conjugateOrbit ρ M)) x := by
  simp_rw [contractionForm_rotation Q ρ hρ minus hm]
  unfold contractionForm
  have hi := compact_conjugateOrbit_integrable sourceHaar ρ hc M
  rw [integral_finsetSum _ (fun i hi' => integrable_finsetSum _
    (fun j hj => (hi i j).mul_const _))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j hj => (hi i j).mul_const _)]
  simp only [integral_mul_const,matrixIntegral]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_Certificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate


theorem eta_numerator : (rows.map (fun r => r.2.1 ^ 2)).sum = 93527408868499 := by
  decide

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_FockHaar
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

theorem pair_contractionForm_one (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) 1 x =
      (sourceFockEnergy Q x : ℂ) := by
  rw [sourceFockEnergy_eq_fin Q hQ]
  simp [contractionForm,Matrix.one_apply,occupationInner_self,Complex.ofReal_sum]

theorem physical_pairFock_haar (Q : ℕ) (hQ : 0 < Q)
    (M : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) (x : Space Q) :
    (∫ g, contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) M
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (Matrix.trace M/(2*Q-2+1 : ℕ)) * (sourceFockEnergy Q x : ℂ) := by
  rw [contractionForm_haar Q (sourceSpinRepresentation (2*Q-2))
    (sourceSpinRepresentation_inv (2*Q-2)) (sourceSpinRepresentation_continuous (2*Q-2))
    _ (sourcePairEnd_rotation Q hQ),source_spin_haar_schur,contractionForm_smul,
    pair_contractionForm_one Q hQ]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_TwoBodyCertificateHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem physicalTwoBodyMatrix_trace (Q : ℕ) (hQ : 5 ≤ Q) :
    Matrix.trace (physicalTwoBodyMatrix Q) = (93527408868499/10^14 : ℂ) := by
  have htr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) :
      Matrix.trace (physicalPairRowMatrix Q row) =
      ((row.2.1 : ℂ)/10^7)^2 := by
    have ht : row.1 ≤ 7 := (show ∀ row ∈ Certificate.rows, row.1 ≤ 7 from by decide) row hr
    let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
    have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; subst i; rfl
    simp only [Matrix.trace,Matrix.diag,physicalPairRowMatrix,he,and_self,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hsum (l : List (Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ)) :
      Matrix.trace l.sum = (l.map Matrix.trace).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.trace_add,ih]
  rw [physicalTwoBodyMatrix,hsum,List.map_map]
  have he : Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row)) =
      Certificate.rows.map (fun row => ((row.2.1 : ℂ)/10^7)^2) := List.map_congr_left htr
  change (Certificate.rows.map (fun row => Matrix.trace (physicalPairRowMatrix Q row))).sum = _
  rw [he]
  have hl (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
      (l.map (fun row => ((row.2.1 : ℂ)/10^7)^2)).sum =
        ((l.map (fun row => row.2.1^2)).sum : ℤ)/(10^14 : ℂ) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,Int.cast_add,Int.cast_pow,ih]
      ring
  rw [hl,Certificate.eta_numerator]
  norm_num

theorem physical_twoBody_certificate_haar_oai (Q : ℕ) (hQ : 5 ≤ Q) (x : Space Q) :
    ((2*Q-2+1 : ℕ) : ℂ) * (∫ g, contractionForm Q
      (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val) (physicalTwoBodyMatrix Q)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      (93527408868499/10^14 : ℂ) * (sourceFockEnergy Q x : ℂ) := by
  rw [physical_pairFock_haar Q (by omega),physicalTwoBodyMatrix_trace Q hQ]
  have hd : ((2*Q-2+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2*Q-2)
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_twoBody_certificate_haar_oai := @OAI.Laughlin.Fock.physical_twoBody_certificate_haar_oai
