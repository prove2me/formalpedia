-- Prove2me | solution 1 for OAI.Laughlin.Fock.fourCopyForm_scaled_haar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:41:55.644988+00:00
-- url     : https://prove2.me/submissions/10e75dd3-6c56-4380-bff4-3d926da46a47

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L003
import Definitions.Def_OAIQ047L004
import Theorems.Thm_OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation

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

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

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
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_ExteriorRotation
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
-- module Solutions.OAIQ047_LA.Laughlin_Fock_SpinContinuity
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

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_OrbitIntegration
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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Copies
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
-- module Solutions.OAIQ047_LA.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hDQ : D ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let P := fun b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) =>
    b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2
  have he : (∑ b : Fin (D+1) × Fin (Q+1) × Fin (Q+1),
      if P b then f b.1.val b.2.1 b.2.2 else 0) =
      ∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
        if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0 := by
    simp only [Fintype.sum_prod_type,P]
  rw [← he,← Finset.sum_filter,Finset.sum_subtype (p := P) _ (by simp)]
  exact (localFourIndexEquiv Q D hDQ).sum_comp
    (fun b => f b.val.1.val b.val.2.1 b.val.2.2) |>.symm

end Laughlin.Spin

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

theorem fourBody_cross_orbit (Q D : ℕ) (hD : D+2 ≤ Q) (r s : OddPairLabel D)
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
        rw [retainedFourInclusion_SU2,retainedFourInclusion_adjoint_SU2]
        simp only [Matrix.mul_assoc]
  unfold matrixIntegral
  simp_rw [he]
  rw [integral_matrix_sandwich sourceHaar _ (compact_conjugateOrbit_integrable sourceHaar _
    (sourceSpinRepresentation_continuous (fourSpinWeight Q D)) M)]
  change retainedFourInclusion Q D hD r * matrixIntegral sourceHaar
    (conjugateOrbit (sourceSpinRepresentation (fourSpinWeight Q D)) M) *
      (retainedFourInclusion Q D hD s)ᴴ = _
  rw [source_spin_haar_schur,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_WeightSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourWeightSlice_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hQ : D+2 ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (2*Q-2+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=D then f p.val i.val.1 i.val.2 else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let F := fun p : ℕ => ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    if p+j.val+k.val=D ∧ j < k then f p j k else 0
  have hi (p : ℕ) : (∑ i : WedgePairIndex Q,
      if p+i.val.1.val+i.val.2.val=D then f p i.val.1 i.val.2 else 0) = F p := by
    have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : SpinIndex Q Q => i.1 < i.2)
      (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp)
      (fun i => if p+i.1.val+i.2.val=D then f p i.1 i.2 else 0)
    rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    by_cases h₁ : j < k <;> by_cases h₂ : p+j.val+k.val=D <;> simp [h₁,h₂]
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range]
  have hsub : (∑ p ∈ Finset.range (D+1), F p) = ∑ p ∈ Finset.range (2*Q-2+1), F p := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hn
    have hpD : D < p := by simpa using hn
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro k hk
    simp [show p+j.val+k.val≠D by omega]
  rw [← hsub,← Fin.sum_univ_eq_sum_range]
  exact localFourIndex_sum Q D (by omega) f

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physicalFourCopyEnd_column (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) (x : Space Q) :
    (∑ i, star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x) =
      physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) x := by
  have hc (i : FourWedgeIndex Q) :
      star (retainedFourInclusion Q D hQ r i 0) • sourceFourFamilyEnd Q i x =
        if i.1.val+i.2.val.1.val+i.2.val.2.val=D then
          (fourBodyCoefficient Q (oddPairDeficit r) D D i.1.val i.2.val.1.val i.2.val.2.val : ℂ) •
            sourceFourEnd Q i.1.val i.2.val.1 i.2.val.2 x else 0 := by
    rw [retainedFourInclusion_column]
    simp only [Fin.val_zero,Complex.star_def,Complex.conj_ofReal]
    by_cases h : i.1.val+i.2.val.1.val+i.2.val.2.val=D
    · have he := fourBodyCopy_source_coefficient Q (oddPairDeficit r) D D
        (oddPairDeficit_le r) (le_refl D) hQ i.1 i.2 h
      simp only [Nat.sub_self] at he
      rw [ite_eq_left h,he]
      rfl
    · rw [ite_eq_right h,fourBodyCopy_off Q (oddPairDeficit r) D 0 _ (oddPairDeficit_le r)
        _ _ i.1 i.2 (by simpa using h)]
      simp
  simp_rw [hc]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [fourWeightSlice_sum Q D hQ (fun p j k =>
    (fourBodyCoefficient Q (oddPairDeficit r) D D p j.val k.val : ℂ) • sourceFourEnd Q p j k x)]
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]

theorem contractionForm_outer_cross {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v w : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v w) x =
      occupationInner Q (∑ i, star (v i) • minus i x) (∑ j, star (w j) • minus j x) := by
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrix_cross_sandwich_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (V W : Matrix I J ℂ) (p : J) :
    V*diagonalUnit p*Wᴴ = complexOuter (fun i => V i p) (fun i => W i p) := by
  ext i j
  simp [diagonalUnit,Matrix.mul_apply,complexOuter,Matrix.conjTranspose_apply,ite_and]

theorem physicalFourCopyEnd_cross_haar (Q D : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, occupationInner Q
      (physicalFourCopyEnd Q (oddPairDeficit r) D (by omega) (exteriorRotation Q g⁻¹ x))
      (physicalFourCopyEnd Q (oddPairDeficit s) D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ s)ᴴ) x := by
  let M : Matrix (Fin (fourSpinWeight Q D+1)) (Fin (fourSpinWeight Q D+1)) ℂ := diagonalUnit 0
  have h := contractionForm_haar Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (fourBodySpinRepresentation_continuous Q)
    (sourceFourFamilyEnd Q) (sourceFourFamilyEnd_rotation Q (by omega))
    (retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ) x
  rw [fourBody_cross_orbit,contractionForm_smul] at h
  have ht : Matrix.trace M=1 := by simp [M,diagonalUnit,Matrix.trace,Matrix.diag]
  rw [ht] at h
  have he := matrix_cross_sandwich_single (retainedFourInclusion Q D hQ r)
    (retainedFourInclusion Q D hQ s) (0 : Fin (fourSpinWeight Q D+1))
  change retainedFourInclusion Q D hQ r*M*(retainedFourInclusion Q D hQ s)ᴴ = _ at he
  simp_rw [he,contractionForm_outer_cross,physicalFourCopyEnd_column] at h
  rw [h]
  have hd : ((4*Q-1-2*D : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CopyOperatorHaar
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

theorem physical_fourCopyOperator_haar (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    ((4*Q-1-2*D : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re := by
  let L : OddPairLabel D → Module.End ℂ (Space Q) :=
    fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
  have hi (r s : OddPairLabel D) := linearMap_rotation_inner_integrable Q (L r) (L s) x
  have hisum : Integrable (fun g : SourceSU2 => ∑ r, ∑ s,
      (C r s : ℂ) * occupationInner Q (L r (exteriorRotation Q g⁻¹ x))
        (L s (exteriorRotation Q g⁻¹ x))) sourceHaar :=
    integrable_finsetSum _ (fun r hr => integrable_finsetSum _ (fun s hs => (hi r s).const_mul _))
  have hc : ((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, ∑ r, ∑ s,
      (C r s : ℂ) * occupationInner Q (L r (exteriorRotation Q g⁻¹ x))
        (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x := by
    rw [integral_finsetSum _ (fun r hr => integrable_finsetSum _ (fun s hs => (hi r s).const_mul _))]
    simp_rw [integral_finsetSum _ (fun s hs => (hi _ s).const_mul _),integral_const_mul]
    simp only [fourCopyOperator,contractionForm_sum,contractionForm_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    calc
      _ = (C r s : ℂ) * (((4*Q-1-2*D : ℕ) : ℂ) * (∫ g, occupationInner Q
        (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) := by ring
      _ = _ := by rw [physicalFourCopyEnd_cross_haar Q D hQ r s]
  have hr := congrArg Complex.re hc
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hr
  have hre := integral_re hisum
  change (∫ g, (∑ r, ∑ s, (C r s : ℂ) * occupationInner Q
    (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x))).re ∂sourceHaar) =
    (∫ g, ∑ r, ∑ s, (C r s : ℂ) * occupationInner Q
      (L r (exteriorRotation Q g⁻¹ x)) (L s (exteriorRotation Q g⁻¹ x)) ∂sourceHaar).re at hre
  rw [← hre] at hr
  simpa only [occupationQuadratic,L,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    zero_mul,sub_zero] using hr

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RetainedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourCopyForm_scaled_haar_oai (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C : OddPairLabel D → OddPairLabel D → ℝ) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ C) x).re =
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, occupationQuadratic Q C
      (fun r => physicalFourCopyEnd Q (oddPairDeficit r) D (by omega)
        (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  rw [← physical_fourCopyOperator_haar Q D hQ C x]
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.fourCopyForm_scaled_haar_oai := @OAI.Laughlin.Fock.fourCopyForm_scaled_haar_oai
