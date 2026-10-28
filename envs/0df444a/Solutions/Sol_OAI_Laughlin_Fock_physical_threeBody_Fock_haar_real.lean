-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:20.432306+00:00
-- url     : https://prove2.me/submissions/faa93c54-e625-43fe-8a0f-4423d767d310

import Mathlib
import Definitions.Def_OAIQ047L003
import Definitions.Def_OAIQ047L004
import Theorems.Thm_OAI_Laughlin_Fock_sourceThreeEnd_rotation

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
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HighestEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_norm (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (∑ i : PairOrbitalIndex Q, (coupledHighest Q z hQ hz i)^2) = 1 := by
  simp only [pow_two]
  unfold coupledHighest
  rw [sum_extendWeightSlice]
  simp_rw [extendWeightSlice_at,← pow_two]
  have hs := highestUnit_norm (2*Q-2) Q z (by omega) hz
  simpa only [← Fin.sum_univ_eq_sum_range] using hs

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_weight (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalWeight (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz =
      (coupledWeight Q z : ℝ) • coupledHighest Q z hQ hz := by
  rw [totalWeight_diagonal]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change ((2*Q-2 : ℕ)+ (Q : ℝ)-2*((i.1.val : ℝ)+i.2.val))*coupledHighest Q z hQ hz i =
    (coupledWeight Q z : ℝ)*coupledHighest Q z hQ hz i
  by_cases hi : i.1.val+i.2.val=z
  · have hc : (i.1.val : ℝ)+i.2.val=z := by exact_mod_cast hi
    rw [hc]
    congr 1
    unfold coupledWeight
    rw [Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),Nat.cast_sub (by omega : 2 ≤ 3*Q),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  · have he : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [he]; ring

theorem coupledHighest_raising_zero (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalRaise (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz = 0 := by
  apply extendWeightSlice_highest
  intro p
  exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt

theorem coupledDescendant_norm_pos (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : 0 < vectorNormSq (coupledDescendant Q z hQ hz n) := by
  apply descendant_norm_pos (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledWeight Q z) n
  · exact total_raise_lower_commutator _ _
  · exact total_weight_lower_commutator _ _
  · exact Matrix.transpose_transpose _
  · exact coupledHighest_weight Q z hQ hz
  · exact coupledHighest_raising_zero Q z hQ hz
  · change 0 < ∑ i, (coupledHighest Q z hQ hz i)^2
    rw [coupledHighest_norm Q z hQ hz]; norm_num
  · exact hn

theorem normalizedCoupledDescendant_norm (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : vectorNormSq (normalizedCoupledDescendant Q z hQ hz n) = 1 := by
  have hp := coupledDescendant_norm_pos Q z n hQ hz hn
  unfold normalizedCoupledDescendant vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  change (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ ^ 2 *
    vectorNormSq (coupledDescendant Q z hQ hz n) = 1
  rw [inv_pow,Real.sq_sqrt (le_of_lt hp),inv_mul_cancel₀ (ne_of_gt hp)]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Orthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_orthogonal (Q z w : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hzw : z ≠ w) :
    (∑ i, coupledHighest Q z hQ hz i*coupledHighest Q w hQ hw i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i.1.val+i.2.val=z
  · have hh : i.1.val+i.2.val ≠ w := by omega
    have hv : coupledHighest Q w hQ hw i = 0 :=
      extendWeightSlice_off (2*Q-2) Q w (by omega) hw _ i hh
    rw [hv,mul_zero]
  · have hv : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i he
    rw [hv,zero_mul]

theorem coupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) = 0 := by
  apply descendants_orthogonal (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledHighest Q w hQ hw)
    (coupledWeight Q w) (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (coupledHighest_weight Q w hQ hw)
    (coupledHighest_raising_zero Q z hQ hz) (coupledHighest_raising_zero Q w hQ hw) n m
  rcases hne with h | h
  · exact Or.inl (coupledHighest_orthogonal Q z w hQ hz hw h)
  · exact Or.inr h

theorem normalizedCoupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, normalizedCoupledDescendant Q z hQ hz n i *
      normalizedCoupledDescendant Q w hQ hw m i) = 0 := by
  unfold normalizedCoupledDescendant
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ *
      (Real.sqrt (vectorNormSq (coupledDescendant Q w hQ hw m)))⁻¹ *
      (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [coupledDescendant_orthogonal Q z w n m hQ hz hw hne,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledIndex_card (Q : ℕ) (hQ : 2 ≤ Q) :
    Fintype.card (CoupledIndex Q) = Fintype.card (PairOrbitalIndex Q) := by
  have hr : (Fintype.card (CoupledIndex Q) : ℝ) = (Fintype.card (PairOrbitalIndex Q) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (Q+1)) : ((coupledWeight Q z.val+1 : ℕ) : ℝ) = 3*(Q : ℝ)-1-2*z.val := by
      unfold coupledWeight
      rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub (by omega : 2*z.val ≤ 3*Q-2),
        Nat.cast_sub (by omega : 2 ≤ 3*Q)]
      push_cast; ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  exact_mod_cast hr

theorem coupledBasis_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (coupledBasisMatrix Q hQ)ᵀ * coupledBasisMatrix Q hQ = 1 := by
  ext s t
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply,coupledBasisMatrix,Matrix.one_apply]
  by_cases hst : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      normalizedCoupledDescendant_norm Q s.1.val s.2.val hQ (by omega) (by omega)
  · rw [ite_eq_right hst]
    apply normalizedCoupledDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      apply hst
      have he : n=m := Fin.ext hnm
      rw [he]
    · left
      intro h
      exact hzw (Fin.ext h)

theorem coupledBasis_complete (Q : ℕ) (hQ : 2 ≤ Q) :
    coupledBasisMatrix Q hQ * (coupledBasisMatrix Q hQ)ᵀ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq (m := CoupledIndex Q) (n := PairOrbitalIndex Q)
    (R := ℝ) (coupledIndex_card Q hQ)).mp (coupledBasis_isometry Q hQ)

end Laughlin.Spin

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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Specializations
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
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_SpinProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledSelector_sum (Q : ℕ) : (∑ z : Fin (Q+1), coupledSelector Q z) = 1 := by
  ext s t
  by_cases h : s=t
  · subst t
    simp [coupledSelector,Matrix.sum_apply]
  · simp [coupledSelector,Matrix.sum_apply,h]

theorem threeSpinProjector_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), threeSpinProjector Q hQ z) = 1 := by
  unfold threeSpinProjector
  rw [← Matrix.sum_mul,← Matrix.mul_sum,coupledSelector_sum,Matrix.mul_one,coupledBasis_complete Q hQ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_GroupIntertwining
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
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HaarBlocks
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

theorem threeBodySpinRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    threeBodySpinRepresentation Q g⁻¹=(threeBodySpinRepresentation Q g)ᴴ := by
  change _ ⊗ₖ _ = (_ ⊗ₖ _)ᴴ
  rw [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv,sourceSpinRepresentation_inv]

theorem threeCoupledInclusion_adjoint_SU2 (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (g : SourceSU2) :
    (threeCoupledInclusion Q hQ z)ᴴ * threeBodySpinRepresentation Q g =
      sourceSpinRepresentation (coupledWeight Q z.val) g * (threeCoupledInclusion Q hQ z)ᴴ := by
  have h : threeBodySpinRepresentation Q g⁻¹ * threeCoupledInclusion Q hQ z =
    threeCoupledInclusion Q hQ z * sourceSpinRepresentation (coupledWeight Q z.val) g⁻¹ :=
    threeCoupledInclusion_SU2 Q hQ z g⁻¹
  have ht := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul,threeBodySpinRepresentation_inv,sourceSpinRepresentation_inv,
    Matrix.conjTranspose_conjTranspose] using ht

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
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,threeCoupledInclusion_adjoint_SU2,
    Matrix.mul_assoc,Matrix.mul_assoc,hw]
  simp only [Matrix.mul_assoc]

theorem threeBody_haar_diagonal_block (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
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

theorem threeBody_haar_offdiagonal_block (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1))
    (hzw : z ≠ w) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    (threeCoupledInclusion Q hQ z)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (threeBodySpinRepresentation Q) M) * threeCoupledInclusion Q hQ w = 0 := by
  rw [threeBody_haar_compressed]
  apply source_unequal_spin_haar_zero
  intro h
  apply hzw
  apply Fin.ext
  unfold coupledWeight at h
  have hz := z.isLt
  have hw := w.isLt
  omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_RankTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem realOuter_quadratic {I : Type*} [Fintype I] (u v x : I → ℝ) :
    dotProduct x (realOuter u v *ᵥ x) = dotProduct x u * dotProduct x v := by
  simp only [dotProduct,Matrix.mulVec,realOuter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem threeSpinProjector_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    Matrix.trace (threeSpinProjector Q hQ z * M) =
      ∑ n : Fin (coupledWeight Q z.val+1),
        dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n.val)
          (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n.val) := by
  let B := coupledBasisMatrix Q hQ
  have he : Matrix.trace (threeSpinProjector Q hQ z * M) =
      Matrix.trace (coupledSelector Q z * (Bᵀ*M*B)) := by
    change Matrix.trace (B*coupledSelector Q z*Bᵀ*M) = _
    calc
      _ = Matrix.trace ((B*coupledSelector Q z)*(Bᵀ*M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Bᵀ*M)*(B*coupledSelector Q z)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Bᵀ*M*B)*coupledSelector Q z) := by simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [he]
  unfold coupledSelector
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  rw [Fintype.sum_sigma]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Matrix.mul_apply,Matrix.transpose_apply,B,coupledBasisMatrix,Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PhysicalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_dot (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (pairOrbitalUnit Q p j) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  simp only [dotProduct,pairOrbitalUnit,mul_ite,mul_one,mul_zero]
  have he : ∀ i : PairOrbitalIndex Q, (i.1.val=p ∧ i.2.val=j) ↔ i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    intro i
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp_rw [he]
  simp

theorem threeBodyLevelMatrix_quadratic (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ))
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (threeBodyLevelMatrix Q t T ell entries *ᵥ v) =
      2*((ell : ℝ)/10^7)*dotProduct v (pairOrbitalUnit Q t (T-t))*
        dotProduct v (threeBodyLevelVector Q t T entries) +
      (dotProduct v (threeBodyLevelVector Q t T entries))^2 := by
  simp only [threeBodyLevelMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,realOuter_quadratic,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem phasedThreeDescendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (i : PairOrbitalIndex Q) (hi : i.1.val+i.2.val ≠ z.val+n) :
    phasedThreeDescendant Q hQ z n i = 0 := by
  have hh := genericUnitDescendant_off (2*Q-2) Q z.val n (by omega) (by omega) i hi
  change (-1 : ℝ)^z.val * genericUnitDescendant (2*Q-2) Q z.val (by omega) (by omega) n i = 0
  rw [hh,mul_zero]

theorem phasedThreeDescendant_at_level (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (T p j : ℕ)
    (hz : z.val ≤ T) (hT : T ≤ Q) (hpj : p+j=T) :
    phasedThreeDescendant Q hQ z (T-z.val) (⟨p,by omega⟩,⟨j,by omega⟩) =
      physicalCouplingCoefficient (2*Q-2) Q z.val T p := by
  rw [physicalCouplingCoefficient,dite_eq_left ⟨hz,by omega,by omega,hT⟩]
  have hj : T-p=j := by omega
  subst j
  rfl

theorem threeBodyLevelVector_dot {Q : ℕ} (v : PairOrbitalIndex Q → ℝ) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) :
    dotProduct v (threeBodyLevelVector Q t T entries) =
      (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
        dotProduct v (pairOrbitalUnit Q e.1 e.2.1) else 0)).sum := by
  induction entries with
  | nil => simp [threeBodyLevelVector]
  | cons e es ih =>
    simp only [threeBodyLevelVector,List.map_cons,List.sum_cons] at ih ⊢
    rw [dotProduct_add,ih]
    by_cases h : e.1+e.2.1=T
    · simp [h,dotProduct_smul,mul_comm]
    · simp [h]

theorem phasedThreeDescendant_unit_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n p j : ℕ)
    (h : p+j ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q p j) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [pairOrbitalUnit]
  split_ifs with he
  · rw [phasedThreeDescendant_off Q hQ z n i (by omega),zero_mul]
  · exact mul_zero _

theorem threeBodyLevelVector_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n) (threeBodyLevelVector Q t T entries) = 0 := by
  rw [threeBodyLevelVector_dot]
  have he : entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e *
      dotProduct (phasedThreeDescendant Q hQ z n) (pairOrbitalUnit Q e.1 e.2.1) else 0) = entries.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro e he
    split_ifs with hT
    · rw [phasedThreeDescendant_unit_off Q hQ z n e.1 e.2.1 (by omega),mul_zero]
    · rfl
  rw [he]
  simp

theorem threeBodyLevelVector_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val)) (threeBodyLevelVector Q t T entries) =
      threeBodyInner (physicalCouplingCoefficient (2*Q-2) Q) z.val T t entries := by
  rw [threeBodyLevelVector_dot]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  split_ifs with h
  · rw [pairOrbitalUnit_dot Q e.1 e.2.1 (by omega) (by omega),
      phasedThreeDescendant_at_level Q hQ z T e.1 e.2.1 hz hT h]
  · rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_LevelTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem phasedThreeDescendant_quadratic (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
    dotProduct (phasedThreeDescendant Q hQ z n) (M *ᵥ phasedThreeDescendant Q hQ z n) =
      dotProduct (normalizedCoupledDescendant Q z.val hQ (by omega) n)
        (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n) := by
  simp only [phasedThreeDescendant,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  have hs : ((-1 : ℝ)^z.val)^2=1 := by rw [← pow_mul,mul_comm z.val 2,pow_mul]; norm_num
  nlinarith only [congrArg (fun s : ℝ => s * dotProduct
    (normalizedCoupledDescendant Q z.val hQ (by omega) n)
    (M *ᵥ normalizedCoupledDescendant Q z.val hQ (by omega) n)) hs]

theorem threeBodyLevelMatrix_descendant_off (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (h : T ≠ z.val+n) :
    dotProduct (phasedThreeDescendant Q hQ z n)
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z n) = 0 := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant_off Q hQ z n t T entries h]
  ring

theorem threeBodyLevelMatrix_descendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hz : z.val ≤ T) (hT : T ≤ Q) (ht : t ≤ T) :
    dotProduct (phasedThreeDescendant Q hQ z (T-z.val))
      (threeBodyLevelMatrix Q t T ell entries *ᵥ phasedThreeDescendant Q hQ z (T-z.val)) =
      physicalThreeBodyLevel Q z.val T t ell entries := by
  rw [threeBodyLevelMatrix_quadratic,threeBodyLevelVector_descendant Q hQ z t T entries hz hT,
    pairOrbitalUnit_dot Q t (T-t) (by omega) (by omega),
    phasedThreeDescendant_at_level Q hQ z T t (T-t) hz hT (by omega)]
  rfl

theorem threeBodyLevelMatrix_trace (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (t T : ℕ)
    (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) (hT : T ≤ Q) (ht : t ≤ T) :
    Matrix.trace (threeSpinProjector Q hQ z * threeBodyLevelMatrix Q t T ell entries) =
      if z.val ≤ T then physicalThreeBodyLevel Q z.val T t ell entries else 0 := by
  classical
  rw [threeSpinProjector_trace]
  simp_rw [← phasedThreeDescendant_quadratic]
  by_cases hz : z.val ≤ T
  · rw [ite_eq_left hz]
    have hn : T-z.val < coupledWeight Q z.val+1 := by unfold coupledWeight; omega
    rw [Finset.sum_eq_single (⟨T-z.val,hn⟩ : Fin (coupledWeight Q z.val+1))]
    · exact threeBodyLevelMatrix_descendant Q hQ z t T ell entries hz hT ht
    · intro n hn' hne
      apply threeBodyLevelMatrix_descendant_off
      intro he
      apply hne
      exact Fin.ext (by dsimp; omega)
    · simp
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro n hn
    exact threeBodyLevelMatrix_descendant_off Q hQ z n.val t T ell entries (by omega)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Topology

 theorem trace_mul_list_sum {I : Type*} [Fintype I] (P : Matrix I I ℝ)
    (l : List (Matrix I I ℝ)) :
    Matrix.trace (P*l.sum) = (l.map (fun M => Matrix.trace (P*M))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.trace_add,ih]

 theorem list_filter_sum_if {I : Type*} (l : List I) (p q : I → Prop)
    [DecidablePred p] [DecidablePred q] (f : I → ℝ) :
    ((l.filter p).map (fun i => if q i then f i else 0)).sum =
      ((l.filter (fun i => p i ∧ q i)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp,hq,ih]

theorem source_physical_threeBody_trace_identity (Q : ℕ) (hQ : 15 ≤ Q) (z : Fin (Q+1)) :
    Matrix.trace (threeSpinProjector Q (by omega) z * physicalThreeBodyMatrix Q) =
      physicalThreeBodyTraceFormula Q z.val := by
  unfold physicalThreeBodyMatrix
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  unfold physicalThreeBodyTraceFormula threeBodyTraceFormula
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  rw [trace_mul_list_sum]
  simp only [List.map_map,Function.comp_def]
  have he : (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => Matrix.trace (threeSpinProjector Q (by omega) z * threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2))) =
      (((List.range 16).filter (fun T => row.1 ≤ T)).map
        (fun T => if z.val ≤ T then physicalThreeBodyLevel Q z.val T row.1 row.2.1 row.2.2 else 0)) := by
    apply List.map_congr_left
    intro T hT
    simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hT
    exact threeBodyLevelMatrix_trace Q (by omega) z row.1 T row.2.1 row.2.2 (by omega) hT.2
  rw [he,list_filter_sum_if]
  simp only [physicalThreeBodyLevel,max_le_iff,and_comm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_HaarNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix
open Rotation

theorem threeSpinProjector_complex_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), (threeSpinProjector Q hQ z).map Complex.ofReal) = 1 := by
  funext i j
  have h := congrArg Complex.ofReal (congrFun (congrFun (threeSpinProjector_sum Q hQ) i) j)
  simpa only [Matrix.sum_apply,Matrix.map_apply,Complex.ofReal_sum,Matrix.one_apply,
    apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h

theorem physical_threeBody_haar_normalization (Q : ℕ) (hQ : 2 ≤ Q)
    (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ) :
    matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M) =
      ∑ z : Fin (Q+1),
        (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/
          (coupledWeight Q z.val+1 : ℕ)) • (threeSpinProjector Q hQ z).map Complex.ofReal := by
  let H := matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q) M)
  let R := fun z => (threeSpinProjector Q hQ z).map Complex.ofReal
  have hblock (z w : Fin (Q+1)) : R z*H*R w =
      if z=w then (Matrix.trace (R z*M)/(coupledWeight Q z.val+1 : ℕ)) • R z else 0 := by
    change (threeSpinProjector Q hQ z).map Complex.ofReal*H*
      (threeSpinProjector Q hQ w).map Complex.ofReal = _
    rw [threeSpinProjector_complex_factor,threeSpinProjector_complex_factor]
    have he : threeCoupledInclusion Q hQ z*(threeCoupledInclusion Q hQ z)ᴴ*H*
        (threeCoupledInclusion Q hQ w*(threeCoupledInclusion Q hQ w)ᴴ) =
        threeCoupledInclusion Q hQ z*
          ((threeCoupledInclusion Q hQ z)ᴴ*H*threeCoupledInclusion Q hQ w)*
          (threeCoupledInclusion Q hQ w)ᴴ := by simp only [Matrix.mul_assoc]
    rw [he]
    by_cases hzw : z=w
    · subst w
      rw [ite_eq_left rfl]
      change _ = (Matrix.trace ((threeSpinProjector Q hQ z).map Complex.ofReal*M)/_) • _
      rw [threeBody_haar_diagonal_block,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
        ← threeSpinProjector_complex_factor]
    · rw [ite_eq_right hzw,threeBody_haar_offdiagonal_block Q hQ z w hzw,Matrix.mul_zero,Matrix.zero_mul]
  calc
    _ = (∑ z, R z)*H*(∑ w, R w) := by
      change H = _
      rw [show (∑ z, R z)=1 from threeSpinProjector_complex_sum Q hQ,Matrix.one_mul,Matrix.mul_one]
    _ = ∑ z, ∑ w, R z*H*R w := by rw [Matrix.sum_mul,Matrix.sum_mul]; simp only [Matrix.mul_sum]
    _ = _ := by simp only [hblock,Finset.sum_ite_eq,Finset.mem_univ,ite_true,R]

theorem complex_trace_mul_real {I : Type*} [Fintype I] (A B : Matrix I I ℝ) :
    Matrix.trace (A.map Complex.ofReal * B.map Complex.ofReal) = ((Matrix.trace (A*B) : ℝ) : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.map_apply,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem physical_threeBody_certificate_haar (Q : ℕ) (hQ : 15 ≤ Q) :
    matrixIntegral sourceHaar (conjugateOrbit (threeBodySpinRepresentation Q)
      ((physicalThreeBodyMatrix Q).map Complex.ofReal)) =
      ∑ z : Fin (Q+1),
        ((physicalThreeBodyTraceFormula Q z.val : ℂ)/(coupledWeight Q z.val+1 : ℕ)) •
          (threeSpinProjector Q (by omega) z).map Complex.ofReal := by
  rw [physical_threeBody_haar_normalization Q (by omega)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [complex_trace_mul_real,source_physical_threeBody_trace_identity Q hQ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

theorem physical_threeBody_Fock_haar (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      ∑ z : Fin (Q+1),
        ((physicalThreeBodyTraceFormula Q z.val : ℂ)/(coupledWeight Q z.val+1 : ℕ)) *
          contractionForm Q (sourceThreeEnd Q)
            ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x := by
  rw [contractionForm_haar Q (threeBodySpinRepresentation Q)
    (threeBodySpinRepresentation_inv Q) (threeBodySpinRepresentation_continuous Q)
    _ (sourceThreeEnd_rotation Q (by omega)),physical_threeBody_certificate_haar Q hQ,
    contractionForm_sum]
  simp only [contractionForm_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_FockComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory Filter
open scoped BigOperators Matrix

theorem physical_threeBody_Fock_haar_real_oai (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re =
      ∑ z : Fin (Q+1), (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) *
        (contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re := by
  rw [physical_threeBody_Fock_haar Q hQ,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Complex.ofReal_natCast,← Complex.ofReal_div]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_oai := @OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_oai
