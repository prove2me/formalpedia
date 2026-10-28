-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceA4Form_retained_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:44:55.494108+00:00
-- url     : https://prove2.me/submissions/93ce46c8-d066-4e9e-99d2-4393b2326305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L003
import Definitions.Def_OAIQ047L004
import Theorems.Thm_OAI_Laughlin_Fock_fourCopyForm_allowance_identity
import Theorems.Thm_OAI_Laughlin_Fock_fourCopyForm_scaled_haar
import Theorems.Thm_OAI_Laughlin_Fock_physical_fourBody_total_haar_transfer
import Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real
import Theorems.Thm_OAI_Laughlin_Fock_sourceFourFamilyEnd_rotation
import Theorems.Thm_OAI_Laughlin_Spin_physicalFourBodyHaar_retained_sum

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

theorem insertionSign_norm (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    ‖insertionSign Q i A‖ = 1 := by
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

theorem annihilate_normSq (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) =
      ∑ A : Finset (Fin (Q+1)), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0 := by
  have h (A : Finset (Fin (Q+1))) :
      ‖(occupationBasis Q).repr (annihilate i x) A‖^2 =
        if i ∉ A then ‖(occupationBasis Q).repr x (insert i A)‖^2 else 0 := by
    by_cases hi : i ∈ A <;> simp [annihilate_coordinate,hi,insertionSign_norm]
  unfold occupationNormSq
  simp_rw [h]
  simpa only [Finset.sum_filter] using
    sum_unoccupied_insert (R := ℝ) i (fun A => ‖(occupationBasis Q).repr x A‖^2)

theorem annihilate_normSq_le (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) ≤ occupationNormSq Q x := by
  rw [annihilate_normSq]
  unfold occupationNormSq
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · positivity

theorem two_annihilate_normSq_le (Q : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate k (annihilate j x)) ≤ occupationNormSq Q x :=
  (annihilate_normSq_le Q k _).trans (annihilate_normSq_le Q j x)

theorem sourceFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (sourceFourEnd Q p j k x) ≤
      occupationNormSq Q (sourcePairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (sourcePairEnd Q p x)

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

theorem linearMap_rotation_norm_continuous (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Continuous (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) := by
  unfold occupationNormSq
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q L x A).norm.pow 2

theorem linearMap_rotation_norm_integrable (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) sourceHaar :=
  (linearMap_rotation_norm_continuous Q L x).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

end Laughlin.Fock

end OAI
end

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

theorem source_fourBody_coefficients_norm (Q r D T : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQT : T+2 ≤ Q) :
    (∑ p : Fin ((2*Q-2)+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=T then
        (fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val)^2 else 0) = 1 := by
  have hn : T-D ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r) := by
    unfold genericCoupledWeight; omega
  have hnorm := fourBodyCopy_norm Q r D (T-D) (by omega) ho (by omega)
    (by unfold genericCoupledWeight; omega) hn
  rw [vectorNormSq,Fintype.sum_prod_type] at hnorm
  rw [← hnorm]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro i hi
  by_cases he : p.val+i.val.1.val+i.val.2.val=T
  · rw [ite_eq_left he,fourBodyCopy_source_coefficient Q r D T hrD hDT hQT p i he]
  · rw [ite_eq_right he,fourBodyCopy_off Q r D (T-D) (by omega) hrD (by omega)
      (by unfold genericCoupledWeight; omega) p i (by omega),zero_pow (by omega)]

end Laughlin.Spin

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

theorem allowance_count :
    ((List.range 23).map (fun n => ((n+2)/2) * ((n+2)^2/4))).sum = 10946 := by
  decide

end Laughlin.Certificate

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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CopyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem fourCopyOperator_diagonal (Q D : ℕ) (hQ : D+2 ≤ Q) (c : OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (Matrix.diagonal c) = ∑ r,
      (c r : ℂ) • (retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) := by
  classical
  simp [fourCopyOperator,Matrix.diagonal_apply,apply_ite,ite_smul]

theorem fourCopyOperator_sub (Q D : ℕ) (hQ : D+2 ≤ Q)
    (C E : OddPairLabel D → OddPairLabel D → ℝ) :
    fourCopyOperator Q D hQ (C-E) = fourCopyOperator Q D hQ C-fourCopyOperator Q D hQ E := by
  simp only [fourCopyOperator,Pi.sub_apply,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

theorem fourCopyOperator_middle (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    fourCopyOperator Q D hQ (finiteFourMiddle Q D) =
      (fourDimensionRatio Q D : ℂ) •
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
          (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) +
      ((3/10^6 : ℝ) : ℂ) • (∑ r : OddPairLabel D,
        retainedFourInclusion Q D hQ r * (retainedFourInclusion Q D hQ r)ᴴ) -
      fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s)) := by
  classical
  unfold finiteFourMiddle
  erw [fourCopyOperator_sub,fourCopyOperator_diagonal]
  have he (r : OddPairLabel D) : Certificate.copyLabel r=1 ↔ r=firstOddPairLabel D hD := by
    dsimp [Certificate.copyLabel,firstOddPairLabel]
    constructor
    · intro h; apply Fin.ext; dsimp; omega
    · intro h; have := congrArg Fin.val h; dsimp at this; omega
  simp only [Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
  simp_rw [he]
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,← Finset.smul_sum]
  rfl

theorem fourDimensionRatio_exact (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourDimensionRatio Q D =
      ((4*Q-1-2*D : ℕ) : ℝ)/((2*Q-2+1 : ℕ) : ℝ) := by
  unfold fourDimensionRatio
  congr 1
  · rw [Nat.cast_sub (by omega : 2*D ≤ 4*Q-1),Nat.cast_sub (by omega : 1 ≤ 4*Q)]
    push_cast
    ring
  · rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_LocalNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_local_normalization (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) (hQ : D+2 ≤ Q) :
    (∑ b : LocalFourIndex D,
      (fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val)^2) = 1 := by
  classical
  let f := fun p : ℕ => ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    if p+j.val+k.val=D ∧ j < k then (fourBodyCoefficient Q r D D p j.val k.val)^2 else 0
  have hi (p : ℕ) : (∑ i : WedgePairIndex Q,
      if p+i.val.1.val+i.val.2.val=D then (fourBodyCoefficient Q r D D p i.val.1.val i.val.2.val)^2 else 0) = f p := by
    have hs := Finset.sum_subtype (F := inferInstance) (p := fun i : SpinIndex Q Q => i.1 < i.2)
      (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2)) (by simp)
      (fun i => if p+i.1.val+i.2.val=D then (fourBodyCoefficient Q r D D p i.1.val i.2.val)^2 else 0)
    rw [← hs,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro k hk
    by_cases h₁ : j < k <;> by_cases h₂ : p+j.val+k.val=D <;> simp [h₁,h₂]
  have hn := source_fourBody_coefficients_norm Q r D D hor hr (le_refl _) hQ
  simp_rw [hi] at hn
  rw [Fin.sum_univ_eq_sum_range] at hn
  have hsub : (∑ p ∈ Finset.range (D+1), f p) = ∑ p ∈ Finset.range ((2*Q-2)+1), f p := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro p hp hn
    have hpD : D < p := by simpa using hn
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro k hk
    simp [show p+j.val+k.val≠D by omega]
  have he := localFourIndex_sum Q D (by omega)
    (fun p j k => (fourBodyCoefficient Q r D D p j.val k.val)^2)
  rw [← he]
  change (∑ p : Fin (D+1), f p.val)=1
  rw [Fin.sum_univ_eq_sum_range,hsub]
  exact hn

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_WeightedOccupationNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem normalized_occupation_sum_bound {I : Type*} [Fintype I] (Q : ℕ)
    (c : I → ℝ) (v : I → Space Q) (hc : (∑ i, (c i)^2)=1) :
    occupationNormSq Q (∑ i, (c i : ℂ) • v i) ≤ ∑ i, occupationNormSq Q (v i) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm (f := fun i A => ‖(occupationBasis Q).repr (v i) A‖^2)]
  apply Finset.sum_le_sum
  intro A hA
  have ht : ‖∑ i, (c i : ℂ) * (occupationBasis Q).repr (v i) A‖ ≤
      ∑ i, |c i| * ‖(occupationBasis Q).repr (v i) A‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      (norm_sum_le Finset.univ (fun i => (c i : ℂ) * (occupationBasis Q).repr (v i) A))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |c i|)
    (fun i => ‖(occupationBasis Q).repr (v i) A‖)
  simp only [sq_abs,hc,one_mul] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem source_fourBody_normalized_allowance (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : D+2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (physicalFourCopyEnd Q r D (by omega) x) ≤
      ∑ b : LocalFourIndex D, occupationNormSq Q (sourcePairEnd Q b.val.1.val x) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  apply (normalized_occupation_sum_bound Q
    (fun b : LocalFourIndex D => fourBodyCoefficient Q r D D b.val.1.val b.val.2.1.val b.val.2.2.val)
    (fun b => sourceFourEnd Q b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ x)
    (source_fourBody_local_normalization Q r D hr hor hQ)).trans
  apply Finset.sum_le_sum
  intro b hb
  exact sourceFour_normSq_le_pair Q b.val.1.val _ _ x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_LocalFourCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem localFourIndex_card_sum (D : ℕ) :
    Fintype.card (LocalFourIndex D) = ∑ n : Fin (D+1), (n.val+1)/2 := by
  rw [Fintype.card_congr (localFourCountEquiv D),Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem localFourIndex_card_retained (D : ℕ) (hD : D ≤ 23) :
    Fintype.card (LocalFourIndex D) = (D+1)^2/4 := by
  rw [localFourIndex_card_sum]
  interval_cases D <;> norm_num [Fin.sum_univ_succ]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_HaarAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem physical_fourBody_haar_allowance (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : D+2 ≤ Q) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q r D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * sourceFockEnergy Q x := by
  have hi := integral_mono
    (linearMap_rotation_norm_integrable Q (physicalFourCopyEnd Q r D (by omega)) x)
    (integrable_finsetSum _ (fun (b : LocalFourIndex D) hb => linearMap_rotation_norm_integrable Q
      (sourcePairEnd Q b.val.1.val) x))
    (fun g => source_fourBody_normalized_allowance Q r D hr hor hQ (exteriorRotation Q g⁻¹ x))
  apply (mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))).trans_eq
  rw [integral_finsetSum _ (fun (b : LocalFourIndex D) hb => linearMap_rotation_norm_integrable Q _ x)]
  have hp (b : LocalFourIndex D) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q b.val.1.val (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
        sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨b.val.1.val,by have := b.val.1.isLt; omega⟩ x
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem physical_fourBody_haar_allowance_retained (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (hQ : 25 ≤ Q) (hD : D ≤ 23) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
      (physicalFourCopyEnd Q r D (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) ≤
      ((D+1)^2/4 : ℕ) * sourceFockEnergy Q x := by
  simpa only [localFourIndex_card_retained D hD] using
    physical_fourBody_haar_allowance Q r D hr hor (by omega) x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TotalAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem source_allowance_count_fin :
    (∑ n : Fin 23, ((n.val+2)/2) * ((n.val+2)^2/4)) = 10946 := by
  have he (n : ℕ) (f : ℕ → ℕ) :
      (∑ i ∈ Finset.range n, f i) = ((List.range n).map f).sum := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ,List.range_succ,List.map_append,
        List.sum_append,List.map_singleton,List.sum_singleton,ih]
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n+2)/2) * ((n+2)^2/4)) 23,he]
  exact Certificate.allowance_count

theorem physical_fourBody_total_haar_allowance (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (∑ d : Fin 23, ∑ i : Fin ((d.val+2)/2),
      (2*Q-2+1 : ℕ) * (∫ g, occupationNormSq Q
        (physicalFourCopyEnd Q (Certificate.copyLabel (D := d.val+1) i) (d.val+1) (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar)) ≤
      10946 * sourceFockEnergy Q x := by
  calc
    _ ≤ ∑ d : Fin 23, ∑ _i : Fin ((d.val+2)/2),
        ((d.val+2)^2/4 : ℕ) * sourceFockEnergy Q x := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro i hi
      exact physical_fourBody_haar_allowance_retained Q (Certificate.copyLabel (D := d.val+1) i) (d.val+1)
        (by unfold Certificate.copyLabel; have := i.isLt; omega)
        (by exact ⟨i.val,by unfold Certificate.copyLabel; omega⟩) hQ (by omega) x
    _ = 10946 * sourceFockEnergy Q x := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_assoc,
        ← Nat.cast_mul,← Finset.sum_mul,← Nat.cast_sum,source_allowance_count_fin,Nat.cast_ofNat]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CopyFormAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

theorem retainedFourAllowance_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourAllowance Q hQ x ≤ 10946*sourceFockEnergy Q x := by
  unfold retainedFourAllowance
  simp_rw [fourCopyForm_allowance_identity]
  exact physical_fourBody_total_haar_allowance Q hQ x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_GlobalFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem physical_fourBody_global_Fock_haar (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (∫ g, contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)
      (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
    ∑ d : Fin 23, (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) *
      contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q (d.val+1) (by omega)
          (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))) x := by
  rw [contractionForm_haar Q (fourBodySpinRepresentation Q)
    (fourBodySpinRepresentation_inv Q) (fourBodySpinRepresentation_continuous Q)
    _ (sourceFourFamilyEnd_rotation Q (by omega)),physicalFourBodyHaar_retained_sum Q hQ,
    contractionForm_sum]
  simp only [contractionForm_smul]

theorem sourceA4Form_retained (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x = ∑ d : Fin 23,
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q (d.val+1) (by omega)
            (fun r s => physicalFourError Q (d.val+1) (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  rw [sourceA4Form,physical_fourBody_global_Fock_haar Q hQ x,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : (1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℂ)) =
      ((1 / ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MiddleForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem contractionForm_add {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M+N) x = contractionForm Q L M x+contractionForm Q L N x := by
  simp only [contractionForm,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem contractionForm_sub {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (M N : Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (M-N) x = contractionForm Q L M x-contractionForm Q L N x := by
  simp only [contractionForm,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

theorem fourCopyMiddleForm (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) (x : Space Q) :
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q) (fourCopyOperator Q D hQ (finiteFourMiddle Q D)) x).re =
    (contractionForm Q (sourceFourFamilyEnd Q)
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
        (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ) x).re +
    (3/10^6 : ℝ) * (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (∑ r : OddPairLabel D, (contractionForm Q (sourceFourFamilyEnd Q)
        (retainedFourInclusion Q D hQ r*(retainedFourInclusion Q D hQ r)ᴴ) x).re) -
    (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*D : ℕ) : ℝ)) *
      (contractionForm Q (sourceFourFamilyEnd Q)
        (fourCopyOperator Q D hQ (fun r s => physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s))) x).re := by
  rw [fourCopyOperator_middle Q D hQ hD,contractionForm_sub,contractionForm_add]
  simp only [contractionForm_smul,contractionForm_sum,Complex.sub_re,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum]
  rw [fourDimensionRatio_exact Q D hQ]
  have ha : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : ((4*Q-1-2*D : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 4*Q-1-2*D ≠ 0 by omega)
  field_simp

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

theorem sourceA4Form_retained_bound_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
      (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := physical_fourBody_total_haar_transfer Q hQ x
  have ha := retainedFourAllowance_bound Q hQ x
  have he : (∑ d : Fin 23,
      (((2*Q-2+1 : ℕ) : ℝ)/((4*Q-1-2*(d.val+1) : ℕ) : ℝ)) *
        (contractionForm Q (sourceFourFamilyEnd Q)
          (fourCopyOperator Q (d.val+1) (by omega) (finiteFourMiddle Q (d.val+1))) x).re) =
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    conv_lhs => arg 2; ext d; erw [fourCopyMiddleForm Q _ (by omega) (by omega) x]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sourceA4Form_retained Q hQ x]
    unfold retainedFourTarget retainedFourAllowance
    rw [Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hi : -(averagedFourTransferError Q*sourceFockEnergy Q x) ≤
      retainedFourTarget Q hQ x+(3/10^6 : ℝ)*retainedFourAllowance Q hQ x-sourceA4Form Q x := by
    rw [← he]
    conv_rhs => arg 2; ext d; erw [fourCopyForm_scaled_haar]
    exact ht
  nlinarith

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceA4Form_retained_bound_oai := @OAI.Laughlin.Fock.sourceA4Form_retained_bound_oai
