-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceKForm_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:37:22.637831+00:00
-- url     : https://prove2.me/submissions/29826c71-3f96-429b-a97e-ab5ddb778c01

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Theorems.Thm_OAI_Laughlin_Fock_physical_twoBody_certificate_haar

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q)) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

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

theorem annihilate_sq {Q : ℕ} (i : Fin (Q+1)) : annihilate i * annihilate i = 0 := by
  have h : (2 : ℂ) • (annihilate i * annihilate i) = 0 := by
    simpa only [two_smul] using annihilate_anticommute i i
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

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
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Representation
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
-- module Solutions.OAIQ047_LA.Laughlin_Operators_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_create {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j = delta i j • (1 : Module.End ℂ (Space Q)) -
      create j * annihilate i := by
  exact eq_sub_of_add_eq (mixed_car i j)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_sub_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y-z) = occupationInner Q x y-occupationInner Q x z := by
  simp [occupationInner,mul_sub,Finset.sum_sub_distrib]

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_NormalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem annihilate_create_inner (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

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
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_HighestFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

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

end Laughlin.Fock

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

theorem fourWedgeUnit_zero (Q p j k : ℕ) (hkj : k ≤ j) : fourWedgeUnit Q p j k=0 := by
  funext i
  have h := i.2.property
  simp only [fourWedgeUnit,Pi.zero_apply]
  rw [ite_eq_right (by rintro ⟨_,hj,hk⟩; change i.2.val.1.val < i.2.val.2.val at h; omega)]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_NormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix

theorem fourWedgeUnit_family_sum (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (hjk : j < k) (v : FourWedgeIndex Q → Space Q) :
    (∑ i, (fourWedgeUnit Q p j k i : ℂ) • v i) =
      v (⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
  have he (i : FourWedgeIndex Q) :
      (i.1.val=p ∧ i.2.val.1.val=j ∧ i.2.val.2.val=k) ↔
        i=(⟨p,hp⟩,⟨(⟨j,by omega⟩,⟨k,by omega⟩),hjk⟩) := by
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h3)))
    · intro h; subst i; exact ⟨rfl,rfl,rfl⟩
  simp only [fourWedgeUnit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,ite_smul,one_smul,zero_smul]
  simp_rw [he]
  simp

theorem sourceFourEnd_swap (Q p : ℕ) (j k : Fin (Q+1)) :
    sourceFourEnd Q p k j = -sourceFourEnd Q p j k := by
  have h : annihilate j*annihilate k = -(annihilate k*annihilate j) :=
    eq_neg_of_add_eq_zero_left (annihilate_anticommute j k)
  rw [sourceFourEnd,sourceFourEnd,h]
  ext x
  rfl

theorem fourSignedUnit_family_sum (Q p j k : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q) (hk : k ≤ Q)
    (x : Space Q) :
    (∑ i, (fourSignedUnit Q p j k i : ℂ) • sourceFourFamilyEnd Q i x) =
      sourceFourEnd Q p ⟨j,by omega⟩ ⟨k,by omega⟩ x := by
  simp only [fourSignedUnit,Pi.sub_apply,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  rcases lt_trichotomy j k with h | h | h
  · rw [fourWedgeUnit_family_sum Q p j k hp hj hk h,fourWedgeUnit_zero Q p k j (by omega)]
    simp only [Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,sub_zero]
    rfl
  · subst k
    rw [sub_self]
    simp only [sourceFourEnd,annihilate_sq,zero_mul,LinearMap.zero_apply]
  · rw [fourWedgeUnit_zero Q p j k (by omega),fourWedgeUnit_family_sum Q p k j hp hk hj h]
    simp only [Pi.zero_apply,Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,zero_sub,
      sourceFourFamilyEnd,sourceFourEnd_swap Q p ⟨j,by omega⟩ ⟨k,by omega⟩,
      LinearMap.neg_apply,neg_neg]

theorem fourBodyTermMatrix_Fock (Q t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hQ : e.1+e.2.1+(f.1+f.2.1-t)+2 ≤ Q) (x : Space Q) :
    contractionForm Q (sourceFourFamilyEnd Q) ((fourBodyTermMatrix Q t e f).map Complex.ofReal) x =
      -(sourceAlpha t e * sourceAlpha t f : ℝ) * occupationInner Q
        (sourceFourEnd Q e.1 ⟨e.2.1,by omega⟩ ⟨f.1+f.2.1-t,by omega⟩ x)
        (sourceFourEnd Q f.1 ⟨f.2.1,by omega⟩ ⟨e.1+e.2.1-t,by omega⟩ x) := by
  have hm : (fourBodyTermMatrix Q t e f).map Complex.ofReal =
      (-(sourceAlpha t e * sourceAlpha t f : ℝ) : ℂ) •
        complexOuter (fun i => (fourSignedUnit Q e.1 e.2.1 (f.1+f.2.1-t) i : ℂ))
          (fun i => (fourSignedUnit Q f.1 f.2.1 (e.1+e.2.1-t) i : ℂ)) := by
    ext i j
    simp [fourBodyTermMatrix,realOuter,complexOuter]
  rw [hm,contractionForm_smul,contractionForm_outer_cross]
  simp only [Complex.star_def,Complex.conj_ofReal]
  rw [fourSignedUnit_family_sum Q e.1 e.2.1 (f.1+f.2.1-t) (by omega) (by omega) (by omega),
    fourSignedUnit_family_sum Q f.1 f.2.1 (e.1+e.2.1-t) (by omega) (by omega) (by omega)]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_RowNormalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem create_create_inner (Q : ℕ) (i j : Fin (Q+1)) (y z : Space Q) :
    occupationInner Q (create i y) (create j z) =
      delta i j * occupationInner Q y z -
        occupationInner Q (annihilate j y) (annihilate i z) := by
  rw [create_annihilate_adjoint]
  change occupationInner Q y ((annihilate i * create j) z) = _
  rw [annihilate_create]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
    Module.End.mul_apply,occupationInner_sub_right,occupationInner_smul_right,
    annihilate_create_inner]

theorem row_normal_square {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (m : I → Fin (Q+1)) (hm : Function.Injective m)
    (ell : ℝ) (u : Space Q) (v : I → Space Q) :
    (occupationNormSq Q ((ell : ℂ) • u + ∑ i, create (m i) (v i)) : ℂ) =
      (ell : ℂ)^2 * (occupationNormSq Q u : ℂ) +
      (∑ i, (ell : ℂ) * (occupationInner Q (annihilate (m i) u) (v i) +
        occupationInner Q (v i) (annihilate (m i) u))) +
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
  rw [← occupationInner_self]
  simp only [occupationInner_add_left,occupationInner_add_right,occupationInner_smul_left,
    occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal,
    occupationInner_sum_left,occupationInner_sum_right]
  have hd (i j : I) : delta (m i) (m j) = if i=j then (1 : ℂ) else 0 := by
    simp only [delta,hm.eq_iff]
  have he : (∑ i, ∑ j, occupationInner Q (create (m i) (v i)) (create (m j) (v j))) =
      (∑ i, (occupationNormSq Q (v i) : ℂ)) -
      ∑ i, ∑ j, occupationInner Q (annihilate (m j) (v i)) (annihilate (m i) (v j)) := by
    simp_rw [create_create_inner,hd]
    simp [Finset.sum_sub_distrib,occupationInner_self]
  rw [Finset.sum_comm] at he
  simp only [Finset.sum_add_distrib]
  rw [he]
  simp only [create_annihilate_adjoint,annihilate_create_inner,occupationInner_self,
    Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem pairOrbitalUnit_family_sum (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → Space Q) :
    (∑ i, (pairOrbitalUnit Q p j i : ℂ) • v i) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  have he (i : PairOrbitalIndex Q) : (i.1.val=p ∧ i.2.val=j) ↔
      i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp only [pairOrbitalUnit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
    ite_smul,one_smul,zero_smul,he]
  simp

theorem contractionForm_realOuter {I : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (u v : I → ℝ) (x : Space Q) :
    contractionForm Q L ((realOuter u v).map Complex.ofReal) x =
      occupationInner Q (∑ i, (u i : ℂ) • L i x) (∑ j, (v j : ℂ) • L j x) := by
  have he : (realOuter u v).map Complex.ofReal =
      complexOuter (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) := by
    ext i j
    simp [realOuter,complexOuter]
  rw [he,contractionForm_outer_cross]
  simp only [Complex.star_def,Complex.conj_ofReal]

theorem threeBodyLevelMatrix_Fock (Q t T : ℕ) (ell : ℤ)
    (entries : List (ℕ × ℕ × ℤ)) (ht : t < 2*Q-2+1) (hT : T-t ≤ Q) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q)
      ((threeBodyLevelMatrix Q t T ell entries).map Complex.ofReal) x =
      ((ell : ℂ)/10^7) *
        (occupationInner Q (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))
          (sourceRowLevel Q t T entries x) +
        occupationInner Q (sourceRowLevel Q t T entries x)
          (annihilate ⟨T-t,by omega⟩ (sourcePairEnd Q t x))) +
      (occupationNormSq Q (sourceRowLevel Q t T entries x) : ℂ) := by
  have hadd (M N : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (M+N).map Complex.ofReal = M.map Complex.ofReal + N.map Complex.ofReal := by
    ext i j; simp
  have hsmul (r : ℝ) (M : Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ) :
      (r • M).map Complex.ofReal = (r : ℂ) • M.map Complex.ofReal := by
    ext i j; simp
  simp only [threeBodyLevelMatrix,hadd,hsmul,contractionForm_add,contractionForm_smul,
    contractionForm_realOuter,pairOrbitalUnit_family_sum Q t (T-t) ht hT]
  simp only [sourceRowLevel,sourceThreeEnd,Module.End.mul_apply,occupationInner_self,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,
    Complex.ofReal_intCast]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem rowOutputMode_injective (Q t : ℕ) (hQ : 15 ≤ Q) :
    Function.Injective (rowOutputMode Q t hQ) := by
  intro T S h
  have he := congrArg Fin.val h
  dsimp [rowOutputMode] at he
  have hT := T.property
  have hS := S.property
  apply Subtype.ext
  apply Fin.ext
  omega

theorem sourceRowSquareVector_normal (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) +
      (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
        ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
      sourceRowFourForm Q hQ row x := by
  have h := row_normal_square Q (rowOutputMode Q row.1 hQ)
    (rowOutputMode_injective Q row.1 hQ) ((row.2.1 : ℝ)/10^7)
    (sourcePairEnd Q row.1 x) (fun T => sourceRowLevel Q row.1 T.val.val row.2.2 x)
  have hc : (((row.2.1 : ℝ)/10^7 : ℝ) : ℂ) = (row.2.1 : ℂ)/10^7 := by push_cast; rfl
  rw [hc] at h
  rw [sourceRowSquareVector,h]
  have hl (T : RowLevel row.1) := threeBodyLevelMatrix_Fock Q row.1 T.val.val
    row.2.1 row.2.2 (by omega) (by have hT := T.val.isLt; omega) x
  simp_rw [hl]
  simp only [sourceRowFourForm,rowOutputMode,Finset.sum_add_distrib]
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_SourceExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem source_threeBody_rows_support : ∀ row ∈ Certificate.rows,
    row.1 ≤ 7 ∧ ∀ e ∈ row.2.2, row.1 ≤ e.1+e.2.1 ∧ e.1+e.2.1 ≤ 15 ∧ e.1+e.2.1-row.1 ≤ 8 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem contractionForm_list {I J : Type*} [Fintype I] (Q : ℕ)
    (L : I → Module.End ℂ (Space Q)) (l : List J) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q L (l.map M).sum x = (l.map (fun j => contractionForm Q L (M j) x)).sum := by
  induction l with
  | nil => simp [contractionForm]
  | cons j l ih => simp only [List.map_cons,List.sum_cons,contractionForm_add,ih]

theorem matrix_ofReal_list {I J : Type*} (l : List J) (M : J → Matrix I I ℝ) :
    ((l.map M).sum).map Complex.ofReal = (l.map (fun j => (M j).map Complex.ofReal)).sum := by
  induction l with
  | nil => ext i j; simp
  | cons k l ih =>
    simp only [List.map_cons,List.sum_cons]
    have he (A B : Matrix I I ℝ) : (A+B).map Complex.ofReal =
        A.map Complex.ofReal+B.map Complex.ofReal := by ext i j; simp
    rw [he,ih]

theorem physicalThreeBodyMatrix_row_sum (Q : ℕ) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x =
      (Certificate.rows.map (fun row => ∑ T : RowLevel row.1,
        contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x)).sum := by
  simp only [physicalThreeBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1

theorem physicalPairRowMatrix_Fock (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (ht : row.1 ≤ 7) (x : Space Q) :
    contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
      (physicalPairRowMatrix Q row) x =
      ((row.2.1 : ℂ)/10^7)^2 * (occupationNormSq Q (sourcePairEnd Q row.1 x) : ℂ) := by
  let p : Fin (2*Q-2+1) := ⟨row.1,by omega⟩
  have he (i : Fin (2*Q-2+1)) : i.val=row.1 ↔ i=p := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst i; rfl
  simp only [contractionForm,physicalPairRowMatrix,he,ite_mul,zero_mul]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,occupationInner_self]
  rfl

theorem source_rows_normal_two_three (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      (Certificate.rows.map (fun row => sourceRowFourForm Q hQ row x)).sum := by
  rw [physicalTwoBodyMatrix,contractionForm_list,physicalThreeBodyMatrix_row_sum]
  have hr (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
      (occupationNormSq Q (sourceRowSquareVector Q hQ row x) : ℂ) =
        contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
          (physicalPairRowMatrix Q row) x +
        (∑ T : RowLevel row.1, contractionForm Q (sourceThreeEnd Q)
          ((threeBodyLevelMatrix Q row.1 T.val.val row.2.1 row.2.2).map Complex.ofReal) x) +
        sourceRowFourForm Q hQ row x := by
    have ht := (source_threeBody_rows_support row hrow).1
    rw [sourceRowSquareVector_normal Q hQ row ht,physicalPairRowMatrix_Fock Q hQ row ht]
  rw [List.map_congr_left hr]
  simp only [List.sum_map_add]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem sourceEntryThree_eq (Q : ℕ) (e : ℕ × ℕ × ℤ)
    (hp : e.1 < 2*Q-2+1) (hj : e.2.1 ≤ Q) (x : Space Q) :
    sourceEntryThree Q e x = annihilate ⟨e.2.1,by omega⟩ (sourcePairEnd Q e.1 x) := by
  rw [sourceEntryThree,pairOrbitalUnit_family_sum Q e.1 e.2.1 hp hj]
  rfl

theorem sourceRowLevel_entries (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) (x : Space Q) :
    sourceRowLevel Q t T entries x =
      (entries.map (fun e => if e.1+e.2.1=T then
        (sourceAlpha t e : ℂ) • sourceEntryThree Q e x else 0)).sum := by
  induction entries with
  | nil => simp [sourceRowLevel,threeBodyLevelVector]
  | cons e entries ih =>
    simp only [sourceRowLevel,threeBodyLevelVector,List.map_cons,List.sum_cons,
      Pi.add_apply,Complex.ofReal_add,add_smul,Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    by_cases h : e.1+e.2.1=T
    · simp only [ite_eq_left h,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,sourceEntryThree,
        Finset.smul_sum,smul_smul]
    · simp [h]

theorem occupationInner_list_left {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q (l.map f).sum x = (l.map (fun i => occupationInner Q (f i) x)).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_left,ih]

theorem occupationInner_list_right {I : Type*} (Q : ℕ) (l : List I)
    (f : I → Space Q) (x : Space Q) :
    occupationInner Q x (l.map f).sum = (l.map (fun i => occupationInner Q x (f i))).sum := by
  induction l with
  | nil => simp [occupationInner]
  | cons i l ih => simp only [List.map_cons,List.sum_cons,occupationInner_add_right,ih]

theorem finset_list_sum_swap {I J A : Type*} [AddCommMonoid A]
    (s : Finset I) (l : List J) (f : I → J → A) :
    (∑ i ∈ s, (l.map (f i)).sum) = (l.map (fun j => ∑ i ∈ s, f i j)).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

theorem rowLevel_sum_select {A : Type*} [AddCommMonoid A] (t n : ℕ)
    (ht : t ≤ n) (hn : n < 16) (f : RowLevel t → A) :
    (∑ T : RowLevel t, if n=T.val.val then f T else 0) = f ⟨⟨n,hn⟩,ht⟩ := by
  classical
  have he (T : RowLevel t) : n=T.val.val ↔ T=⟨⟨n,hn⟩,ht⟩ := by
    constructor
    · intro h; exact Subtype.ext (Fin.ext h.symm)
    · intro h; subst T; rfl
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Ungroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem boundedAnnihilate_rowOutput (Q t : ℕ) (hQ : 15 ≤ Q) (T : RowLevel t) :
    boundedAnnihilate Q (T.val.val-t) = annihilate (rowOutputMode Q t hQ T) := by
  have ht : T.val.val-t ≤ Q := by have h := T.val.isLt; omega
  rw [boundedAnnihilate,dite_eq_left ht]
  rfl

theorem linearMap_list_sum {I : Type*} (Q : ℕ) (L : Module.End ℂ (Space Q))
    (l : List I) (v : I → Space Q) :
    L (l.map v).sum = (l.map (fun i => L (v i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons,List.sum_cons,map_add,ih]

theorem sourceRowFourForm_entries (Q : ℕ) (hQ : 15 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows) (x : Space Q) :
    sourceRowFourForm Q hQ row x =
      (row.2.2.map (fun e => (row.2.2.map (fun f => sourceRowFourEntry Q row.1 e f x)).sum)).sum := by
  classical
  let term := fun (T S : RowLevel row.1) (e f : ℕ × ℕ × ℤ) =>
    if e.1+e.2.1=T.val.val then if f.1+f.2.1=S.val.val then
      -(sourceAlpha row.1 e : ℂ)*(sourceAlpha row.1 f : ℂ) * occupationInner Q
        (boundedAnnihilate Q (S.val.val-row.1) (sourceEntryThree Q e x))
        (boundedAnnihilate Q (T.val.val-row.1) (sourceEntryThree Q f x)) else 0 else 0
  have ht (T S : RowLevel row.1) :
      -occupationInner Q
        (annihilate (rowOutputMode Q row.1 hQ S) (sourceRowLevel Q row.1 T.val.val row.2.2 x))
        (annihilate (rowOutputMode Q row.1 hQ T) (sourceRowLevel Q row.1 S.val.val row.2.2 x)) =
      (row.2.2.map (fun e => (row.2.2.map (fun f => term T S e f)).sum)).sum := by
    rw [← boundedAnnihilate_rowOutput,← boundedAnnihilate_rowOutput]
    simp only [sourceRowLevel_entries,linearMap_list_sum]
    rw [occupationInner_list_left]
    simp_rw [occupationInner_list_right]
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [List.sum_neg]
    simp only [List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro f hf
    dsimp only [term]
    by_cases heT : e.1+e.2.1=T.val.val <;> by_cases hfS : f.1+f.2.1=S.val.val
    · simp only [ite_eq_left heT,ite_eq_left hfS,map_smul,occupationInner_smul_left,
        occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal]
      ring
    all_goals simp [heT,hfS,occupationInner]
  rw [sourceRowFourForm,← Finset.sum_neg_distrib]
  simp only [← Finset.sum_neg_distrib,ht]
  simp_rw [finset_list_sum_swap]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  obtain ⟨hft,hf15,hf8⟩ := (source_threeBody_rows_support row hr).2 f hf
  simp only [term,Finset.sum_ite_irrel,Finset.sum_const_zero]
  rw [rowLevel_sum_select row.1 (e.1+e.2.1) het (by omega)]
  rw [rowLevel_sum_select row.1 (f.1+f.2.1) hft (by omega)]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_NormalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem sourceRowFourEntry_physical (Q : ℕ) (hQ : 25 ≤ Q)
    (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hr : row ∈ Certificate.rows)
    (e f : ℕ × ℕ × ℤ) (he : e ∈ row.2.2) (hf : f ∈ row.2.2) (x : Space Q) :
    sourceRowFourEntry Q row.1 e f x = contractionForm Q (sourceFourFamilyEnd Q)
      ((fourBodyTermMatrix Q row.1 e f).map Complex.ofReal) x := by
  obtain ⟨het,he15,he8⟩ := (source_threeBody_rows_support row hr).2 e he
  obtain ⟨hft,hf15,hf8⟩ := (source_threeBody_rows_support row hr).2 f hf
  rw [fourBodyTermMatrix_Fock Q row.1 e f het hft (by omega),sourceRowFourEntry,
    boundedAnnihilate,dite_eq_left (show f.1+f.2.1-row.1 ≤ Q by omega),
    boundedAnnihilate,dite_eq_left (show e.1+e.2.1-row.1 ≤ Q by omega),
    sourceEntryThree_eq Q e (by omega) (by omega),sourceEntryThree_eq Q f (by omega) (by omega)]
  simp only [sourceFourEnd,Module.End.mul_apply,Complex.ofReal_mul]
  ring

theorem source_rows_four_form (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => sourceRowFourForm Q (by omega) row x)).sum =
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  simp only [physicalFourBodyMatrix,matrix_ofReal_list,contractionForm_list]
  congr 1
  apply List.map_congr_left
  intro row hr
  rw [sourceRowFourForm_entries Q (by omega) row hr]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  exact sourceRowFourEntry_physical Q hQ row hr e f he hf x

theorem source_seven_squares_normal_form (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (Certificate.rows.map (fun row => (occupationNormSq Q
      (sourceRowSquareVector Q (by omega) row x) : ℂ))).sum =
      contractionForm Q (fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val)
        (physicalTwoBodyMatrix Q) x +
      contractionForm Q (sourceThreeEnd Q) ((physicalThreeBodyMatrix Q).map Complex.ofReal) x +
      contractionForm Q (sourceFourFamilyEnd Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) x := by
  rw [source_rows_normal_two_three Q (by omega),source_rows_four_form Q hQ]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_SevenSquareAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_rotation_integrable {I : Type*} [Fintype I]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (M : Matrix I I ℂ) (x : Space Q) :
    Integrable (fun g : SourceSU2 => contractionForm Q L M (exteriorRotation Q g⁻¹ x)) sourceHaar := by
  unfold contractionForm
  exact integrable_finsetSum _ (fun i hi => integrable_finsetSum _
    (fun j hj => (linearMap_rotation_inner_integrable Q (L i) (L j) x).const_mul _))

theorem sourceKForm_decomposition_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceKForm Q (by omega) x = (93527408868499/10^14 : ℝ)*sourceFockEnergy Q x +
      sourceA3Form Q x + sourceA4Form Q x := by
  let L2 := fun p : Fin (2*Q-2+1) => sourcePairEnd Q p.val
  let M2 := physicalTwoBodyMatrix Q
  let M3 := (physicalThreeBodyMatrix Q).map Complex.ofReal
  let M4 := (physicalFourBodyMatrix Q).map Complex.ofReal
  have hp (y : Space Q) :
      (Certificate.rows.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum =
      (contractionForm Q L2 M2 y + contractionForm Q (sourceThreeEnd Q) M3 y +
        contractionForm Q (sourceFourFamilyEnd Q) M4 y).re := by
    have h := congrArg Complex.re (source_seven_squares_normal_form Q hQ y)
    have hs (l : List (ℕ × ℤ × List (ℕ × ℕ × ℤ))) :
        (l.map (fun row => (occupationNormSq Q (sourceRowSquareVector Q (by omega) row y) : ℂ))).sum.re =
          (l.map (fun row => occupationNormSq Q (sourceRowSquareVector Q (by omega) row y))).sum := by
      induction l with
      | nil => simp
      | cons row l ih => simp only [List.map_cons,List.sum_cons,Complex.add_re,Complex.ofReal_re,ih]
    rw [hs] at h
    exact h
  have hi2 := contractionForm_rotation_integrable Q L2 M2 x
  have hi3 := contractionForm_rotation_integrable Q (sourceThreeEnd Q) M3 x
  have hi4 := contractionForm_rotation_integrable Q (sourceFourFamilyEnd Q) M4 x
  have h2 := congrArg Complex.re (physical_twoBody_certificate_haar Q (by omega) x)
  norm_num [Complex.mul_re] at h2
  rw [sourceKForm]
  simp_rw [hp]
  have hre := integral_re ((hi2.add hi3).add hi4)
  change (∫ g, (contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x)).re ∂sourceHaar) =
    (∫ g, contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceFourFamilyEnd Q) M4 (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re at hre
  have hi23 : Integrable (fun g : SourceSU2 =>
      contractionForm Q L2 M2 (exteriorRotation Q g⁻¹ x) +
      contractionForm Q (sourceThreeEnd Q) M3 (exteriorRotation Q g⁻¹ x)) sourceHaar := hi2.add hi3
  rw [hre,integral_add hi23 hi4,
    integral_add hi2 hi3,Complex.add_re,Complex.add_re]
  change _ = _ + ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceThreeEnd Q) M3
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re +
    ((2*Q-2+1 : ℕ) : ℝ) * (∫ g, contractionForm Q (sourceFourFamilyEnd Q) M4
    (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re
  rw [mul_add,mul_add]
  congr 2
  norm_num [L2,M2]
  exact h2

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceKForm_decomposition_oai := @OAI.Laughlin.Fock.sourceKForm_decomposition_oai
