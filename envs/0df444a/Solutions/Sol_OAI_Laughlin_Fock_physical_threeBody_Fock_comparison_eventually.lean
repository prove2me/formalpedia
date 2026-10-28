-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:34:13.05893+00:00
-- url     : https://prove2.me/submissions/214c6b30-0051-46b3-b604-4098cba20e04

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Definitions.Def_OAIQ047L003
import Theorems.Thm_OAI_Laughlin_Fock_complexThreeSpinProjector_eigen
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_Fock_haar_real
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_projector_nonneg
import Theorems.Thm_OAI_Laughlin_Spin_source_threeBody_physical_traces_strict_eventually

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

theorem occupationNormSq_eq_zero (Q : ℕ) (x : Space Q) :
    occupationNormSq Q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hc : ∀ A, (occupationBasis Q).repr x A = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun A (_ : A ∈ Finset.univ) => sq_nonneg ‖(occupationBasis Q).repr x A‖)).mp h
      intro A
      have ha := hs A (Finset.mem_univ A)
      simpa using ha
    apply (occupationBasis Q).repr.injective
    ext A
    simp [hc]
  · intro h
    simp [h,occupationNormSq]

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

theorem normal_order_two_inner {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (annihilate b * create d) -
      delta b c • (annihilate a * create d) +
      create c * annihilate b * annihilate a * create d := by
  calc
    _ = annihilate b * (annihilate a * create c) * create d := by noncomm_ring
    _ = delta a c • (annihilate b * create d) -
        (annihilate b * create c) * annihilate a * create d := by
      rw [annihilate_create]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b c]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_NormalOrderFour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem normal_order_two_one {Q : ℕ} (a b d : Fin (Q+1)) :
    annihilate b * annihilate a * create d =
      delta a d • annihilate b - delta b d • annihilate a +
        create d * annihilate b * annihilate a := by
  calc
    _ = annihilate b * (annihilate a * create d) := by noncomm_ring
    _ = delta a d • annihilate b - (annihilate b * create d) * annihilate a := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one]
      noncomm_ring
    _ = _ := by
      rw [annihilate_create b d]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

theorem normal_order_four {Q : ℕ} (a b c d : Fin (Q+1)) :
    annihilate b * annihilate a * create c * create d =
      delta a c • (delta b d • (1 : Module.End ℂ (Space Q))) -
      delta b c • (delta a d • (1 : Module.End ℂ (Space Q))) -
      delta a c • (create d * annihilate b) +
      delta b c • (create d * annihilate a) +
      delta a d • (create c * annihilate b) -
      delta b d • (create c * annihilate a) +
      create c * create d * annihilate b * annihilate a := by
  rw [normal_order_two_inner, annihilate_create b d, annihilate_create a d]
  have h : create c * annihilate b * annihilate a * create d =
      create c * (annihilate b * annihilate a * create d) := by noncomm_ring
  rw [h, normal_order_two_one]
  simp only [smul_sub, mul_add, mul_sub, mul_smul_comm]
  noncomm_ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.PairNormalization
open scoped BigOperators
open Finset Finset.Nat

theorem binomial_convolution (m n k : ℕ) :
    (∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+n).choose k : ℝ) := by
  exact_mod_cast (Nat.add_choose_eq m n k).symm

theorem weighted_choose (m i : ℕ) :
    ((i+1 : ℕ) : ℝ) * ((m+1).choose (i+1) : ℝ) =
      ((m+1 : ℕ) : ℝ) * (m.choose i : ℝ) := by
  have h : (i+1) * (m+1).choose (i+1) = (m+1) * m.choose i := by
    simpa only [mul_comm] using (Nat.add_one_mul_choose_eq m i).symm
  exact_mod_cast h

theorem weighted_shift (m k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * f ij.1 ij.2) =
      ((m+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * f (ij.1+1) ij.2 := by
  rw [sum_antidiagonal_succ]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_first_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
      ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  rw [weighted_shift m k (fun _ j => (n.choose j : ℝ)), binomial_convolution]

theorem weighted_shift_right (n k : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ) * f ij.1 ij.2) =
      ((n+1 : ℕ) : ℝ) *
        ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * f ij.1 (ij.2+1) := by
  rw [sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  dsimp only
  rw [weighted_choose]
  ring

theorem binomial_second_falling (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      ((m+2).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) =
    ((m+2 : ℕ) : ℝ) * ((m+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+2).choose ij.1 : ℝ) *
          (((ij.1 : ℝ)-1) * (n.choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          ((m+1).choose ij.1 : ℝ) *
            (((ij.1+1 : ℕ) : ℝ)-1) * (n.choose ij.2 : ℝ) := by
      simpa only [mul_assoc] using weighted_shift (m+1) (k+1)
        (fun i j => ((i : ℝ)-1) * (n.choose j : ℝ))
    _ = ((m+2 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1),
          (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) * (n.choose ij.2 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      push_cast
      ring
    _ = _ := by rw [binomial_first_moment]; ring

theorem binomial_cross_moment (m n k : ℕ) :
    (∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * (ij.2 : ℝ) *
      ((m+1).choose ij.1 : ℝ) * ((n+1).choose ij.2 : ℝ)) =
    ((m+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ) * ((m+n).choose k : ℝ) := by
  calc
    _ = ∑ ij ∈ antidiagonal (k+2), (ij.1 : ℝ) * ((m+1).choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (m.choose ij.1 : ℝ) *
          ((ij.2 : ℝ) * ((n+1).choose ij.2 : ℝ)) :=
      weighted_shift m (k+1) (fun _ j => (j : ℝ) * ((n+1).choose j : ℝ))
    _ = ((m+1 : ℕ) : ℝ) * ∑ ij ∈ antidiagonal (k+1), (ij.2 : ℝ) *
          ((n+1).choose ij.2 : ℝ) * (m.choose ij.1 : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (n.choose ij.2 : ℝ) * (m.choose ij.1 : ℝ)) := by
      rw [weighted_shift_right n k (fun i _ => (m.choose i : ℝ))]
    _ = ((m+1 : ℕ) : ℝ) * (((n+1 : ℕ) : ℝ) *
          ∑ ij ∈ antidiagonal k, (m.choose ij.1 : ℝ) * (n.choose ij.2 : ℝ)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = _ := by rw [binomial_convolution]; ring

theorem difference_decomposition (Q n : ℕ) :
    (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
  have hfirst : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hfall : (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      ∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
        (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ) := by
    calc
      _ = ∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
          (Q.choose ij.2 : ℝ) * (Q.choose ij.1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro ij hij
        ring
      _ = _ := sum_antidiagonal_swap (n := n)
        (f := fun ij => (ij.1 : ℝ) * ((ij.1 : ℝ)-1) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ))
  have hpoint : (∑ ij ∈ antidiagonal n, ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * ((ij.1 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * ((ij.2 : ℝ)-1) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) +
    (∑ ij ∈ antidiagonal n, (ij.2 : ℝ) * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) -
    2 * (∑ ij ∈ antidiagonal n, (ij.1 : ℝ) * (ij.2 : ℝ) *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  rw [hpoint, hfirst, hfall]
  ring

theorem pair_binomial_moment (m p : ℕ) :
    (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      ((m+2).choose ij.1 : ℝ) * ((m+2).choose ij.2 : ℝ)) =
      2 * ((m+2 : ℕ) : ℝ) * ((2*m+2).choose p : ℝ) := by
  cases p with
  | zero =>
    rw [sum_antidiagonal_succ]
    simp [Nat.choose_one_right]
    ring
  | succ k =>
    rw [difference_decomposition, binomial_second_falling m (m+2) k,
      binomial_first_moment (m+1) (m+2) (k+1), binomial_cross_moment (m+1) (m+1) k]
    have hA : m+(m+2) = 2*m+2 := by omega
    have hB : m+1+(m+2) = (2*m+2)+1 := by omega
    have hC : m+1+(m+1) = 2*m+2 := by omega
    rw [hA, hB, hC]
    have hp : (((2*m+2)+1).choose (k+1) : ℝ) =
        ((2*m+2).choose k : ℝ) + ((2*m+2).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.choose_succ_succ (2*m+2) k
    rw [hp]
    push_cast
    ring

end Laughlin.PairNormalization

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_CoefficientSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairCoefficient_sq_choose (Q p : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    (pairCoefficient Q p x y)^2 =
      if x.val+y.val = p+1 then
        (((x.val : ℝ)-(y.val : ℝ))^2 * (Q.choose x.val : ℝ) * (Q.choose y.val : ℝ)) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
      else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs with h
  · rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators
open Finset Finset.Nat

theorem finite_pair_antidiagonal (Q n : ℕ) (f : ℕ → ℕ → ℝ)
    (hz : ∀ i j, Q < i ∨ Q < j → f i j = 0) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = n then f x.val y.val else 0) =
        ∑ ij ∈ antidiagonal n, f ij.1 ij.2 := by
  classical
  rw [← Fintype.sum_prod_type (f := fun a : Fin (Q+1) × Fin (Q+1) =>
    if a.1.val+a.2.val = n then f a.1.val a.2.val else 0)]
  refine Finset.sum_bij_ne_zero (fun a _ _ => (a.1.val,a.2.val)) ?_ ?_ ?_ ?_
  · intro a ha hn
    apply HasAntidiagonal.mem_antidiagonal.mpr
    by_contra h
    exact hn (by simp [h])
  · intro a ha hna b hb hnb hab
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hab)
    · exact Fin.ext (congrArg Prod.snd hab)
  · rintro ⟨i,j⟩ hij hn
    have hi : i < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inl (by omega)))
    have hj : j < Q+1 := by
      by_contra h
      exact hn (hz i j (Or.inr (by omega)))
    have hs : i+j = n := HasAntidiagonal.mem_antidiagonal.mp hij
    let a : Fin (Q+1) × Fin (Q+1) := (⟨i,hi⟩,⟨j,hj⟩)
    refine ⟨a, mem_univ a, ?_, rfl⟩
    simpa [a, hs] using hn
  · intro a ha hn
    have hs : a.1.val+a.2.val = n := by
      by_contra h
      exact hn (by simp [h])
    simp [hs]

theorem pairCoefficient_unit_norm (Q p : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1), (pairCoefficient Q p x y)^2) = 1 := by
  let f : ℕ → ℕ → ℝ := fun i j =>
    ((i : ℝ)-(j : ℝ))^2 * (Q.choose i : ℝ) * (Q.choose j : ℝ) /
      (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))
  have hz : ∀ i j, Q < i ∨ Q < j → f i j = 0 := by
    intro i j h
    rcases h with h | h
    · simp [f, Nat.choose_eq_zero_of_lt h]
    · simp [f, Nat.choose_eq_zero_of_lt h]
  simp_rw [pairCoefficient_sq_choose Q p (by omega) hp]
  change (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      if x.val+y.val = p+1 then f x.val y.val else 0) = 1
  rw [finite_pair_antidiagonal Q (p+1) f hz]
  simp only [f, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  have hmoment : (∑ ij ∈ antidiagonal (p+1), ((ij.1 : ℝ)-(ij.2 : ℝ))^2 *
      (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      2*(Q : ℝ)*((2*Q-2).choose p : ℝ) := by
    have h := PairNormalization.pair_binomial_moment (Q-2) p
    have h₁ : Q-2+2 = Q := by omega
    have h₂ : 2*(Q-2)+2 = 2*Q-2 := by omega
    simpa only [h₁, h₂] using h
  rw [hmoment]
  apply div_self
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  exact mul_ne_zero (mul_ne_zero (by norm_num) hq) hc

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Orthonormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_orthogonal (Q p q : ℕ) (hpq : p ≠ q) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hp : x.val+y.val = p+1
  · have hq : x.val+y.val ≠ q+1 := by omega
    simp [pairCoefficient, hq]
  · simp [pairCoefficient, hp]

theorem pairCoefficient_gram (Q p q : ℕ) (hQ : 2 ≤ Q)
    (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    simpa only [pow_two] using pairCoefficient_unit_norm Q p hQ hp
  · rw [ite_eq_right h]
    exact pairCoefficient_orthogonal Q p q h

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_PairNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_vacuum {Q : ℕ} (i : Fin (Q+1)) : annihilate i (1 : Space Q) = 0 := by
  simp [annihilate]

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_vacuum {Q : ℕ} (a i : Fin (Q+1)) :
    annihilate a (create i (1 : Space Q)) = delta a i • (1 : Space Q) := by
  have h := LinearMap.congr_fun (mixed_car a i) (1 : Space Q)
  by_cases ha : a = i <;> simpa [Module.End.mul_apply,annihilate_vacuum,delta,ha] using h

theorem two_annihilate_three_create {Q : ℕ} (a b i j k : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (create k (1 : Space Q))))) =
      (delta a i*delta b j-delta b i*delta a j) • create k (1 : Space Q) -
      (delta a i*delta b k-delta b i*delta a k) • create j (1 : Space Q) +
      (delta a j*delta b k-delta b j*delta a k) • create i (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (create k (1 : Space Q))
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,Module.End.one_apply,annihilate_create_vacuum,map_smul,
    annihilate_vacuum,smul_zero,map_zero,add_zero,smul_smul] at h
  rw [h]
  module

theorem pairEnd_three_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j k : Fin (Q+1)) :
    pairEnd Q c (create i (create j (create k (1 : Space Q)))) =
      (c i j-c j i) • create k (1 : Space Q) -
      (c i k-c k i) • create j (1 : Space Q) +
      (c j k-c k j) • create i (1 : Space Q) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    two_annihilate_three_create,smul_add,smul_sub,smul_smul]
  simp [delta,mul_sub,sub_smul,mul_ite,ite_smul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PairAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sourcePairCreate_apply (Q p : ℕ) (x : Space Q) :
    sourcePairCreateEnd Q p x = ∑ i, ∑ j,
      ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) • create i (create j x) := by
  simp [sourcePairCreateEnd,pairCreateEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]

theorem pair_weight_difference (Q p : ℕ) (i j : Fin (Q+1)) :
    pairCoefficient Q p i j / Real.sqrt 2 - pairCoefficient Q p j i / Real.sqrt 2 =
      Real.sqrt 2 * pairCoefficient Q p i j := by
  rw [pairCoefficient_swap Q p i j]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  calc
    _ = 2*pairCoefficient Q p i j / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2*Real.sqrt 2)*pairCoefficient Q p i j / Real.sqrt 2 := by
      rw [Real.mul_self_sqrt (by norm_num)]
    _ = _ := by field_simp

theorem pair_weight_product (Q p q : ℕ) (i j k l : Fin (Q+1)) :
    ((pairCoefficient Q q i j / Real.sqrt 2 : ℝ) : ℂ) *
      (((pairCoefficient Q p k l / Real.sqrt 2 : ℝ) : ℂ) -
       ((pairCoefficient Q p l k / Real.sqrt 2 : ℝ) : ℂ)) =
      (pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p k l : ℂ) := by
  rw [← Complex.ofReal_sub,pair_weight_difference]
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp

theorem sourcePair_threeBodyColumn (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (k : Fin (Q+1)) :
    sourcePairEnd Q p (threeBodyColumn Q q k) =
      (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) -
      (2 : ℂ) • (∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ) * (pairCoefficient Q p i k : ℂ)) •
        create j (1 : Space Q)) := by
  let F : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • create k (1 : Space Q)
  let U : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i k : ℂ)) • create j (1 : Space Q)
  let V : Space Q := ∑ i, ∑ j, ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j k : ℂ)) • create i (1 : Space Q)
  have hexp : sourcePairEnd Q p (threeBodyColumn Q q k) = F-U+V := by
    rw [threeBodyColumn,sourcePairCreate_apply]
    simp only [map_sum,map_smul,sourcePairEnd,pairEnd_three_create,
      smul_add,smul_sub,smul_smul,pair_weight_product]
    simp only [F,U,V,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hF : F = (if p = q then (1 : ℂ) else 0) • create k (1 : Space Q) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    rw [show (∑ i, ∑ j, (pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) =
      (if p = q then 1 else 0) by by_cases he : p = q <;> simpa [he,mul_comm] using hg]
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [pairCoefficient_swap Q q i j]
    simp
  rw [hexp,hF,hV]
  change _ = _ - (2 : ℂ) • U
  module

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

theorem occupationInner_oneMode (Q : ℕ) (i j : Fin (Q+1)) :
    occupationInner Q (create i (1 : Space Q)) (create j (1 : Space Q)) =
      if i = j then 1 else 0 := by
  have h (k : Fin (Q+1)) : create k (1 : Space Q) = occupationBasis Q {k} := by
    rw [occupation_singleton]
    simp [create]
  rw [h i,h j]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem threeBodyColumn_gram (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    occupationInner Q (threeBodyColumn Q p i) (threeBodyColumn Q q j) =
      (if p = q then (1 : ℂ) else 0)*(if i = j then (1 : ℂ) else 0) -
      2 * ∑ t, (pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ) := by
  rw [threeBodyColumn,sourcePairCreateEnd,pairCreate_pair_adjoint]
  change occupationInner Q (create i (1 : Space Q))
    (sourcePairEnd Q p (threeBodyColumn Q q j)) = _
  rw [sourcePair_threeBodyColumn Q p q hQ hp j,occupationInner_sub_right,
    occupationInner_smul_right,occupationInner_smul_right]
  simp only [occupationInner_sum_right,occupationInner_smul_right,occupationInner_oneMode]
  simp only [mul_ite,mul_one,mul_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [pairCoefficient_swap Q q i t,pairCoefficient_swap Q p j t]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_SpinCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem swapCompression_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    swapCompression Q a b = ∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  have he (i : TripleIndex Q) :
      ((tripleInclusion Q)ᵀ * swap23Matrix Q) a i = tripleInclusion Q (swap23 i) a := by
    have hi (k : TripleIndex Q) : swap23 k=i ↔ k=swap23 i := by
      constructor
      · intro h; simpa using congrArg swap23 h
      · intro h; rw [h,swap23_involutive]
    simp [Matrix.mul_apply,swap23Matrix,hi,Matrix.transpose_apply]
  unfold swapCompression
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [tripleInclusion,pairInclusion,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,swap23]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pairCoefficient_swap Q a.1.val t b.2,pairCoefficient_swap Q b.1.val t a.2]
  ring

theorem threeGram_entry (Q : ℕ) (a b : PairOrbitalIndex Q) :
    threeGram Q a b = (if a=b then 1 else 0) - 2*∑ t : Orbital Q,
      pairCoefficient Q a.1.val b.2 t * pairCoefficient Q b.1.val a.2 t := by
  simp only [threeGram,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,
    swapCompression_entry]

theorem threeGram_physical (Q : ℕ) (hQ : 2 ≤ Q) (a b : PairOrbitalIndex Q) :
    (threeGram Q a b : ℂ) =
      Fock.occupationInner Q (Fock.threeBodyColumn Q a.1.val a.2)
        (Fock.threeBodyColumn Q b.1.val b.2) := by
  rw [threeGram_entry,Fock.threeBodyColumn_gram Q a.1.val b.1.val hQ (by omega)]
  push_cast
  congr 1
  by_cases ha : a.1=b.1 <;> by_cases hb : a.2=b.2 <;>
    simp [Prod.ext_iff,ha,hb]
  simp_all [Fin.ext_iff]

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
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix Kronecker

theorem sourceThreeVector_adjoint (Q : ℕ) (i : PairOrbitalIndex Q) (x y : Space Q) :
    occupationInner Q (sourceThreeVector Q i*x) y =
      occupationInner Q x (sourceThreeEnd Q i y) := by
  have he : sourceThreeVector Q i*x = sourcePairVector Q i.1.val * create i.2 x := by
    change (sourcePairVector Q i.1.val * (ExteriorAlgebra.ι ℂ (mode i.2)*1))*x =
      sourcePairVector Q i.1.val * (ExteriorAlgebra.ι ℂ (mode i.2)*x)
    simp only [mul_one,mul_assoc]
  rw [he,sourcePairVector_adjoint,create_annihilate_adjoint]
  rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_NullFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem gramEigenvalueFormula_zero (Q : ℕ) : gramEigenvalueFormula Q 0 = -1 := by
  simp [gramEigenvalueFormula,fallingRatio]

theorem gramEigenvalueFormula_one (Q : ℕ) (hQ : 2 ≤ Q) : gramEigenvalueFormula Q 1 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hd : (2*(Q : ℝ)-2) ≠ 0 := by
    have h : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hq1 : -1+(Q : ℝ) ≠ 0 := by
    have hh : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  norm_num [gramEigenvalueFormula,fallingRatio,Nat.descFactorial]
  rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  ring_nf
  field_simp [hq1]
  ring

theorem descFactorial_three_real (n : ℕ) (hn : 2 ≤ n) :
    (n.descFactorial 3 : ℝ) = (n : ℝ)*(n-1)*(n-2) := by
  norm_num [Nat.descFactorial]
  rw [Nat.cast_sub hn,Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem gramEigenvalueFormula_three (Q : ℕ) (hQ : 3 ≤ Q) : gramEigenvalueFormula Q 3 = -1 := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have h : (3 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd₀ : (2*(Q : ℝ)-2) ≠ 0 := by linarith
  have hd₁ : (2*(Q : ℝ)-2-1) ≠ 0 := by linarith
  have hd₂ : (2*(Q : ℝ)-2-2) ≠ 0 := by linarith
  have hpoly : -6+(Q : ℝ)*13-(Q : ℝ)^2*9+(Q : ℝ)^3*2 ≠ 0 := by
    have hp : 0 < ((Q : ℝ)-1)*((Q : ℝ)-2)*(2*(Q : ℝ)-3) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    nlinarith
  unfold gramEigenvalueFormula fallingRatio
  rw [descFactorial_three_real Q (by omega),descFactorial_three_real (2*Q-2) (by omega),
    Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  norm_num
  field_simp
  ring_nf
  field_simp [hpoly]
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_PhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem threeWedge_inner (Q : ℕ) (hQ : 2 ≤ Q) (u v : Spin.PairOrbitalIndex Q → ℂ) :
    occupationInner Q (threeWedge Q u) (threeWedge Q v) =
      ∑ a, star (u a)*(complexThreeGram Q *ᵥ v) a := by
  unfold threeWedge
  rw [occupationInner_sum_left]
  simp_rw [occupationInner_smul_left,occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,complexThreeGram]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Spin.threeGram_physical Q hQ a b]
  ring

theorem threeWedge_zero_of_gram_zero (Q : ℕ) (hQ : 2 ≤ Q) (u : Spin.PairOrbitalIndex Q → ℂ)
    (hu : complexThreeGram Q *ᵥ u=0) : threeWedge Q u=0 := by
  apply (occupationNormSq_eq_zero Q _).mp
  apply Complex.ofReal_injective
  rw [← occupationInner_self,threeWedge_inner Q hQ,hu]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_NullSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem source_threeBody_null_sectors (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (u : Spin.PairOrbitalIndex Q → ℂ) :
    threeWedge Q (complexThreeSpinProjector Q hQ z *ᵥ u) = 0 := by
  have hval : gramEigenvalueFormula Q z.val = -1 := by
    rcases hz with hz | hz | hz
    · rw [hz,gramEigenvalueFormula_zero]
    · rw [hz,gramEigenvalueFormula_one Q hQ]
    · rw [hz,gramEigenvalueFormula_three Q (by omega)]
  apply threeWedge_zero_of_gram_zero Q hQ
  rw [Matrix.mulVec_mulVec,complexThreeSpinProjector_eigen,hval]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_FockNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix

theorem threeBodyColumn_sourceThreeVector (Q : ℕ) (i : PairOrbitalIndex Q) :
    threeBodyColumn Q i.1.val i.2 = sourceThreeVector Q i := by
  rw [threeBodyColumn,sourcePairCreateEnd_mul]
  rfl

theorem threeWedge_contraction_zero (Q : ℕ) (v : PairOrbitalIndex Q → ℂ)
    (hv : threeWedge Q v=0) (x : Space Q) :
    (∑ i, star (v i) • sourceThreeEnd Q i x)=0 := by
  apply occupationInner_ext_right Q
  intro y
  have h : occupationInner Q (threeWedge Q v*y) x =
      occupationInner Q y (∑ i, star (v i) • sourceThreeEnd Q i x) := by
    simp only [threeWedge,Finset.sum_mul,smul_mul_assoc,occupationInner_sum_left,
      occupationInner_smul_left,threeBodyColumn_sourceThreeVector,sourceThreeVector_adjoint,
      occupationInner_sum_right,occupationInner_smul_right]
  rw [← h,hv,zero_mul]
  simp [occupationInner]

theorem physical_threeBody_Fock_null (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1))
    (hz : z.val=0 ∨ z.val=1 ∨ z.val=3) (x : Space Q) :
    contractionForm Q (sourceThreeEnd Q) ((threeSpinProjector Q hQ z).map Complex.ofReal) x = 0 := by
  let R := (threeSpinProjector Q hQ z).map Complex.ofReal
  have hc (j : PairOrbitalIndex Q) : (∑ i, star (R i j) • sourceThreeEnd Q i x)=0 := by
    apply threeWedge_contraction_zero
    have h := source_threeBody_null_sectors Q hQ z hz (Pi.single j 1)
    have he : complexThreeSpinProjector Q hQ z *ᵥ Pi.single j 1 = (fun i => R i j) := by
      funext i
      simp [Matrix.mulVec,dotProduct,Pi.single_apply,complexThreeSpinProjector,R]
    rw [he] at h
    exact h
  have he : contractionForm Q (sourceThreeEnd Q) R x =
      ∑ j, occupationInner Q (∑ i, star (R i j) • sourceThreeEnd Q i x) (sourceThreeEnd Q j x) := by
    simp only [contractionForm,occupationInner_sum_left,occupationInner_smul_left,star_star]
    rw [Finset.sum_comm]
  change contractionForm Q (sourceThreeEnd Q) R x=0
  rw [he]
  simp only [hc]
  simp [occupationInner]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_ThreeBody_FockTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem threeBody_dimension_ratio (Q z : ℕ) (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    ((coupledWeight Q z+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) =
      (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) := by
  have hn : ((coupledWeight Q z+1 : ℕ) : ℝ)=3*(Q : ℝ)-1-2*(z : ℝ) := by
    unfold coupledWeight
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 3*Q)]
    push_cast
    ring
  have hd : ((2*Q-2+1 : ℕ) : ℝ)=2*(Q : ℝ)-1 := by
    rw [Nat.cast_add,Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  rw [hn,hd]

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

theorem physicalThreeBodyTraceFormula_high (Q z : ℕ) (hz : 15 < z) :
    physicalThreeBodyTraceFormula Q z=0 := by
  have he (t : ℕ) : (List.range 16).filter (fun T => max z t ≤ T) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro T hT
    simp only [List.mem_range] at hT
    simp only [decide_eq_true_eq,max_le_iff]
    omega
  simp only [physicalThreeBodyTraceFormula,threeBodyTraceFormula,he,List.map_nil,List.sum_nil,
    List.map_const',List.sum_replicate,nsmul_zero]

theorem physical_threeBody_Fock_comparison_eventually_oai :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 15 ≤ Q, ∀ x : Space Q,
      (2*Q-2+1 : ℕ) * (∫ g, contractionForm Q (sourceThreeEnd Q)
        ((physicalThreeBodyMatrix Q).map Complex.ofReal) (exteriorRotation Q g⁻¹ x) ∂sourceHaar).re ≤
      ∑ z : Fin (Q+1), if z.val ≤ 15 then gramEigenvalueFormula Q z.val *
        (contractionForm Q (sourceThreeEnd Q)
          ((threeSpinProjector Q (by omega) z).map Complex.ofReal) x).re else 0 := by
  filter_upwards [source_threeBody_physical_traces_strict_eventually] with Q h
  obtain ⟨hQ,hs⟩ := h
  refine ⟨hQ,fun x => ?_⟩
  rw [physical_threeBody_Fock_haar_real Q hQ,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  by_cases h15 : z.val ≤ 15
  · rw [ite_eq_left h15]
    by_cases hn : z.val=0 ∨ z.val=1 ∨ z.val=3
    · rw [physical_threeBody_Fock_null Q (by omega) z hn]
      simp
    · have hm : z.val ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15] := by
        simp only [List.mem_cons]
        omega
      have ht := hs z hm
      rw [source_physical_threeBody_trace_identity Q hQ] at ht
      have hr := threeBody_dimension_ratio Q z.val (by omega) (by omega)
      change _ = threeBodyDimensionRatio Q z.val at hr
      rw [← hr] at ht
      have ha : (0 : ℝ) < (2*Q-2+1 : ℕ) := by positivity
      have hd : (0 : ℝ) < (coupledWeight Q z.val+1 : ℕ) := by positivity
      have hc : (2*Q-2+1 : ℕ) *
          (physicalThreeBodyTraceFormula Q z.val/(coupledWeight Q z.val+1 : ℕ)) ≤
            gramEigenvalueFormula Q z.val := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hd).mpr
        have hh := mul_lt_mul_of_pos_left ht ha
        have he : ((2*Q-2+1 : ℕ) : ℝ) *
            (((coupledWeight Q z.val+1 : ℕ)/(2*Q-2+1 : ℕ) : ℝ) * gramEigenvalueFormula Q z.val) =
            gramEigenvalueFormula Q z.val*(coupledWeight Q z.val+1 : ℕ) := by
          field_simp
        rw [he] at hh
        exact hh.le
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
        (physical_threeBody_projector_nonneg Q (by omega) z x)
  · rw [ite_eq_right h15,physicalThreeBodyTraceFormula_high Q z.val (by omega)]
    simp

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_oai := @OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_oai
