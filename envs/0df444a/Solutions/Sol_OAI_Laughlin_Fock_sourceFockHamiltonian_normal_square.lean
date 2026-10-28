-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:58.479398+00:00
-- url     : https://prove2.me/submissions/a48394a7-f300-4b2b-819f-0b5632722a6e

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002

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
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_SpinUnitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationInner_add_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y+z) = occupationInner Q x y+occupationInner Q x z := by
  simp [occupationInner,mul_add,Finset.sum_add_distrib]

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

theorem sourceFockHamiltonian_apply_fin (Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairVector Q p.val * sourcePairEnd Q p.val x := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,sourcePairCreateEnd_mul]
  rw [show 2*Q-1=2*Q-2+1 by omega]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_NormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_create_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j : Fin (Q+1)) :
    pairEnd Q c * create i * create j =
      (c i j-c j i) • (1 : Module.End ℂ (Space Q)) -
      (∑ b, (c i b-c b i) • (create j * annihilate b)) +
      (∑ b, (c j b-c b j) • (create i * annihilate b)) +
      create i * create j * pairEnd Q c := by
  classical
  simp only [pairEnd,Finset.sum_mul,smul_mul_assoc,normal_order_four,
    smul_add,smul_sub,smul_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [delta,mul_ite,mul_one,mul_zero,ite_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,mul_smul_comm]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,mul_assoc]
  have hs (a b : ℂ) (v : Module.End ℂ (Space Q)) : (a-b) • v = a • v-b • v := by
    apply LinearMap.ext
    intro x
    exact sub_smul a b (v x)
  simp only [hs,Finset.sum_sub_distrib]
  module

theorem pairEnd_annihilate_commute (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i : Fin (Q+1)) : pairEnd Q c * annihilate i = annihilate i * pairEnd Q c := by
  have h (a b : Fin (Q+1)) : annihilate b * annihilate a * annihilate i =
      annihilate i * (annihilate b * annihilate a) := by
    calc
      _ = annihilate b * (annihilate a * annihilate i) := mul_assoc _ _ _
      _ = annihilate b * -(annihilate i * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute a i)]
      _ = -(annihilate b * (annihilate i * annihilate a)) := by
        apply LinearMap.ext
        intro x
        exact map_neg (annihilate b) ((annihilate i * annihilate a) x)
      _ = -((annihilate b * annihilate i) * annihilate a) := by rw [mul_assoc]
      _ = -(-(annihilate i * annihilate b) * annihilate a) := by rw [eq_neg_of_add_eq_zero_left (annihilate_anticommute b i)]
      _ = _ := by
        apply LinearMap.ext
        intro x
        change -(-(annihilate i (annihilate b (annihilate a x)))) = _
        exact neg_neg _
  simp only [pairEnd,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,h]

theorem pairEnd_commute (Q : ℕ) (c d : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q c * pairEnd Q d = pairEnd Q d * pairEnd Q c := by
  conv_lhs => arg 2; unfold pairEnd
  conv_rhs => arg 1; unfold pairEnd
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ← mul_assoc,pairEnd_annihilate_commute]
  simp only [mul_assoc,pairEnd_annihilate_commute]

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

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PairNormalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourcePair_normal_order (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    sourcePairEnd Q p * sourcePairCreateEnd Q q =
      (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) -
      (2 : ℂ) • (∑ i, ∑ j, ∑ t,
        ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
          (create i * annihilate j)) +
      sourcePairCreateEnd Q q * sourcePairEnd Q p := by
  let F : Module.End ℂ (Space Q) := ∑ i, ∑ j,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i j : ℂ)) • 1
  let U : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ)) • (create j * annihilate b)
  let V : Module.End ℂ (Space Q) := ∑ i, ∑ j, ∑ b,
    ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p j b : ℂ)) • (create i * annihilate b)
  have hexp : sourcePairEnd Q p * sourcePairCreateEnd Q q =
      F-U+V+sourcePairCreateEnd Q q * sourcePairEnd Q p := by
    simp only [sourcePairCreateEnd,pairCreateEnd,Complex.star_def,Complex.conj_ofReal,
      Finset.mul_sum,mul_smul_comm,← mul_assoc,sourcePairEnd,pairEnd_create_create,
      smul_add,smul_sub,Finset.smul_sum,smul_smul,pair_weight_product,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,
      Finset.sum_mul,smul_mul_assoc,F,U,V]
  have hF : F = (if p=q then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
    dsimp [F]
    simp only [← Finset.sum_smul]
    have hg := congrArg Complex.ofReal (pairCoefficient_gram Q p q hQ hp)
    push_cast at hg
    congr 1
    by_cases he : p=q <;> simpa [he,mul_comm] using hg
  have hV : V = -U := by
    dsimp [V,U]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro b hb
    rw [pairCoefficient_swap Q q i j]
    simp only [Complex.ofReal_neg,neg_mul]
    apply LinearMap.ext
    intro x
    exact neg_smul ((pairCoefficient Q q i j : ℂ)*(pairCoefficient Q p i b : ℂ))
      ((create j * annihilate b) x)
  have hU : U = ∑ i, ∑ j, ∑ t,
      ((pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ)) •
        (create i * annihilate j) := by
    dsimp [U]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro t ht
    rw [pairCoefficient_swap Q q t i,pairCoefficient_swap Q p t j]
    simp [mul_comm]
  rw [hexp,hF,hV,hU]
  module

theorem complexThreeGram_sub_one_entry (Q : ℕ) (a b : Spin.PairOrbitalIndex Q) :
    (complexThreeGram Q-1) a b = -2 * ∑ t,
      (pairCoefficient Q a.1.val b.2 t : ℂ)*(pairCoefficient Q b.1.val a.2 t : ℂ) := by
  simp only [complexThreeGram,Spin.threeGram,Matrix.sub_apply,Matrix.smul_apply,
    smul_eq_mul,Spin.swapCompression_entry,Complex.ofReal_sub,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_sum]
  have h : ((1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℝ) a b : ℂ) =
      (1 : Matrix (Spin.PairOrbitalIndex Q) (Spin.PairOrbitalIndex Q) ℂ) a b := by
    classical
    by_cases hab : a=b <;> simp [hab,Matrix.one_apply]
  rw [h]
  ring

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

theorem pair_annihilate_create_inner (Q p : ℕ) (x y : Space Q) :
    occupationInner Q x (sourcePairCreateEnd Q p y) =
      occupationInner Q (sourcePairEnd Q p x) y := by
  have h := congrArg star (pairCreate_pair_adjoint Q
    (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) y x)
  simpa only [occupationInner_star,sourcePairCreateEnd,sourcePairEnd] using h

theorem sourcePairCreate_inner (Q : ℕ) (hQ : 2 ≤ Q)
    (p q : Fin (2*Q-2+1)) (y z : Space Q) :
    occupationInner Q (sourcePairCreateEnd Q p.val y) (sourcePairCreateEnd Q q.val z) =
      (if p=q then (1 : ℂ) else 0) * occupationInner Q y z +
      (∑ i, ∑ j, (complexThreeGram Q-1) (p,i) (q,j) *
        occupationInner Q (annihilate i y) (annihilate j z)) +
      occupationInner Q (sourcePairEnd Q q.val y) (sourcePairEnd Q p.val z) := by
  rw [sourcePairCreateEnd,pairCreate_pair_adjoint]
  change occupationInner Q y ((sourcePairEnd Q p.val * sourcePairCreateEnd Q q.val) z) = _
  rw [sourcePair_normal_order Q p.val q.val hQ (by omega)]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_add_right,occupationInner_sub_right,occupationInner_smul_right,
    occupationInner_sum_right,annihilate_create_inner,pair_annihilate_create_inner,
    complexThreeGram_sub_one_entry,Finset.sum_mul,Finset.mul_sum]
  have he : p.val=q.val ↔ p=q := Fin.val_inj
  simp only [he]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

theorem sourceFockHamiltonian_normal_square_oai (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  have hc (p q : Fin (2*Q-2+1)) :
      sourcePairEnd Q p.val (sourcePairEnd Q q.val x) =
        sourcePairEnd Q q.val (sourcePairEnd Q p.val x) :=
    LinearMap.congr_fun (pairEnd_commute Q _ _) x
  have hH : sourceFockHamiltonian Q x = ∑ p : Fin (2*Q-2+1),
      sourcePairCreateEnd Q p.val (sourcePairEnd Q p.val x) := by
    rw [sourceFockHamiltonian_apply_fin Q (by omega)]
    simp only [sourcePairCreateEnd_mul]
  have he : (occupationNormSq Q (sourceFockHamiltonian Q x) : ℂ) =
      (sourceFockEnergy Q x : ℂ) +
      contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
    rw [← occupationInner_self,hH,occupationInner_sum_left]
    simp_rw [occupationInner_sum_right,sourcePairCreate_inner Q hQ]
    have hl (p q : Fin (2*Q-2+1)) : occupationInner Q
        (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))
        (sourcePairEnd Q p.val (sourcePairEnd Q q.val x)) =
        (occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) : ℂ) := by
      rw [hc p q,occupationInner_self]
    simp only [Finset.sum_add_distrib,hl]
    congr 1
    · congr 1
      · rw [sourceFockEnergy_eq_fin Q (by omega),Complex.ofReal_sum]
        simp [occupationInner_self]
      · simp only [contractionForm,Fintype.sum_prod_type,sourceThreeEnd,Module.End.mul_apply]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
  have hr := congrArg Complex.re he
  simpa only [Complex.add_re,Complex.ofReal_re,Complex.re_sum] using hr

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_oai := @OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_oai
