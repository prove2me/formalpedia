-- Prove2me | solution 1 for OAI.Laughlin.mainTarget_proved
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:40:02.724777+00:00
-- url     : https://prove2.me/submissions/6a80be8a-c50b-4db1-9f56-fa41675e225f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Theorems.Thm_OAI_Laughlin_Fock_physical_fock_kernel_distance_uniform

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
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

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
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Bidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_empty (Q : ℕ) : occupationBasis Q ∅ = (1 : Space Q) := by
  let A : Set.powersetCard (Fin (Q+1)) 0 := ⟨∅,rfl⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra A.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_zero_apply]

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

theorem sourceFockHamiltonian_quadratic (Q : ℕ) (x : Space Q) :
    occupationInner Q (sourceFockHamiltonian Q x) x = (sourceFockEnergy Q x : ℂ) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,sourcePairCreateEnd,sourcePairEnd,pairCreate_pair_adjoint,
    occupationInner_self,sourceFockEnergy,Complex.ofReal_sum]

theorem sourceFockEnergy_eq_zero (Q : ℕ) (x : Space Q) :
    sourceFockEnergy Q x = 0 ↔ ∀ p ∈ Finset.range (2*Q-1), sourcePairEnd Q p x = 0 := by
  unfold sourceFockEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p hp => occupationNormSq_nonneg Q _)]
  simp only [occupationNormSq_eq_zero]

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

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_CARReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_create_apply (Q : ℕ) (a b : Fin (Q+1)) (x : Space Q) :
    annihilate a (create b x) = delta a b • x - create b (annihilate a x) := by
  have h := LinearMap.congr_fun (annihilate_create a b) x
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.one_apply] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_EnergyReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationNormSq_smul (Q : ℕ) (c : ℂ) (x : Space Q) :
    occupationNormSq Q (c • x) = ‖c‖^2 * occupationNormSq Q x := by
  simp [occupationNormSq,mul_pow,Finset.mul_sum]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_EigenvalueGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators

theorem sourceFockHamiltonian_kernel (Q : ℕ) (x : Space Q) :
    sourceFockHamiltonian Q x=0 ↔ sourceFockEnergy Q x=0 := by
  constructor
  · intro h
    have he := sourceFockHamiltonian_quadratic Q x
    rw [h] at he
    have hz : occupationInner Q 0 x=0 := by simp [occupationInner]
    rw [hz] at he
    exact Complex.ofReal_injective he.symm
  · intro h
    have he := (sourceFockEnergy_eq_zero Q x).mp h
    simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply]
    apply Finset.sum_eq_zero
    intro p hp
    rw [he p hp,map_zero]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_DiagonalCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.PairDiagonal
open Polynomial
open scoped Polynomial.Bivariate

theorem eval_swap_diagonal (p : Poly) :
    (Bivariate.swap p).eval (X : Polynomial ℂ) = p.eval X := by
  have he : (evalRingHom (X : Polynomial ℂ)).comp Bivariate.swap.toRingHom =
      evalRingHom (X : Polynomial ℂ) := by
    ext <;> simp [Bivariate.swap_X, Bivariate.swap_Y, Bivariate.swap_C_C]
  exact congrArg (fun f : Poly →+* Polynomial ℂ => f p) he

theorem antisymmetric_eval_zero (p : Poly) (ha : Bivariate.swap p = -p) :
    p.eval (X : Polynomial ℂ) = 0 := by
  have he := eval_swap_diagonal p
  rw [ha, eval_neg] at he
  have hz : (2 : ℂ) • p.eval (X : Polynomial ℂ) = 0 := by
    simp only [two_smul]
    calc
      _ = -p.eval (X : Polynomial ℂ) + p.eval X :=
        congrArg (fun z : Polynomial ℂ => z+p.eval X) he.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left two_ne_zero

theorem swap_diagonal : Bivariate.swap diagonal = -diagonal := by
  simp only [diagonal, map_sub, Bivariate.swap_X, Bivariate.swap_Y]
  ring

theorem cube_dvd_of_antisymmetric_first_jet (p : Poly)
    (ha : Bivariate.swap p = -p) (hj : p.derivative.eval (X : Polynomial ℂ) = 0) :
    diagonal^3 ∣ p := by
  have hd : diagonal ∣ p := by
    apply dvd_iff_isRoot.mpr
    exact antisymmetric_eval_zero p ha
  obtain ⟨g,hg⟩ := hd
  have hg0 : g.eval (X : Polynomial ℂ) = 0 := by
    rw [hg, derivative_mul] at hj
    simpa [diagonal] using hj
  have hdg : diagonal ∣ g := by
    apply dvd_iff_isRoot.mpr
    exact hg0
  obtain ⟨h,hh⟩ := hdg
  have hp : p = diagonal^2*h := by rw [hg,hh]; ring
  have hb : diagonal ≠ 0 := by
    exact X_sub_C_ne_zero (X : Polynomial ℂ)
  have hanti : Bivariate.swap h = -h := by
    rw [hp, map_mul, map_pow, swap_diagonal] at ha
    have hsq : (-diagonal)^2 = diagonal^2 := by ring
    rw [hsq] at ha
    apply mul_left_cancel₀ (pow_ne_zero 2 hb)
    calc
      _ = -(diagonal^2*h) := ha
      _ = _ := by ring
  have hdh : diagonal ∣ h := by
    apply dvd_iff_isRoot.mpr
    exact antisymmetric_eval_zero h hanti
  obtain ⟨k,hk⟩ := hdh
  refine ⟨k, ?_⟩
  rw [hp,hk]
  ring

end Laughlin.PairDiagonal

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Moment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_scaled (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairCoefficient Q p x y * pairNormalization Q p =
      if x.val+y.val = p+1 then ((x.val : ℝ)-(y.val : ℝ))*
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) else 0 := by
  have hd : pairNormalization Q p ≠ 0 := ne_of_gt (pairNormalization_pos Q p hQ hp)
  rw [pairCoefficient_choose Q p hQ hp]
  unfold pairNormalization at hd ⊢
  split_ifs
  · rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    field_simp
  · simp

theorem pairMoment_eq_amplitude (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairMoment Q p ψ = (pairNormalization Q p : ℂ)*
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) := by
  unfold pairMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have h := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_scaled Q p hQ hp x y)
  push_cast at h
  by_cases hs : x.val+y.val = p+1
  · rw [ite_eq_left hs] at h ⊢
    push_cast at h
    unfold weightedPairCoordinate
    push_cast
    calc
      _ = ((x.val : ℂ)-(y.val : ℂ))*(Real.sqrt (Q.choose x.val : ℝ) : ℂ)*
        (Real.sqrt (Q.choose y.val : ℝ) : ℂ)*ψ x y := by ring
      _ = _ := by rw [← h]; ring
  · rw [ite_eq_right hs]
    simp only [ite_eq_right hs, Complex.ofReal_zero] at h
    calc
      _ = ((pairCoefficient Q p x y : ℂ)*(pairNormalization Q p : ℂ))*ψ x y := by rw [h]; simp
      _ = _ := by ring

theorem weightedPairCoordinate_swap (Q : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) (x y : Fin (Q+1)) :
    weightedPairCoordinate Q ψ y x = -weightedPairCoordinate Q ψ x y := by
  unfold weightedPairCoordinate
  rw [ha]
  push_cast
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_MomentKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairMoment_zero_outside (Q p : ℕ) (hp : 2*Q-2 < p)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : pairMoment Q p ψ = 0 := by
  unfold pairMoment
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hs : x.val+y.val = p+1
  · rw [ite_eq_left hs]
    have hxy : x.val = y.val := by omega
    simp [hxy]
  · simp [hs]

theorem pairMoment_zero_of_pair_kernel (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hk : ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) (p : ℕ) :
    pairMoment Q p ψ = 0 := by
  by_cases hp : p ≤ 2*Q-2
  · rw [pairMoment_eq_amplitude Q p (by omega) hp ψ, hk p (by simpa using (show p < 2*Q-1 by omega)), mul_zero]
  · exact pairMoment_zero_outside Q p (by omega) ψ

theorem pair_jet_coefficient_zero (Q n : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) (hm : pairMoment Q n ψ = 0) :
    (∑ x, ∑ y, if x.val+y.val = n+1 then
      (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0) = 0 := by
  let I : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (x.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  let J : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  have hs : I = -J := by
    dsimp [I,J]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [weightedPairCoordinate_swap Q ψ ha x y, Nat.add_comm y.val x.val]
    split_ifs <;> ring
  have hmom : pairMoment Q n ψ = I-J := by
    dsimp [pairMoment,I,J]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs <;> ring
  have hz : (2 : ℂ)*J = 0 := by
    calc
      _ = -(I-J) := by rw [hs]; ring
      _ = 0 := by rw [← hmom, hm]; simp
  exact (mul_eq_zero.mp hz).resolve_left two_ne_zero

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_AffinePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators Polynomial.Bivariate

theorem pairAffinePolynomial_antisymmetric (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y) :
    Bivariate.swap (pairAffinePolynomial Q ψ) = -pairAffinePolynomial Q ψ := by
  unfold pairAffinePolynomial
  simp only [map_sum, Bivariate.swap_monomial_monomial]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [weightedPairCoordinate_swap Q ψ ha x y]
  simp

theorem diagonal_jet_monomial_coeff (i j n : ℕ) (a : ℂ) :
    ((monomial j (monomial i a)).derivative.eval (X : Polynomial ℂ)).coeff n =
      if i+j = n+1 then (j : ℂ)*a else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_monomial, eval_monomial]
    have hm : (monomial i a : Polynomial ℂ)*(j.succ : Polynomial ℂ) =
        monomial i (a*(j.succ : ℂ)) := by
      have hc : (j.succ : Polynomial ℂ) = C (j.succ : ℂ) := by simp
      rw [hc, monomial_mul_C]
    rw [Nat.succ_sub_one, hm, monomial_mul_X_pow, coeff_monomial]
    have he : i+j = n ↔ i+j.succ = n+1 := by omega
    simp only [he, mul_comm]

theorem pairAffinePolynomial_jet_coeff (Q n : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    ((pairAffinePolynomial Q ψ).derivative.eval (X : Polynomial ℂ)).coeff n =
      ∑ x, ∑ y, if x.val+y.val = n+1 then
        (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0 := by
  unfold pairAffinePolynomial
  simp only [derivative_sum, eval_finsetSum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  exact diagonal_jet_monomial_coeff x.val y.val n _

theorem pair_kernel_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y)
    (hk : ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) :
    PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ := by
  apply PairDiagonal.cube_dvd_of_antisymmetric_first_jet
  · exact pairAffinePolynomial_antisymmetric Q ψ ha
  · ext n
    rw [pairAffinePolynomial_jet_coeff, coeff_zero]
    exact pair_jet_coefficient_zero Q n ψ ha (pairMoment_zero_of_pair_kernel Q hQ ψ hk n)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Homogenize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem homogenize_dvd_of_degree_le {R : Type*} [CommRing R] [IsDomain R]
    {p q : Polynomial R} {n : ℕ} (hd : p ∣ q) (hn : q.natDegree ≤ n) :
    p.homogenize p.natDegree ∣ q.homogenize n := by
  have he : q.homogenize n = q.homogenize q.natDegree *
      (1 : Polynomial R).homogenize (n-q.natDegree) := by
    rw [← homogenize_mul q 1 le_rfl (by simp), mul_one,
      Nat.add_sub_of_le hn]
  rw [he]
  exact (homogenize_dvd hd).trans (dvd_mul_right _ _)

theorem homogeneousEval_monomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (n k : ℕ) (h : k ≤ n) (a : R) :
    homogeneousEval f u v n (monomial k a) = f a * v^k * u^(n-k) := by
  simp [homogeneousEval, homogenize_monomial h, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

theorem homogeneousEval_sum {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (n : ℕ) (s : Finset ι) (p : ι → Polynomial R) :
    homogeneousEval f u v n (∑ k ∈ s, p k) =
      ∑ k ∈ s, homogeneousEval f u v n (p k) := by
  simp [homogeneousEval]

theorem homogeneousEval_dvd {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (u v : S) {p q : Polynomial R} {n : ℕ}
    (hd : p ∣ q) (hn : q.natDegree ≤ n) :
    homogeneousEval f u v p.natDegree p ∣ homogeneousEval f u v n q :=
  MvPolynomial.eval₂_dvd _ _ (homogenize_dvd_of_degree_le hd hn)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_HomogeneousCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem homogeneousEval_cube {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (p : Polynomial R) (hp : p.natDegree ≤ 1) :
    homogeneousEval f u v 3 (p^3) = (homogeneousEval f u v 1 p)^3 := by
  have h := homogenize_finsetProd (s := Finset.range 3) (p := fun _ => p)
    (n := fun _ => 1) (fun _ _ => hp)
  have he : (p^3).homogenize 3 = (p.homogenize 1)^3 := by simpa using h
  simp [homogeneousEval, he]

theorem homogeneousEval_linear {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u v : S) (a b : R) :
    homogeneousEval f u v 1 (C a - X * C b) = f a * u - v * f b := by
  simp [homogeneousEval, homogenize_sub, show X * C b = C b * X by ring,
    MvPolynomial.eval₂_mul]
  ring

theorem linear_natDegree {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (hb : b ≠ 0) : (C a - X * C b).natDegree = 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_mul_le).trans (by simp)))
  · simpa using neg_ne_zero.mpr hb

theorem pairPartialPolynomial_expansion {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairPartialPolynomial f uj vj Q ψ = ∑ x, ∑ y,
      monomial x.val (f (weightedPairCoordinate Q ψ x y) * vj^y.val * uj^(Q-y.val)) := by
  unfold pairPartialPolynomial pairAffinePolynomial
  simp only [homogeneousEval_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [homogeneousEval_monomial _ _ _ _ _ (Nat.le_of_lt_succ y.isLt)]
  change (monomial x.val (weightedPairCoordinate Q ψ x y)).map f *
    C vj ^ y.val * C uj ^ (Q-y.val) = _
  simp only [map_monomial, ← map_pow, monomial_mul_C]

theorem pairPartialPolynomial_degree {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    (pairPartialPolynomial f uj vj Q ψ).natDegree ≤ Q := by
  rw [pairPartialPolynomial_expansion]
  apply natDegree_sum_le_of_forall_le
  intro x hx
  apply natDegree_sum_le_of_forall_le
  intro y hy
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ x.isLt)

theorem pairAffinePolynomial_degree (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    (pairAffinePolynomial Q ψ).natDegree ≤ Q := by
  apply natDegree_sum_le_of_forall_le
  intro x hx
  apply natDegree_sum_le_of_forall_le
  intro y hy
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ y.isLt)

theorem pairPartialPolynomial_cube {R : Type*} [CommRing R]
    (f : ℂ →+* R) (uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    (C vj - X * C uj)^3 ∣ pairPartialPolynomial f uj vj Q ψ := by
  have hd := homogeneousEval_dvd (Polynomial.mapRingHom f) (C uj) (C vj)
    hc (pairAffinePolynomial_degree Q ψ)
  have hdeg : (PairDiagonal.diagonal^3).natDegree = 3 := by
    simp [PairDiagonal.diagonal, natDegree_pow]
  rw [hdeg, homogeneousEval_cube _ _ _ _ (by simp [PairDiagonal.diagonal])] at hd
  have he : homogeneousEval (Polynomial.mapRingHom f) (C uj) (C vj) 1
      PairDiagonal.diagonal = C vj - X * C uj := by
    simp [homogeneousEval, PairDiagonal.diagonal]
  simpa only [he, pairPartialPolynomial] using hd

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem bracket_ne_zero {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    bracket i j ≠ 0 := by
  intro h
  let f : SpinorVariables N → ℂ := fun kb =>
    if (kb.1 = i ∧ kb.2 = false) ∨ (kb.1 = j ∧ kb.2 = true) then 1 else 0
  have := congrArg (MvPolynomial.eval f) h
  have hji : j ≠ i := Ne.symm hij
  simp [bracket, f, hij, hji] at this

theorem laughlinPolynomial_ne_zero (N : ℕ) : laughlinPolynomial N ≠ 0 := by
  classical
  unfold laughlinPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs with hij
  · exact pow_ne_zero 3 (bracket_ne_zero (ne_of_lt hij))
  · exact one_ne_zero

theorem bracket_cube_dvd_laughlin {N : ℕ} {i j : Fin N} (hij : i < j) :
    bracket i j ^ 3 ∣ laughlinPolynomial N := by
  classical
  unfold laughlinPolynomial
  have h₁ : bracket i j ^ 3 ∣ ∏ k : Fin N, if i < k then bracket i k ^ 3 else 1 := by
    simpa [hij] using
    (Finset.dvd_prod_of_mem (fun j => if i < j then bracket i j ^ 3 else 1)
      (Finset.mem_univ j))
  exact h₁.trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j : Fin N, if i < j then bracket i j ^ 3 else 1)
      (Finset.mem_univ i))

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_SpinorCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem pairSpinorPolynomial_homogeneousEval {R : Type*} [CommRing R]
    (f : ℂ →+* R) (ui vi uj vj : R) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairSpinorPolynomial f ui vi uj vj Q ψ =
      homogeneousEval (RingHom.id R) ui vi Q (pairPartialPolynomial f uj vj Q ψ) := by
  rw [pairPartialPolynomial_expansion]
  simp only [homogeneousEval_sum, pairSpinorPolynomial]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [homogeneousEval_monomial _ _ _ _ _ (Nat.le_of_lt_succ x.isLt)]
  simp only [RingHom.id_apply]
  ring

theorem pairSpinorPolynomial_cube {R : Type*} [CommRing R] [IsDomain R]
    (f : ℂ →+* R) (ui vi uj vj : R) (huj : uj ≠ 0) (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    (ui*vj-uj*vi)^3 ∣ pairSpinorPolynomial f ui vi uj vj Q ψ := by
  have hd := homogeneousEval_dvd (RingHom.id R) ui vi
    (pairPartialPolynomial_cube f uj vj Q ψ hc)
    (pairPartialPolynomial_degree f uj vj Q ψ)
  have hdeg : ((C vj-X*C uj)^3).natDegree = 3 := by
    rw [natDegree_pow, linear_natDegree vj uj huj]
  rw [hdeg, homogeneousEval_cube _ _ _ _ (by rw [linear_natDegree vj uj huj]),
    homogeneousEval_linear] at hd
  rw [pairSpinorPolynomial_homogeneousEval]
  simpa only [RingHom.id_apply, mul_comm vj ui, mul_comm vi uj] using hd

theorem pairSpinorPolynomial_bracket_cube {N Q : ℕ} (i j : Fin N)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    bracket i j^3 ∣ pairSpinorPolynomial MvPolynomial.C
      (MvPolynomial.X (i,false)) (MvPolynomial.X (i,true))
      (MvPolynomial.X (j,false)) (MvPolynomial.X (j,true)) Q ψ := by
  exact pairSpinorPolynomial_cube _ _ _ _ _ (MvPolynomial.X_ne_zero _) Q ψ hc

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem energy_eq_zero_iff {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ p : ℕ, p < 2*Q-1 →
      ∀ a : Configuration N Q, a i = 0 → a j = 0 → pairAmplitude ψ i j p a = 0 := by
  unfold energy
  simp (disch := intros; positivity) [Finset.sum_eq_zero_iff_of_nonneg]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_AffineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Polynomial
open scoped BigOperators

theorem pairMoment_eq_jet (Q n : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) :
    pairMoment Q n ψ = -2 * ((pairAffinePolynomial Q ψ).derivative.eval
      (X : Polynomial ℂ)).coeff n := by
  rw [pairAffinePolynomial_jet_coeff]
  let I : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (x.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  let J : ℂ := ∑ x, ∑ y, if x.val+y.val = n+1 then
    (y.val : ℂ)*weightedPairCoordinate Q ψ x y else 0
  have hs : I = -J := by
    dsimp [I,J]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [weightedPairCoordinate_swap Q ψ ha x y, Nat.add_comm y.val x.val]
    split_ifs <;> ring
  have hmom : pairMoment Q n ψ = I-J := by
    dsimp [pairMoment,I,J]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs <;> ring
  change pairMoment Q n ψ = -2*J
  rw [hmom,hs]
  ring

theorem pair_kernel_of_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y)
    (hcube : PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ) :
    ∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0 := by
  obtain ⟨g,hg⟩ := hcube
  have hj : (pairAffinePolynomial Q ψ).derivative.eval (X : Polynomial ℂ) = 0 := by
    rw [hg, derivative_mul]
    simp [PairDiagonal.diagonal, derivative_pow]
  intro p hp
  have hp' : p ≤ 2*Q-2 := by have h := Finset.mem_range.mp hp; omega
  have hm : pairMoment Q p ψ = 0 := by
    rw [pairMoment_eq_jet Q p ψ ha, hj, coeff_zero]
    ring
  rw [pairMoment_eq_amplitude Q p (by omega) hp' ψ] at hm
  have hn : (pairNormalization Q p : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (pairNormalization_pos Q p (by omega) hp'))
  exact (mul_eq_zero.mp hm).resolve_left hn

theorem pair_kernel_iff_affine_cube (Q : ℕ) (hQ : 2 ≤ Q)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (ha : ∀ x y, ψ y x = -ψ x y) :
    (∀ p ∈ Finset.range (2*Q-1),
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) = 0) ↔
        PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q ψ :=
  ⟨pair_kernel_affine_cube Q hQ ψ ha, pair_kernel_of_affine_cube Q hQ ψ ha⟩

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalPairKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairSlice_antisymmetric {N Q : ℕ} (ψ : State N Q) (hψ : Antisymmetric ψ)
    (i j : Fin N) (hij : i ≠ j) (a : Configuration N Q) :
    ∀ x y, pairSlice ψ i j a y x = -pairSlice ψ i j a x y := by
  intro x y
  have h := hψ i j hij (Function.update (Function.update a i x) j y)
  have hs : (Function.update (Function.update a i x) j y) ∘ Equiv.swap i j =
      Function.update (Function.update a i y) j x := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hij]
    · by_cases hkj : k = j
      · subst k; simp [hij]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj,hki,hkj]
  simpa only [hs,pairSlice] using h

theorem pairSlice_anchor {N Q : ℕ} (ψ : State N Q) (i j : Fin N)
    (a : Configuration N Q) :
    pairSlice ψ i j (Function.update (Function.update a i 0) j 0) = pairSlice ψ i j a := by
  funext x y
  unfold pairSlice
  congr 1
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all

theorem energy_eq_zero_iff_pair_slices {N Q : ℕ} (ψ : State N Q) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ a : Configuration N Q,
      ∀ p ∈ Finset.range (2*Q-1),
        (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*pairSlice ψ i j a x y) = 0 := by
  rw [energy_eq_zero_iff]
  constructor
  · intro h i j hij a p hp
    have h0 := h i j hij p (Finset.mem_range.mp hp)
      (Function.update (Function.update a i 0) j 0)
      (by simp [ne_of_lt hij]) (by simp)
    change (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*
      pairSlice ψ i j (Function.update (Function.update a i 0) j 0) x y) = 0 at h0
    simpa only [pairSlice_anchor] using h0
  · intro h i j hij p hp a hai haj
    exact h i j hij a p (Finset.mem_range.mpr hp)

theorem energy_eq_zero_iff_affine_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∀ (i j : Fin N), i < j → ∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a) := by
  rw [energy_eq_zero_iff_pair_slices]
  constructor
  · intro h i j hij a
    exact (pair_kernel_iff_affine_cube Q hQ _
      (pairSlice_antisymmetric ψ hψ i j (ne_of_lt hij) a)).mp (h i j hij a)
  · intro h i j hij a
    exact (pair_kernel_iff_affine_cube Q hQ _
      (pairSlice_antisymmetric ψ hψ i j (ne_of_lt hij) a)).mpr (h i j hij a)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_BracketIrreducible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial

theorem bracket_irreducible {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Irreducible (bracket i j) := by
  let f : MvPolynomial (SpinorVariables N) ℂ := X (j,true)
  let g : MvPolynomial (SpinorVariables N) ℂ := -(X (j,false)*X (i,true))
  have hf : f ≠ 0 := X_ne_zero _
  have hif : (i,false) ∉ f.vars := by simp [f]
  have hig : (i,false) ∉ g.vars := by
    simp only [g, vars_neg]
    intro h
    have hu := vars_mul (X (j,false) : MvPolynomial (SpinorVariables N) ℂ) (X (i,true)) h
    simp [hij] at hu
  have hnd : ¬ f ∣ g := by
    intro hd
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ :=
      eval₂Hom (RingHom.id ℂ) (fun z => if z = (j,true) then 0 else 1)
    have h := map_dvd ev hd
    norm_num [ev,f,g,eval₂Hom,hij,Ne.symm hij] at h
  have hr : IsRelPrime f g :=
    (X_prime (R := ℂ) (i := (j,true))).irreducible.isRelPrime_iff_not_dvd.mpr hnd
  have h := irreducible_mul_X_add f g (i,false) hf hif hig hr
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold bracket f g
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_BracketCoprime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial

theorem pair_outside_endpoint {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : (k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j) := by
  by_cases hk : k = i ∨ k = j
  · right
    rcases hk with rfl | rfl
    · constructor
      · exact ne_of_gt hkl
      · intro h
        subst l
        exact hne rfl
    · constructor
      · intro h
        subst l
        exact (lt_asymm hij hkl)
      · exact ne_of_gt hkl
  · exact Or.inl (not_or.mp hk)

theorem bracket_not_dvd_distinct {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : ¬ bracket i j ∣ bracket k l := by
  intro hd
  rcases pair_outside_endpoint i j k l hij hkl hne with hk | hl
  · let point : SpinorVariables N → ℂ := fun z =>
      if z.2 then (if z.1 = k then 1 else 0) else (if z.1 = k then 0 else 1)
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) point
    have h := map_dvd ev hd
    norm_num [ev,point,bracket,eval₂Hom,hk.1,hk.2,Ne.symm hk.1,Ne.symm hk.2,ne_of_gt hkl] at h
  · let point : SpinorVariables N → ℂ := fun z =>
      if z.2 then (if z.1 = l then 1 else 0) else (if z.1 = l then 0 else 1)
    let ev : MvPolynomial (SpinorVariables N) ℂ →+* ℂ := eval₂Hom (RingHom.id ℂ) point
    have h := map_dvd ev hd
    norm_num [ev,point,bracket,eval₂Hom,hl.1,hl.2,Ne.symm hl.1,Ne.symm hl.2,ne_of_lt hkl] at h

theorem bracket_isRelPrime {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : IsRelPrime (bracket i j) (bracket k l) :=
  (bracket_irreducible i j (ne_of_lt hij)).isRelPrime_iff_not_dvd.mpr
    (bracket_not_dvd_distinct i j k l hij hkl hne)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_BracketProductDivisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem laughlinPolynomial_eq_orderedProduct (N : ℕ) :
    laughlinPolynomial N = ∏ ij ∈ orderedPairs N, bracket ij.1 ij.2 ^ 3 := by
  unfold laughlinPolynomial orderedPairs
  rw [Finset.prod_filter, Fintype.prod_prod_type]

theorem laughlinPolynomial_dvd_of_pair_cubes {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (h : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    laughlinPolynomial N ∣ P := by
  rw [laughlinPolynomial_eq_orderedProduct]
  apply Finset.prod_dvd_of_isRelPrime
  · rintro ⟨i,j⟩ hij ⟨k,l⟩ hkl hne
    exact (bracket_isRelPrime i j k l (Finset.mem_filter.mp hij).2
      (Finset.mem_filter.mp hkl).2 hne).pow
  · rintro ⟨i,j⟩ hij
    exact h i j (Finset.mem_filter.mp hij).2

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_LaughlinDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem bracket_isHomogeneous {N : ℕ} (i j : Fin N) :
    (bracket i j).IsHomogeneous 2 :=
  ((isHomogeneous_X ℂ (i,false)).mul (isHomogeneous_X ℂ (j,true))).sub
    ((isHomogeneous_X ℂ (j,false)).mul (isHomogeneous_X ℂ (i,true)))

theorem orderedPairs_card (N : ℕ) : (orderedPairs N).card = N.choose 2 := by
  simpa [orderedPairs] using (Fintype.card_product_filter_lt (α := Fin N))

theorem laughlinPolynomial_isHomogeneous (N : ℕ) :
    (laughlinPolynomial N).IsHomogeneous (6 * N.choose 2) := by
  rw [laughlinPolynomial_eq_orderedProduct]
  have h := IsHomogeneous.prod (orderedPairs N)
    (fun ij => bracket ij.1 ij.2 ^ 3) (fun _ => 6)
    (fun ij _ => (bracket_isHomogeneous ij.1 ij.2).pow 3)
  simpa [orderedPairs_card, Nat.mul_comm] using h

theorem laughlinPolynomial_totalDegree (N : ℕ) :
    (laughlinPolynomial N).totalDegree = 6 * N.choose 2 :=
  (laughlinPolynomial_isHomogeneous N).totalDegree (laughlinPolynomial_ne_zero N)

theorem laughlin_degree_at_flux (N : ℕ) : 6 * N.choose 2 = N * (3 * (N-1)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right, Nat.reduceAdd] at h
    simp only [Nat.add_sub_cancel]
    nlinarith

theorem scalar_laughlin_of_degree_and_pair_cubes {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (hdegree : P.totalDegree ≤ 6 * N.choose 2)
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    ∃ c : ℂ, P = C c * laughlinPolynomial N := by
  obtain ⟨g,hg⟩ := laughlinPolynomial_dvd_of_pair_cubes P hcubes
  by_cases hzero : g = 0
  · exact ⟨0, by simp [hg,hzero]⟩
  · have hdeg : g.totalDegree = 0 := by
      rw [hg, totalDegree_mul_of_isDomain (laughlinPolynomial_ne_zero N) hzero,
        laughlinPolynomial_totalDegree] at hdegree
      omega
    exact ⟨g.coeff 0, by rw [hg, mul_comm]; exact congrArg (fun z => z * laughlinPolynomial N) (totalDegree_eq_zero_iff_eq_C.mp hdeg)⟩

theorem scalar_laughlin_at_flux {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (hdegree : P.totalDegree ≤ N * (3 * (N-1)))
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    ∃ c : ℂ, P = C c * laughlinPolynomial N :=
  scalar_laughlin_of_degree_and_pair_cubes P
    (by simpa [laughlin_degree_at_flux] using hdegree) hcubes

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Polynomial2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem monomialExponent_injective (N Q : ℕ) :
    Function.Injective (monomialExponent (N := N) (Q := Q)) := by
  intro a b hab
  funext i
  apply Fin.ext
  have h := congrArg (fun d => d (i,true)) hab
  simpa [monomialExponent] using h

theorem spinWeight_ne_zero {N Q : ℕ} (a : Configuration N Q) : spinWeight a ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a i).isLt)

theorem spinPolynomial_coeff {N Q : ℕ} (ψ : State N Q) (a : Configuration N Q) :
    (spinPolynomial ψ).coeff (monomialExponent a) = spinWeight a * ψ a := by
  classical
  simp only [spinPolynomial, coeff_sum, coeff_monomial]
  have he (b : Configuration N Q) : monomialExponent b = monomialExponent a ↔ b = a :=
    (monomialExponent_injective N Q).eq_iff
  simp_rw [he]
  simp

theorem state_eq_laughlin_of_polynomial {N Q : ℕ} (ψ : State N Q) (c : ℂ)
    (h : spinPolynomial ψ = C c * laughlinPolynomial N) :
    ψ = fun a => c * laughlinVector N Q a := by
  funext a
  have hc := congrArg (fun p => p.coeff (monomialExponent a)) h
  rw [spinPolynomial_coeff, coeff_C_mul] at hc
  change ψ a = c * ((laughlinPolynomial N).coeff (monomialExponent a) / spinWeight a)
  apply (mul_left_cancel₀ (spinWeight_ne_zero a))
  rw [hc]
  field_simp [spinWeight_ne_zero a]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Spectators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem sum_pair_configurations {N Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i j : Fin N) (hij : i ≠ j) (F : Configuration N Q → R) :
    (∑ a, F a) = ∑ a : PairSpectators (Q := Q) i j, ∑ x, ∑ y,
      F (Function.update (Function.update a.val i x) j y) := by
  classical
  rw [← Equiv.sum_comp (pairConfigurationEquiv (Q := Q) i j hij)]
  simp only [Fintype.sum_prod_type, pairConfigurationEquiv, Equiv.coe_fn_mk]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_OrbitalExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem spinPolynomial_expansion {N Q : ℕ} (ψ : State N Q) :
    spinPolynomial ψ = ∑ a, C (ψ a) * ∏ k, spinOrbitalPolynomial Q k (a k) := by
  classical
  unfold spinPolynomial
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  have he (k : Fin N) : (∏ b : Bool, X (k,b)^monomialExponent a (k,b)) =
      (X (k,false)^(Q-(a k).val)*X (k,true)^(a k).val : MvPolynomial _ ℂ) := by
    simp [monomialExponent, mul_comm]
  simp_rw [he]
  simp only [spinOrbitalPolynomial, Finset.prod_mul_distrib, ← map_prod, map_mul]
  have hw : spinWeight a = ∏ k : Fin N,
      (Real.sqrt (Nat.choose Q (a k).val : ℝ) : ℂ) := by
    simp [spinWeight]
  rw [hw]
  ring

theorem prod_pair_split {N : ℕ} {R : Type*} [CommMonoid R]
    (i j : Fin N) (hij : i ≠ j) (f : Fin N → R) :
    (∏ k, f k) = (∏ k ∈ (Finset.univ.erase i).erase j, f k) * f i * f j := by
  classical
  have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm hij]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ hj]
  ac_rfl

theorem spinOrbital_update_product {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : Configuration N Q) (x y : Fin (Q+1)) :
    (∏ k, spinOrbitalPolynomial Q k ((Function.update (Function.update a i x) j y) k)) =
      spectatorPolynomial i j a * spinOrbitalPolynomial Q i x * spinOrbitalPolynomial Q j y := by
  rw [prod_pair_split i j hij]
  simp only [Function.update_self, Function.update_of_ne hij]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [Function.update_of_ne, hki,hkj]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_AffineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem pairAffineChart_bracket {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    pairAffineChart i j (bracket i j) = C PairDiagonal.diagonal := by
  unfold bracket
  rw [map_sub, map_mul, map_mul]
  simp [pairAffineChart, Ne.symm hij, PairDiagonal.diagonal]

theorem pairAffineChart_pair {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairAffineChart i j
      (pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q ψ) =
      C (pairAffinePolynomial Q ψ) := by
  unfold pairSpinorPolynomial pairAffinePolynomial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp [pairAffineChart, eval₂Hom, Ne.symm hij,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]

theorem affineExponent_injective (N Q : ℕ) :
    Function.Injective (affineExponent (N := N) (Q := Q)) := by
  intro a b h
  funext k
  apply Fin.ext
  exact congrArg (fun d => d k) h

theorem spectatorWeight_ne_zero {N Q : ℕ} (i j : Fin N) (a : Configuration N Q) :
    spectatorWeight i j a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a k).isLt)

theorem pairAffineChart_spectator {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : PairSpectators (Q := Q) i j) :
    pairAffineChart i j (spectatorPolynomial i j a.val) =
      monomial (affineExponent a.val) (Polynomial.C (Polynomial.C (spectatorWeight i j a.val))) := by
  classical
  unfold spectatorPolynomial
  simp only [map_prod]
  have he (k : Fin N) (hk : k ∈ (Finset.univ.erase i).erase j) :
      pairAffineChart i j (spinOrbitalPolynomial Q k (a.val k)) =
        C (Polynomial.C (Polynomial.C (Real.sqrt (Nat.choose Q (a.val k).val : ℝ) : ℂ))) *
          X k^(a.val k).val := by
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    simp [pairAffineChart, spinOrbitalPolynomial, eval₂Hom, hki, hkj]
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, monomial_eq]
  simp only [← map_prod, ← RingHom.comp_apply, spectatorWeight]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [affineExponent, Finsupp.onFinset_apply]
  rw [prod_pair_split i j hij]
  simp [a.property.1, a.property.2]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_PolynomialDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem monomialExponent_degree {N Q : ℕ} (a : Configuration N Q) :
    (monomialExponent a).degree = N * Q := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  have h (i : Fin N) : ∑ b : Bool, monomialExponent a (i,b) = Q := by
    simpa [monomialExponent, Nat.add_comm] using Nat.sub_add_cancel (Nat.le_of_lt_succ (a i).isLt)
  simp_rw [h]
  simp

theorem spinPolynomial_isHomogeneous {N Q : ℕ} (ψ : State N Q) :
    (spinPolynomial ψ).IsHomogeneous (N * Q) := by
  apply IsHomogeneous.sum
  intro a ha
  exact isHomogeneous_monomial _ (monomialExponent_degree a)

theorem spinPolynomial_totalDegree_le {N Q : ℕ} (ψ : State N Q) :
    (spinPolynomial ψ).totalDegree ≤ N * Q :=
  (spinPolynomial_isHomogeneous ψ).totalDegree_le

theorem state_eq_laughlin_of_pair_cubes {N : ℕ} (ψ : State N (3*(N-1)))
    (hcubes : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ spinPolynomial ψ) :
    ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  obtain ⟨c,hc⟩ := scalar_laughlin_at_flux (spinPolynomial ψ)
    (spinPolynomial_totalDegree_le ψ) hcubes
  exact ⟨c,state_eq_laughlin_of_polynomial ψ c hc⟩

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_PairDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem pairSpinorPolynomial_orbitals {N Q : ℕ} (i j : Fin N)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q ψ =
      ∑ x, ∑ y, C (ψ x y) * spinOrbitalPolynomial Q i x * spinOrbitalPolynomial Q j y := by
  unfold pairSpinorPolynomial
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [weightedPairCoordinate, Complex.ofReal_mul, map_mul, spinOrbitalPolynomial]
  ring

theorem spinPolynomial_pair_decomposition {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    spinPolynomial ψ = ∑ a : PairSpectators (Q := Q) i j,
      spectatorPolynomial i j a.val *
      pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q
        (pairSlice ψ i j a.val) := by
  rw [spinPolynomial_expansion, sum_pair_configurations i j hij]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pairSpinorPolynomial_orbitals]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [spinOrbital_update_product i j hij]
  unfold pairSlice
  ring

theorem bracket_cube_dvd_spinPolynomial_of_slices {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j)
    (hc : ∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a)) :
    bracket i j^3 ∣ spinPolynomial ψ := by
  rw [spinPolynomial_pair_decomposition ψ i j hij]
  apply Finset.dvd_sum
  intro a ha
  exact dvd_mul_of_dvd_right (pairSpinorPolynomial_bracket_cube i j _ (hc a.val)) _

theorem energy_zero_global_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∀ i j : Fin N, i < j → bracket i j^3 ∣ spinPolynomial ψ := by
  intro i j hij
  exact bracket_cube_dvd_spinPolynomial_of_slices ψ i j (ne_of_lt hij)
    ((energy_eq_zero_iff_affine_pair_cubes hQ ψ hψ).mp hE i j hij)

theorem zero_energy_state_eq_laughlin {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3*(N-1))) (hψ : Antisymmetric ψ) (hE : energy ψ = 0) :
    ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  exact state_eq_laughlin_of_pair_cubes ψ
    (energy_zero_global_pair_cubes (by omega) ψ hψ hE)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_GlobalPairCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem pairAffineChart_coefficient {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) (a : PairSpectators (Q := Q) i j) :
    (pairAffineChart i j (spinPolynomial ψ)).coeff (affineExponent a.val) =
      Polynomial.C (Polynomial.C (spectatorWeight i j a.val)) *
        pairAffinePolynomial Q (pairSlice ψ i j a.val) := by
  classical
  rw [spinPolynomial_pair_decomposition ψ i j hij]
  simp only [map_sum, map_mul]
  simp_rw [pairAffineChart_spectator i j hij, pairAffineChart_pair i j hij]
  simp only [coeff_sum]
  simp_rw [mul_comm (monomial _ _) (C _), coeff_C_mul, coeff_monomial, mul_ite, mul_zero]
  have he (b : PairSpectators (Q := Q) i j) :
      affineExponent b.val = affineExponent a.val ↔ b = a := by
    rw [(affineExponent_injective N Q).eq_iff]
    exact Subtype.val_injective.eq_iff
  simp_rw [he]
  simp [mul_comm]

theorem affine_pair_cubes_of_bracket_dvd {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) (hc : bracket i j^3 ∣ spinPolynomial ψ)
    (a : Configuration N Q) :
    PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a) := by
  let a0 : PairSpectators (Q := Q) i j :=
    ⟨Function.update (Function.update a i 0) j 0, by simp [hij]⟩
  have hd := map_dvd (pairAffineChart i j) hc
  rw [map_pow, pairAffineChart_bracket i j hij, ← map_pow] at hd
  obtain ⟨g,hg⟩ := hd
  have he : Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
      pairAffinePolynomial Q (pairSlice ψ i j a0.val) =
        PairDiagonal.diagonal^3 * g.coeff (affineExponent a0.val) := by
    rw [← pairAffineChart_coefficient ψ i j hij a0, hg, coeff_C_mul]
  have hunit : Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
      Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)⁻¹) = (1 : PairDiagonal.Poly) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (spectatorWeight_ne_zero i j a0.val),
      map_one, map_one]
  have hdiv : PairDiagonal.diagonal^3 ∣
      (Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)) *
        pairAffinePolynomial Q (pairSlice ψ i j a0.val)) *
          Polynomial.C (Polynomial.C (spectatorWeight i j a0.val)⁻¹) :=
    dvd_mul_of_dvd_left ⟨g.coeff (affineExponent a0.val), he⟩ _
  rw [mul_right_comm, hunit, one_mul] at hdiv
  simpa only [a0, pairSlice_anchor] using hdiv

theorem affine_pair_cubes_iff_bracket_dvd {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) :
    (∀ a : Configuration N Q,
      PairDiagonal.diagonal^3 ∣ pairAffinePolynomial Q (pairSlice ψ i j a)) ↔
        bracket i j^3 ∣ spinPolynomial ψ :=
  ⟨bracket_cube_dvd_spinPolynomial_of_slices ψ i j hij,
    fun h => affine_pair_cubes_of_bracket_dvd ψ i j hij h⟩

theorem energy_eq_zero_iff_global_pair_cubes {N Q : ℕ} (hQ : 2 ≤ Q)
    (ψ : State N Q) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∀ i j : Fin N, i < j → bracket i j^3 ∣ spinPolynomial ψ := by
  rw [energy_eq_zero_iff_affine_pair_cubes hQ ψ hψ]
  constructor
  · intro h i j hij
    exact (affine_pair_cubes_iff_bracket_dvd ψ i j (ne_of_lt hij)).mp (h i j hij)
  · intro h i j hij
    exact (affine_pair_cubes_iff_bracket_dvd ψ i j (ne_of_lt hij)).mpr (h i j hij)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Multidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem particleDegreeWeight_apply {N : ℕ} (k : Fin N) (d : SpinorVariables N →₀ ℕ) :
    Finsupp.weight (particleDegreeWeight k) d=d (k,false)+d (k,true) := by
  rw [Finsupp.weight_eq_sum,Fintype.sum_prod_type]
  simp [particleDegreeWeight,Nat.add_comm]

theorem exponent_eq_configuration {N Q : ℕ} (d : SpinorVariables N →₀ ℕ)
    (hd : ∀ k : Fin N, d (k,false)+d (k,true)=Q) :
    ∃ a : Configuration N Q, monomialExponent a=d := by
  let a : Configuration N Q := fun k => ⟨d (k,true),by have h := hd k; omega⟩
  refine ⟨a,?_⟩
  ext ⟨k,b⟩
  cases b <;> simp only [monomialExponent,Finsupp.onFinset_apply,Bool.false_eq_true,↓reduceIte,a]
  have h := hd k
  omega

theorem spinPolynomial_reconstruct {N Q : ℕ} (P : MvPolynomial (SpinorVariables N) ℂ)
    (hP : ∀ k : Fin N, P.IsWeightedHomogeneous (particleDegreeWeight k) Q) :
    spinPolynomial (fun a : Configuration N Q => P.coeff (monomialExponent a)/spinWeight a)=P := by
  ext d
  by_cases hd : P.coeff d=0
  · by_cases he : ∃ a : Configuration N Q, monomialExponent a=d
    · obtain ⟨a,rfl⟩ := he
      rw [spinPolynomial_coeff]
      simp [hd]
    · rw [hd]
      simp only [spinPolynomial,coeff_sum,coeff_monomial]
      apply Finset.sum_eq_zero
      intro a ha
      simp only [ite_eq_right (fun h => he ⟨a,h⟩)]
  · obtain ⟨a,rfl⟩ := exponent_eq_configuration d (fun k => by
      rw [← particleDegreeWeight_apply]; exact hP k hd)
    rw [spinPolynomial_coeff]
    field_simp [spinWeight_ne_zero a]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_LaughlinMultidegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem bracket_particle_degree {N : ℕ} (k i j : Fin N) :
    (bracket i j).IsWeightedHomogeneous (particleDegreeWeight k)
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) := by
  have h (a : Fin N) (b : Bool) := isWeightedHomogeneous_X (R := ℂ) (particleDegreeWeight k) (a,b)
  have h1 := (h i false).mul (h j true)
  have h2 := (h j false).mul (h i true)
  exact h1.sub (by simpa only [particleDegreeWeight,Nat.add_comm] using h2)

theorem particle_pair_degree_count {N : ℕ} (k : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N, if i<j then
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0)=N-1 := by
  have hsplit : (∑ i : Fin N, ∑ j : Fin N, if i<j then
      ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
      (∑ j : Fin N, if k<j then 1 else 0)+(∑ i : Fin N, if i<k then 1 else 0) := by
    have he (i j : Fin N) : (if i<j then
        ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
        (if i=k then (if k<j then 1 else 0) else 0)+
        (if j=k then (if i<k then 1 else 0) else 0) := by
      split_ifs <;> omega
    simp_rw [he,Finset.sum_add_distrib]
    simp
  rw [hsplit,← Finset.sum_add_distrib]
  have hentry (j : Fin N) : (if k<j then 1 else 0)+(if j<k then 1 else 0) =
      (if j=k then 0 else 1 : ℕ) := by
    split_ifs <;> omega
  simp_rw [hentry]
  simp [Finset.sum_ite,Finset.filter_ne']

theorem laughlinPolynomial_particle_degree (N : ℕ) (k : Fin N) :
    (laughlinPolynomial N).IsWeightedHomogeneous (particleDegreeWeight k) (3*(N-1)) := by
  have hp := IsWeightedHomogeneous.prod (Finset.univ : Finset (Fin N))
    (fun i => ∏ j : Fin N, if i<j then bracket i j^3 else 1)
    (fun i => ∑ j : Fin N, if i<j then
      3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) (w := particleDegreeWeight k) (by
      intro i hi
      apply IsWeightedHomogeneous.prod
      intro j hj
      by_cases hij : i<j
      · simpa only [ite_eq_left hij,nsmul_eq_mul,Nat.cast_id] using (bracket_particle_degree k i j).pow 3
      · simp only [ite_eq_right hij]
        exact isWeightedHomogeneous_one ℂ _)
  have hs : (∑ i : Fin N, ∑ j : Fin N, if i<j then
      3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0)=3*(N-1) := by
    have he (i j : Fin N) : (if i<j then
        3*((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) =
        3*(if i<j then ((if i=k then 1 else 0)+(if j=k then 1 else 0) : ℕ) else 0) := by
      by_cases h : i<j <;> simp [h]
    simp_rw [he,← Finset.mul_sum]
    rw [particle_pair_degree_count]
  rw [hs] at hp
  exact hp

theorem spinPolynomial_laughlinVector (N : ℕ) :
    spinPolynomial (laughlinVector N (3*(N-1)))=laughlinPolynomial N := by
  exact spinPolynomial_reconstruct _ (laughlinPolynomial_particle_degree N)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_PhysicalLaughlinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

theorem spinPolynomial_scalar {N Q : ℕ} (c : ℂ) (ψ : State N Q) :
    spinPolynomial (fun a => c * ψ a) = C c * spinPolynomial ψ := by
  unfold spinPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [C_mul_monomial]
  congr 1
  ring

theorem physical_Laughlin_kernel {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3*(N-1))) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∃ c : ℂ, ψ = fun a => c * laughlinVector N (3*(N-1)) a := by
  constructor
  · exact zero_energy_state_eq_laughlin hN ψ hψ
  · rintro ⟨c,hc⟩
    apply (energy_eq_zero_iff_global_pair_cubes (by omega) ψ hψ).mpr
    intro i j hij
    rw [hc, spinPolynomial_scalar, spinPolynomial_laughlinVector]
    exact dvd_mul_of_dvd_right (bracket_cube_dvd_laughlin hij) _

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_Antisymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem antisymmetric_perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (σ : Equiv.Perm (Fin N)) (a : Configuration N Q) :
    ψ (a ∘ σ) = σ.sign • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' generalizing a with
  | one => simp
  | mul_swap σ i j hij ih =>
    change ψ ((a ∘ σ) ∘ Equiv.swap i j) = _
    rw [hψ i j hij, ih]
    simp [map_mul, Equiv.Perm.sign_swap hij]

theorem antisymmetric_insertNth {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (k : Fin (n+1)) (i : Fin (Q+1)) (a : Configuration n Q) :
    ψ (k.insertNth i a) = (-1 : ℂ)^k.val * ψ (Fin.cons i a) := by
  rw [← Fin.cons_comp_cycleRange, antisymmetric_perm hψ]
  simp [Units.smul_def]

theorem antisymmetric_cons {n Q : ℕ} {ψ : State (n+1) Q}
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    Antisymmetric (fun a : Configuration n Q => ψ (Fin.cons i a)) := by
  intro j k hjk a
  change ψ (Fin.cons i (a ∘ Equiv.swap j k)) = _
  rw [show Fin.cons i (a ∘ Equiv.swap j k) =
    Fin.cons i a ∘ Equiv.swap j.succ k.succ from Matrix.cons_swap i a j k]
  exact hψ j.succ k.succ (by simpa using hjk) (Fin.cons i a)

theorem sum_config_insert {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (k : Fin (n+1)) (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (k.insertNth i b) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n+1) => Fin (Q+1)) k).sum_comp]
  exact Fintype.sum_prod_type _

theorem sum_config_cons {n Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : Configuration (n+1) Q → M) :
    ∑ a, f a = ∑ i : Fin (Q+1), ∑ b : Configuration n Q, f (Fin.cons i b) := by
  simpa using sum_config_insert (0 : Fin (n+1)) f

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_ExteriorContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem orderedWedge_cons {n Q : ℕ} (i : Fin (Q+1)) (a : Configuration n Q) :
    orderedWedge (Fin.cons i a) = create i (orderedWedge a) := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

theorem orderedWedge_head {n Q : ℕ} (a : Configuration (n+1) Q) :
    orderedWedge a = create (a 0) (orderedWedge (fun j => a j.succ)) := by
  rw [← orderedWedge_cons]
  congr 1
  exact (Fin.cons_self_tail a).symm

theorem annihilate_orderedWedge (n Q : ℕ) (i : Fin (Q+1))
    (a : Configuration (n+1) Q) :
    annihilate i (orderedWedge a) =
      ∑ k : Fin (n+1), ((-1 : ℂ)^k.val * delta i (a k)) •
        orderedWedge (k.removeNth a) := by
  induction n with
  | zero =>
    rw [orderedWedge_head, annihilate_create_apply]
    simp [orderedWedge, ExteriorAlgebra.ιMulti_zero_apply, annihilate_vacuum]
  | succ n ih =>
    rw [orderedWedge_head, annihilate_create_apply, ih, map_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ,
      map_smul]
    have h0 : (0 : Fin (n+2)).removeNth a = fun j => a j.succ := by rfl
    rw [h0]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hw : orderedWedge (k.succ.removeNth a) =
        create (a 0) (orderedWedge (k.removeNth (fun j => a j.succ))) := by
      rw [← orderedWedge_cons]
      congr 1
      have h := Fin.cons_comp_succ_succAbove (a 0) (fun j => a j.succ) k
      have ha : Fin.cons (a 0) (fun j => a j.succ) = a := Fin.cons_self_tail a
      rw [ha] at h
      exact h
    rw [hw]
    simp only [mul_neg_one, neg_mul, neg_smul]

theorem tensorExterior_cons (n Q : ℕ) (ψ : State (n+1) Q) :
    tensorExterior (n+1) Q ψ =
      ∑ i : Fin (Q+1), create i (tensorExterior n Q (fun a => ψ (Fin.cons i a))) := by
  change (∑ a, ψ a • orderedWedge a) = _
  rw [sum_config_cons]
  change (∑ i, ∑ b, ψ (Fin.cons i b) • orderedWedge (Fin.cons i b)) = _
  simp only [orderedWedge_cons,tensorExterior,map_sum,map_smul]
  rfl

theorem annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+1) Q)
    (hψ : Antisymmetric ψ) (i : Fin (Q+1)) :
    annihilate i (tensorExterior (n+1) Q ψ) =
      (n+1 : ℂ) • tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
  change annihilate i (∑ a, ψ a • orderedWedge a) = _
  simp only [map_sum,map_smul,annihilate_orderedWedge,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  have hs (k : Fin (n+1)) :
      (∑ a : Configuration (n+1) Q,
        (ψ a * ((-1 : ℂ)^k.val * delta i (a k))) • orderedWedge (k.removeNth a)) =
        tensorExterior n Q (fun a => ψ (Fin.cons i a)) := by
    rw [sum_config_insert k]
    simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      antisymmetric_insertNth hψ]
    have he (x : Fin (Q+1)) (b : Configuration n Q) :
        ((-1 : ℂ)^k.val * ψ (Fin.cons x b) * ((-1 : ℂ)^k.val * delta i x)) =
          delta i x * ψ (Fin.cons x b) := by
      have hpow : ((-1 : ℂ)^k.val)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      calc
        _ = ((-1 : ℂ)^k.val)^2 * (delta i x * ψ (Fin.cons x b)) := by ring
        _ = _ := by rw [hpow,one_mul]
    simp only [he]
    simp [delta,tensorExterior,orderedWedge]
  simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_ExteriorIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem tensorExterior_inner (n Q : ℕ) (ψ φ : State n Q) (hφ : Antisymmetric φ) :
    occupationInner Q (tensorExterior n Q ψ) (tensorExterior n Q φ) =
      (n.factorial : ℂ) * ∑ a, star (ψ a) * φ a := by
  induction n with
  | zero =>
    simp only [tensorExterior, ExteriorAlgebra.ιMulti_zero_apply]
    simp only [occupationInner_sum_left,occupationInner_sum_right]
    simp only [occupationInner_smul_left,occupationInner_smul_right]
    have h1 : occupationInner Q 1 1 = 1 := by
      rw [← occupation_empty]
      simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]
    simp [h1,mul_comm]
  | succ n ih =>
    rw [tensorExterior_cons,occupationInner_sum_left]
    simp only [create_annihilate_adjoint,annihilate_tensorExterior n Q φ hφ,
      occupationInner_smul_right]
    simp_rw [ih _ _ (antisymmetric_cons hφ _)]
    rw [sum_config_cons]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Finset.mul_sum]
    ring_nf

theorem tensorExterior_norm (n Q : ℕ) (ψ : State n Q) (hψ : Antisymmetric ψ) :
    occupationNormSq Q (tensorExterior n Q ψ) =
      (n.factorial : ℝ) * ∑ a, ‖ψ a‖^2 := by
  have h := tensorExterior_inner n Q ψ ψ hψ
  rw [occupationInner_self] at h
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  simp only [he,← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

theorem normalizedTensorExterior_inner (n Q : ℕ) (ψ φ : State n Q)
    (hφ : Antisymmetric φ) :
    occupationInner Q (normalizedTensorExterior n Q ψ) (normalizedTensorExterior n Q φ) =
      ∑ a, star (ψ a)*φ a := by
  have hp : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he : ((Real.sqrt (n.factorial : ℝ) : ℂ))^2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (le_of_lt hp)
  simp only [normalizedTensorExterior,occupationInner_smul_left,occupationInner_smul_right,
    tensorExterior_inner n Q ψ φ hφ]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have hsc : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [← he]
  field_simp

theorem normalizedTensorExterior_norm (n Q : ℕ) (ψ : State n Q)
    (hψ : Antisymmetric ψ) :
    occupationNormSq Q (normalizedTensorExterior n Q ψ) = ∑ a, ‖ψ a‖^2 := by
  have h := normalizedTensorExterior_inner n Q ψ ψ hψ
  rw [occupationInner_self] at h
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  simp only [he,← Complex.ofReal_sum] at h
  exact Complex.ofReal_injective h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_PairContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem headPairAmplitude_antisymmetric {n Q : ℕ} (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (p : ℕ) : Antisymmetric (headPairAmplitude ψ p) := by
  intro i j hij b
  unfold headPairAmplitude
  simp_rw [(antisymmetric_cons (antisymmetric_cons hψ _) _) i j hij,
    mul_neg,Finset.sum_neg_distrib]

namespace Fock

theorem tensorExterior_sum {I : Type*} (n Q : ℕ) (s : Finset I) (ψ : I → State n Q) :
    tensorExterior n Q (fun a => ∑ i ∈ s, ψ i a) = ∑ i ∈ s, tensorExterior n Q (ψ i) := by
  simp only [tensorExterior,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem tensorExterior_smul (n Q : ℕ) (c : ℂ) (ψ : State n Q) :
    tensorExterior n Q (fun a => c * ψ a) = c • tensorExterior n Q ψ := by
  simp only [tensorExterior,Finset.smul_sum,smul_smul]

theorem two_annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (i j : Fin (Q+1)) :
    annihilate j (annihilate i (tensorExterior (n+2) Q ψ)) =
      ((n+2 : ℂ)*(n+1)) • tensorExterior n Q (fun a => ψ (Fin.cons i (Fin.cons j a))) := by
  rw [annihilate_tensorExterior (n+1) Q ψ hψ,map_smul,
    annihilate_tensorExterior n Q _ (antisymmetric_cons hψ i),smul_smul]
  congr 1
  push_cast
  ring

theorem sourcePairEnd_tensorExterior (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (p : ℕ) :
    sourcePairEnd Q p (tensorExterior (n+2) Q ψ) =
      (((n+2 : ℂ)*(n+1))/(Real.sqrt 2 : ℂ)) •
        tensorExterior n Q (headPairAmplitude ψ p) := by
  simp only [sourcePairEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,
    Module.End.mul_apply,two_annihilate_tensorExterior n Q ψ hψ,smul_smul]
  unfold headPairAmplitude
  simp only [tensorExterior_sum,tensorExterior_smul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  ring

end Fock

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalPairCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pair_update_insert {n Q : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (u v x y : Fin (Q+1)) (b : Configuration n Q) :
    Function.update (Function.update (i.insertNth u (j.insertNth v b) : Configuration (n+2) Q) i x)
      (i.succAbove j) y = i.insertNth x (j.insertNth y b) := by
  rw [Fin.update_insertNth, ← Fin.insertNth_update, Fin.update_insertNth]

theorem pairAmplitude_insert {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (p : ℕ)
    (u v : Fin (Q+1)) (b : Configuration n Q) :
    pairAmplitude ψ i (i.succAbove j) p (i.insertNth u (j.insertNth v b)) =
      ((-1 : ℂ)^i.val * (-1 : ℂ)^j.val) * headPairAmplitude ψ p b := by
  simp only [pairAmplitude,pair_update_insert,antisymmetric_insertNth hψ]
  have he (x y : Fin (Q+1)) :
      ψ (Fin.cons x (j.insertNth y b)) =
        (-1 : ℂ)^j.val * ψ (Fin.cons x (Fin.cons y b)) :=
    antisymmetric_insertNth (antisymmetric_cons hψ x) j y b
  simp only [he,headPairAmplitude,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem anchored_pair_sum {n Q : ℕ} (ψ : State (n+2) Q) (hψ : Antisymmetric ψ)
    (i : Fin (n+2)) (j : Fin (n+1)) (p : ℕ) :
    (∑ a : Configuration (n+2) Q,
      if a i = 0 ∧ a (i.succAbove j) = 0 then
        ‖pairAmplitude ψ i (i.succAbove j) p a‖^2 else 0) =
      ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
  rw [sum_config_insert i]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  simp_rw [sum_config_insert j]
  simp only [Fin.insertNth_apply_same,pairAmplitude_insert ψ hψ]
  simp [norm_pow,ite_and]

theorem unordered_position_count (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) =
      (n : ℝ)*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ,Fin.lt_def,Fin.val_zero,Fin.val_succ,
      Nat.zero_lt_succ,Nat.not_lt_zero,ite_true,ite_false,Nat.add_lt_add_iff_right]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      zero_add]
    change (n : ℝ) + (∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) = _
    rw [ih]
    push_cast
    ring

theorem energy_head_pair (n Q : ℕ) (ψ : State (n+2) Q) (hψ : Antisymmetric ψ) :
    energy ψ = ((n+2 : ℝ)*(n+1)/2) *
      ∑ p ∈ Finset.range (2*Q-1), ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
  have he (i j : Fin (n+2)) (hij : i < j) (p : ℕ) :
      (∑ a : Configuration (n+2) Q,
        if a i = 0 ∧ a j = 0 then ‖pairAmplitude ψ i j p a‖^2 else 0) =
        ∑ b : Configuration n Q, ‖headPairAmplitude ψ p b‖^2 := by
    obtain ⟨k,hk⟩ := (Fin.exists_succAbove_eq (ne_of_lt hij).symm)
    subst j
    exact anchored_pair_sum ψ hψ i k p
  unfold energy
  have hs : (∑ i : Fin (n+2), ∑ j : Fin (n+2), if i < j then (1 : ℝ) else 0) =
      (n+2 : ℝ)*(n+1)/2 := by
    rw [unordered_position_count]
    push_cast
    ring
  rw [← hs,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [ite_eq_left hij,one_mul]
    exact Finset.sum_congr rfl (fun p hp => he i j hij p)
  · simp [hij]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_FockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem tensorExterior_energy (n Q : ℕ) (ψ : State (n+2) Q) (hψ : Antisymmetric ψ) :
    sourceFockEnergy Q (tensorExterior (n+2) Q ψ) = ((n+2).factorial : ℝ)*energy ψ := by
  have hn : ‖((n+2 : ℂ)*(n+1))/(Real.sqrt 2 : ℂ)‖^2 =
      ((n+2 : ℝ)*(n+1))^2/2 := by
    rw [norm_div,norm_mul,div_pow,mul_pow]
    have h2 : ‖(Real.sqrt 2 : ℂ)‖^2 = (2 : ℝ) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by norm_num)]
    rw [h2]
    have hn2 : (n+2 : ℂ) = ((n+2 : ℝ) : ℂ) := by push_cast; rfl
    have hn1 : (n+1 : ℂ) = ((n+1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hn2,hn1,Complex.norm_of_nonneg (by positivity),Complex.norm_of_nonneg (by positivity)]
    ring
  simp only [sourceFockEnergy,sourcePairEnd_tensorExterior n Q ψ hψ,
    occupationNormSq_smul,hn,tensorExterior_norm n Q _ (headPairAmplitude_antisymmetric ψ hψ _)]
  rw [energy_head_pair n Q ψ hψ]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,← Finset.mul_sum]
  ring

theorem normalizedTensorExterior_energy (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) :
    sourceFockEnergy Q (normalizedTensorExterior (n+2) Q ψ) = energy ψ := by
  have hp : 0 < ((n+2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n+2)
  have hs : (Real.sqrt ((n+2).factorial : ℝ))^2 = ((n+2).factorial : ℝ) :=
    Real.sq_sqrt (le_of_lt hp)
  have he (c : ℂ) (x : Space Q) : sourceFockEnergy Q (c • x) = ‖c‖^2*sourceFockEnergy Q x := by
    simp only [sourceFockEnergy,map_smul,occupationNormSq_smul,Finset.mul_sum]
  rw [normalizedTensorExterior,he,tensorExterior_energy n Q ψ hψ]
  have hn : ‖((Real.sqrt ((n+2).factorial : ℝ))⁻¹ : ℂ)‖^2 =
      (((n+2).factorial : ℝ))⁻¹ := by
    rw [norm_inv,inv_pow]
    congr 1
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hs
  rw [hn]
  field_simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_ExteriorAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem orderedWedge_swap {n Q : ℕ} (a : Configuration n Q) (i j : Fin n) (hij : i≠j) :
    orderedWedge (a ∘ Equiv.swap i j) = -orderedWedge a := by
  exact (ExteriorAlgebra.ιMulti ℂ n).map_swap (fun k => mode (a k)) hij

theorem normalizedTensorReadout_antisymmetric (n Q : ℕ) (x : Space Q) :
    Antisymmetric (normalizedTensorReadout n Q x) := by
  intro i j hij a
  simp [normalizedTensorReadout,orderedWedge_swap a i j hij,occupationInner]

theorem tensorExterior_single (n Q : ℕ) (a : Configuration n Q) :
    tensorExterior n Q (Pi.single a 1) = orderedWedge a := by
  simp [tensorExterior,Pi.single_apply,orderedWedge]

theorem normalizedTensorReadout_left_inverse (n Q : ℕ) (ψ : State n Q)
    (hψ : Antisymmetric ψ) :
    normalizedTensorReadout n Q (normalizedTensorExterior n Q ψ) = ψ := by
  funext a
  have h := normalizedTensorExterior_inner n Q (Pi.single a 1) ψ hψ
  rw [normalizedTensorExterior,tensorExterior_single,occupationInner_smul_left] at h
  have hr : star (((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)) =
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) := by simp
  rw [hr] at h
  simpa [normalizedTensorReadout,Pi.single_apply] using h

theorem normalizedTensorExterior_adjoint (n Q : ℕ) (ψ : State n Q) (x : Space Q) :
    occupationInner Q (normalizedTensorExterior n Q ψ) x =
      ∑ a, star (ψ a)*normalizedTensorReadout n Q x a := by
  simp only [normalizedTensorExterior,tensorExterior,occupationInner_smul_left,
    occupationInner_sum_left,normalizedTensorReadout,orderedWedge]
  simp only [Complex.star_def,map_inv₀,Complex.conj_ofReal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem normalizedTensorReadout_sub (n Q : ℕ) (x y : Space Q) :
    normalizedTensorReadout n Q (x-y) =
      fun a => normalizedTensorReadout n Q x a - normalizedTensorReadout n Q y a := by
  funext a
  simp [normalizedTensorReadout,occupationInner,mul_sub,Finset.sum_sub_distrib]

theorem normalizedTensorReadout_norm_le (n Q : ℕ) (x : Space Q) :
    (∑ a, ‖normalizedTensorReadout n Q x a‖^2) ≤ occupationNormSq Q x := by
  let ψ := normalizedTensorReadout n Q x
  let z := normalizedTensorExterior n Q ψ
  let S : ℝ := ∑ a, ‖ψ a‖^2
  have he (a : Configuration n Q) : star (ψ a)*ψ a = ((‖ψ a‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    rfl
  have hzx : occupationInner Q z x = (S : ℂ) := by
    rw [normalizedTensorExterior_adjoint]
    change (∑ a, star (ψ a)*ψ a) = (S : ℂ)
    simp only [he,← Complex.ofReal_sum]
    rfl
  have hzz : occupationInner Q z z = (S : ℂ) := by
    rw [occupationInner_self,normalizedTensorExterior_norm n Q ψ
      (normalizedTensorReadout_antisymmetric n Q x)]
  have hxz : occupationInner Q x z = (S : ℂ) := by
    rw [← occupationInner_star,hzx]
    simp
  have hs : occupationNormSq Q (x-z) = occupationNormSq Q x-S := by
    apply Complex.ofReal_injective
    rw [← occupationInner_self]
    have hsub : occupationInner Q (x-z) (x-z) =
        occupationInner Q x x - occupationInner Q x z -
          occupationInner Q z x + occupationInner Q z z := by
      simp [occupationInner,sub_mul,mul_sub,Finset.sum_sub_distrib]
      ring
    rw [hsub,occupationInner_self,hzx,hxz,hzz]
    push_cast
    ring
  have hp := occupationNormSq_nonneg Q (x-z)
  rw [hs] at hp
  exact sub_nonneg.mp hp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_KernelReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem headPairAmplitude_readout (n Q : ℕ) (x : Space Q) (p : ℕ)
    (b : Configuration n Q) :
    headPairAmplitude (normalizedTensorReadout (n+2) Q x) p b =
      (((Real.sqrt ((n+2).factorial : ℝ))⁻¹ : ℂ)*(Real.sqrt 2 : ℂ)) *
        occupationInner Q (orderedWedge b) (sourcePairEnd Q p x) := by
  have he (i j : Fin (Q+1)) :
      occupationInner Q (orderedWedge (Fin.cons i (Fin.cons j b))) x =
        occupationInner Q (orderedWedge b) (annihilate j (annihilate i x)) := by
    rw [orderedWedge_cons,orderedWedge_cons,create_annihilate_adjoint,create_annihilate_adjoint]
  simp only [headPairAmplitude,normalizedTensorReadout,he,sourcePairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_right,occupationInner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  push_cast
  field_simp

theorem normalizedTensorReadout_zero_energy (n Q : ℕ) (x : Space Q)
    (hx : sourceFockEnergy Q x=0) :
    energy (normalizedTensorReadout (n+2) Q x)=0 := by
  rw [energy_head_pair n Q _ (normalizedTensorReadout_antisymmetric (n+2) Q x)]
  have hp := (sourceFockEnergy_eq_zero Q x).mp hx
  have hs : (∑ p ∈ Finset.range (2*Q-1), ∑ b : Configuration n Q,
      ‖headPairAmplitude (normalizedTensorReadout (n+2) Q x) p b‖^2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hpr
    simp [headPairAmplitude_readout,hp p hpr,occupationInner]
  rw [hs,mul_zero]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators
open Fock

theorem distanceToLaughlinSq_le {N Q : ℕ} (ψ : State N Q) (c : ℂ) :
    distanceToLaughlinSq ψ ≤ ∑ a, ‖ψ a-c*laughlinVector N Q a‖^2 := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨d,rfl⟩
    exact Finset.sum_nonneg (fun a ha => sq_nonneg _)
  · exact ⟨c,rfl⟩

theorem mainTarget_proved_oai : MainTarget := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_kernel_distance_uniform
  refine ⟨Q₀+2,by omega,fun N hN ψ hψ => ?_⟩
  have hN2 : 2 ≤ N := by omega
  obtain ⟨n,rfl⟩ : ∃ n, N=n+2 := ⟨N-2,by omega⟩
  have hQ : Q₀ ≤ 3*(n+2-1) := by omega
  let Q := 3*(n+2-1)
  let x := normalizedTensorExterior (n+2) Q ψ
  obtain ⟨y,hy,hb⟩ := hgap Q hQ x
  have hyE : sourceFockEnergy Q y=0 := (sourceFockHamiltonian_kernel Q y).mp hy
  have hrE : energy (normalizedTensorReadout (n+2) Q y)=0 :=
    normalizedTensorReadout_zero_energy n Q y hyE
  have hrA := normalizedTensorReadout_antisymmetric (n+2) Q y
  obtain ⟨c,hc⟩ := (physical_Laughlin_kernel (show 2 ≤ n+2 by omega)
    (normalizedTensorReadout (n+2) Q y) hrA).mp hrE
  have hread : normalizedTensorReadout (n+2) Q (x-y) =
      fun a => ψ a-c*laughlinVector (n+2) Q a := by
    rw [normalizedTensorReadout_sub,normalizedTensorReadout_left_inverse (n+2) Q ψ hψ,hc]
  have hnorm := normalizedTensorReadout_norm_le (n+2) Q (x-y)
  rw [hread] at hnorm
  have hdist := distanceToLaughlinSq_le ψ c
  have hE : sourceFockEnergy Q x=energy ψ := normalizedTensorExterior_energy n Q ψ hψ
  rw [hE] at hb
  exact (mul_le_mul_of_nonneg_left (hdist.trans hnorm) (by norm_num : (0 : ℝ) ≤ 1/100)).trans hb

end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.mainTarget_proved_oai := @OAI.Laughlin.mainTarget_proved_oai
