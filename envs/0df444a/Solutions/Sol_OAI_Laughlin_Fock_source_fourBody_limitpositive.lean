-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_fourBody_limitpositive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:38:51.178544+00:00
-- url     : https://prove2.me/submissions/36ccf874-ea07-41a6-993b-3a53eae16e59

import Mathlib
import Definitions.Def_OAIQ047L002
import Theorems.Thm_OAI_Laughlin_Certificate_scaled_four_body_certificates
import Theorems.Thm_OAI_Laughlin_Fock_source_fourBody_physical_L

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

theorem vacuum_bidegree (Q : ℕ) : OccupationBidegree Q 0 0 (1 : Space Q) := by
  intro A hA
  have hn : (∅ : Finset (Fin (Q+1))) ≠ A := by intro he; subst A; simp at hA
  rw [← occupation_empty]
  simp [Module.Basis.repr_self,hn]

theorem create_bidegree (Q n w : ℕ) (x : Space Q) (hx : OccupationBidegree Q n w x)
    (i : Fin (Q+1)) : OccupationBidegree Q (n+1) (w+i.val) (create i x) := by
  intro A hA
  rw [create_coordinate]
  by_cases hi : i ∈ A
  · rw [ite_eq_left hi]
    have hc := Finset.card_erase_of_mem hi
    have hw := Finset.sum_erase_add A (fun j : Fin (Q+1) => j.val) hi
    have hlow : (A.erase i).card ≠ n ∨ (∑ j ∈ A.erase i, j.val) ≠ w := by
      rcases hA with hA | hA
      · left; have hp := Finset.card_pos.mpr ⟨i,hi⟩; omega
      · right; omega
    rw [hx (A.erase i) hlow,mul_zero]
  · rw [ite_eq_right hi]

theorem four_create_bidegree (Q : ℕ) (a b c d : Fin (Q+1)) :
    OccupationBidegree Q 4 (a.val+b.val+c.val+d.val)
      (create a (create b (create c (create d (1 : Space Q))))) := by
  have h := create_bidegree Q _ _ _
    (create_bidegree Q _ _ _ (create_bidegree Q _ _ _
      (create_bidegree Q 0 0 _ (vacuum_bidegree Q) d) c) b) a
  convert h using 1; omega

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_FourLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationBasis_four (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    occupationBasis Q A =
      create (occupationFourLabels Q A hA 0) (create (occupationFourLabels Q A hA 1)
        (create (occupationFourLabels Q A hA 2) (create (occupationFourLabels Q A hA 3) (1 : Space Q)))) := by
  let B : Set.powersetCard (Fin (Q+1)) 4 := ⟨A,hA⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra B.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply,occupationFourLabels,B,create,Pi.basisFun_apply,mode,Matrix.vecTail,Function.comp_def]

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

theorem create_annihilate_adjoint_right (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

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

theorem occupation_matrix_quadratic_positive {I : Type*} [Fintype I]
    (Q : ℕ) (M : Matrix I I ℂ) (hM : M.PosSemidef) (v : I → Space Q) :
    0 ≤ (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)).re := by
  have he : (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)) =
      ∑ A : Finset (Fin (Q+1)), star (fun i => (occupationBasis Q).repr (v i) A) ⬝ᵥ
        (M*ᵥ (fun i => (occupationBasis Q).repr (v i) A)) := by
    simp only [occupationInner,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro A hA
    ring
  rw [he,Complex.re_sum]
  exact Finset.sum_nonneg (fun A hA => (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1)

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
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_OscillatorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem sqrtFactorial_pos (n : ℕ) : 0 < sqrtFactorial n := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos n

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
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_SourceIntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_one_sum (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U 1 z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩]
  simp only [Int.natCast_one,one_pow,mul_one]
  rw [← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter,List.toFinset_range]
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_filter,Finset.mem_range] at hh ⊢
    omega
  · intro h hh hn
    simp only [Finset.mem_range,Finset.mem_filter,decide_eq_true_eq,not_and] at hh hn
    by_cases hhz : h ≤ z
    · have hbound : ¬ p+z ≤ T+h := hn (by omega)
      rw [Nat.choose_eq_zero_of_lt (by omega : T-z < p-h)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : z < h)]
      simp

theorem integerCouplingPolynomial_coeff (z n p : ℕ) (hp : p ≤ z+n) :
    (integerCouplingPolynomial z n).coeff p = U 1 z (z+n) p := by
  rw [U_one_sum z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold integerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  have hpos : (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 := by simp
  rw [hneg,hpos,coeff_X_add_C_pow,coeff_X_add_C_pow]
  simp

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Polynomial_SourceEqualSpinPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators
open Polynomial

theorem equalSpin_polynomial (u : ℝ) (z n : ℕ) :
    couplingPolynomial u u z n = C (u^(z+n)) *
      (Certificate.integerCouplingPolynomial z n).map (Int.castRingHom ℝ) := by
  simp only [couplingPolynomial,Certificate.integerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,pow_add,C_mul,C_pow]
  rw [show C u * X-C u = C u*(X-1) by ring,
    show C u * X+C u = C u*(X+1) by ring,mul_pow,mul_pow]
  ring

theorem equalSpin_polynomialCoefficient (u : ℝ) (z n p : ℕ) (hp : p ≤ z+n) :
    couplingPolynomialCoefficient u u z n p =
      u^(z+n) * (Certificate.U 1 z (z+n) p : ℝ) *
        sqrtFactorial p * sqrtFactorial (z+n-p) / (sqrtFactorial z * sqrtFactorial n) := by
  unfold couplingPolynomialCoefficient
  rw [equalSpin_polynomial,coeff_C_mul,coeff_map,Certificate.integerCouplingPolynomial_coeff z n p hp]
  simp only [Int.coe_castRingHom,monomialNormFactor]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FactorialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem source_fourBody_factorial_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) (hr : r ≤ j+k) :
    fourBodyLimitCoefficient r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) * (Certificate.V r D T p j k : ℝ) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  have hi : r+(j+k-r)=j+k := by omega
  have ho : (D-r)+(T-D)=T-r := by omega
  have hk : j+k-j=k := by omega
  have hb : T-r-p=j+k-r := by omega
  rw [fourBodyLimitCoefficient,ite_eq_left hr,
    equalSpin_polynomialCoefficient _ r (j+k-r) j (by omega),
    equalSpin_polynomialCoefficient _ (D-r) (T-D) p (by omega)]
  rw [hi,ho,hk,hb]
  simp only [Certificate.V,ite_eq_left hr,Int.cast_mul]
  rw [pow_add]
  field_simp [ne_of_gt (sqrtFactorial_pos r),ne_of_gt (sqrtFactorial_pos (D-r)),
    ne_of_gt (sqrtFactorial_pos (T-D)),ne_of_gt (sqrtFactorial_pos (j+k-r))]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RadicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem fourBodyRadical_factorial (r D T p j k : ℕ) (hr : r ≤ T) :
    fourBodyRadical r D T p j k =
      Real.sqrt 2 * (Real.sqrt (1/2))^(j+k+(T-r)) *
      sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
        (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D)) := by
  let m := j+k+(T-r)
  have hm : (1 : ℤ)-(j : ℤ)-k-T+r = 1-(m : ℤ) := by
    dsimp [m]
    simp only [Nat.cast_sub hr]
    omega
  have hp : (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) = 2*(1/2 : ℝ)^m := by
    rw [hm,zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),zpow_one,zpow_natCast]
    simp [div_eq_mul_inv]
  let a := Real.sqrt 2 * (Real.sqrt (1/2))^m *
    sqrtFactorial j * sqrtFactorial k * sqrtFactorial p /
      (sqrtFactorial r * sqrtFactorial (D-r) * sqrtFactorial (T-D))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) *
    ((j.factorial : ℝ)*(k.factorial : ℝ)*(p.factorial : ℝ) /
      ((r.factorial : ℝ)*((D-r).factorial : ℝ)*((T-D).factorial : ℝ))) := by
    rw [hp]
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    rw [show ((Real.sqrt (1/2))^m)^2 = (1/2 : ℝ)^m by
      rw [← pow_mul,mul_comm m 2,pow_mul,Real.sq_sqrt (by norm_num)]]
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sq_sqrt (Nat.cast_nonneg _)]
    ring_nf
    norm_num
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_fourBody_radical_coefficient (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    fourBodyLimitCoefficient r D T p j k =
      (Certificate.V r D T p j k : ℝ) * fourBodyRadical r D T p j k := by
  by_cases hr : r ≤ j+k
  · rw [source_fourBody_factorial_coefficient r D T p j k hrD hDT hT hr,
      fourBodyRadical_factorial r D T p j k (by omega)]
    ring
  · simp [fourBodyLimitCoefficient,Certificate.V,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RadicalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem source_Y_radical_cancellation (D r s t p j q l : ℕ)
    (hor : Odd r) (hos : Odd s) (he : t ≤ p+j) (hf : t ≤ q+l) :
    alphaRadical t p j * alphaRadical t q l *
      fourBodyRadical r D (p+j+(q+l-t)) p j (q+l-t) *
      fourBodyRadical s D (p+j+(q+l-t)) q l (p+j-t) =
    Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  let e : ℤ := 1-2*(T : ℤ)+p+q-t+((r+s)/2 : ℕ)
  have hT : p+j+k=T := rfl
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  have hTr : (p : ℤ)+j+k=T := by exact_mod_cast hT
  have hTr' : (q : ℤ)+l+i=T := by exact_mod_cast hT'
  have heven : (((r+s)/2 : ℕ) : ℤ)*2=(r : ℤ)+s := by
    rcases hor with ⟨a,ha⟩; rcases hos with ⟨b,hb⟩
    omega
  have hex : ((p : ℤ)-t)+((q : ℤ)-t)+((1 : ℤ)-j-k-T+r)+((1 : ℤ)-l-i-T+s)=e*2 := by
    dsimp [e]; omega
  have hpowers : (2 : ℝ)^((p : ℤ)-t) * (2 : ℝ)^((q : ℤ)-t) *
      (2 : ℝ)^((1 : ℤ)-j-k-T+r) * (2 : ℝ)^((1 : ℤ)-l-i-T+s) = ((2 : ℝ)^e)^2 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),hex,zpow_mul]
    norm_num
  let F : ℝ := ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ))^2 /
    ((r.factorial : ℝ)*((D-r).factorial : ℝ)*(s.factorial : ℝ)*((D-s).factorial : ℝ)*((T-D).factorial : ℝ)^2)
  have hsq : (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i)^2 =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l)^2 := by
    simp only [alphaRadical,fourBodyRadical,mul_pow]
    have hc0 : 0 ≤ sourceCopyWeight D r * sourceCopyWeight D s := by
      unfold sourceCopyWeight; positivity
    rw [Real.sq_sqrt hc0]
    repeat rw [Real.sq_sqrt (by positivity)]
    change (2^((p : ℤ)-t)*((t.factorial : ℝ)*i.factorial/(p.factorial*j.factorial))) *
      (2^((q : ℤ)-t)*((t.factorial : ℝ)*k.factorial/(q.factorial*l.factorial))) *
      (2^((1 : ℤ)-j-k-T+r)*((j.factorial : ℝ)*k.factorial*p.factorial /
        (r.factorial*(D-r).factorial*(T-D).factorial))) *
      (2^((1 : ℤ)-l-i-T+s)*((l.factorial : ℝ)*i.factorial*q.factorial /
        (s.factorial*(D-s).factorial*(T-D).factorial))) = _
    calc
      _ = (2^((p : ℤ)-t)*2^((q : ℤ)-t)*2^((1 : ℤ)-j-k-T+r)*2^((1 : ℤ)-l-i-T+s))*F := by
        dsimp [F]
        field_simp
      _ = ((2 : ℝ)^e)^2*F := by rw [hpowers]
      _ = _ := by
        dsimp [F,sourceYFactor,sourceCopyWeight]
        change ((2 : ℝ)^e)^2 * _ = (1/((r.factorial : ℝ)*(D-r).factorial) *
          (1/((s.factorial : ℝ)*(D-s).factorial))) *
          ((2 : ℝ)^e * ((i.factorial : ℝ)*k.factorial*t.factorial/(T-D).factorial))^2
        field_simp
  have hl : 0 ≤ alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i := by unfold alphaRadical fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
    unfold sourceYFactor; positivity
  nlinarith only [hsq,hl,hr]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sourceAlpha_factor (t : ℕ) (e : ℕ × ℕ × ℤ) :
    sourceAlpha t e = (e.2.2 : ℝ)/(10^7) * alphaRadical t e.1 e.2.1 := rfl

theorem fourErrorLimitEntry_certificate (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s)
    (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1) :
    fourErrorLimitEntry D r s t e f =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yEntry D r s t e f : ℝ) := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp only at he hf ⊢
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  by_cases hD : D ≤ T
  · have heq : fourErrorLimitEntry D r s t (p,j,a) (q,l,b) =
        sourceAlpha t (p,j,a) * sourceAlpha t (q,l,b) *
          fourBodyLimitCoefficient r D T p j k * fourBodyLimitCoefficient s D T q l i := by
      simp only [fourErrorLimitEntry]; exact ite_eq_left hD
    rw [heq,sourceAlpha_factor,sourceAlpha_factor,
      source_fourBody_radical_coefficient r D T p j k hr hD rfl,
      source_fourBody_radical_coefficient s D T q l i hs hD hT']
    dsimp only
    calc
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k * fourBodyRadical s D T q l i) := by ring
      _ = ((a : ℝ)*(b : ℝ)*(Certificate.V r D T p j k : ℝ)*(Certificate.V s D T q l i : ℝ)/(10^14)) *
          (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)*sourceYFactor D r s t p j q l) := by
        rw [source_Y_radical_cancellation D r s t p j q l hor hos he hf]
      _ = _ := by
        simp only [Certificate.yEntry]
        rw [ite_eq_left hD]
        push_cast
        dsimp [sourceYFactor,i,k,T]
        ring
  · simp only [fourErrorLimitEntry,Certificate.yEntry]
    rw [ite_eq_right hD,ite_eq_right hD]
    simp

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem fourErrorLimitRow_certificate (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) (hrow : row ∈ Certificate.rows) :
    fourErrorLimitRow D r s row =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ) := by
  unfold fourErrorLimitRow
  have he : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      fourErrorLimitEntry D r s row.1 e f =
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ) := by
    intro e he f hf
    exact fourErrorLimitEntry_certificate D r s row.1 e f hr hs hor hos
      (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
          (Certificate.yEntry D r s row.1 e f : ℝ))).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left; intro e he'
      apply congrArg List.sum
      apply List.map_congr_left; intro f hf'
      exact he e he' f hf'
    _ = _ := by
      simp_rw [real_list_sum_scale]
      unfold Certificate.yRow
      push_cast
      simp only [List.map_map,Function.comp_def]
      push_cast
      simp only [List.map_map,Function.comp_def]

theorem source_fourBody_error_certificate_identity (D r s : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    limitFourError D r s = Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
      (Certificate.Y D r s : ℝ) := by
  unfold limitFourError
  have he : Certificate.rows.map (fourErrorLimitRow D r s) = Certificate.rows.map (fun row =>
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s)/(10^14)) *
        (Certificate.yRow D r s row : ℝ)) := by
    apply List.map_congr_left; intro row hrow
    exact fourErrorLimitRow_certificate D r s hr hs hor hos row hrow
  rw [he,real_list_sum_scale]
  unfold Certificate.Y
  push_cast
  simp only [List.map_map,Function.comp_def]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ErrorMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Matrix Topology
open Filter

theorem sourceCopyWeight_certificate (D : ℕ) (i : Fin ((D+1)/2)) :
    sourceCopyWeight D (Certificate.copyLabel i) = (Certificate.copyWeight D i : ℝ) := by
  simp [sourceCopyWeight,Certificate.copyWeight]

theorem source_fourBody_error_matrix (D : ℕ) (i j : Fin ((D+1)/2)) :
    limitFourError D (Certificate.copyLabel i) (Certificate.copyLabel j) = Certificate.scaledError D i j := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  have hoj : Odd (Certificate.copyLabel j) := ⟨j.val,by unfold Certificate.copyLabel; omega⟩
  rw [source_fourBody_error_certificate_identity D _ _ hi hj hoi hoj,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledError,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem limitFourColumn_adjoint (Q r D : ℕ) (x : Space Q) :
    occupationInner Q (limitFourColumn Q r D) x = occupationInner Q (1 : Space Q) (limitFourCopyEnd Q r D x) := by
  simp only [limitFourColumn,limitFourCopyEnd,weightedFourEnd,limitFourEnd,limitPairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,create_annihilate_adjoint,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  push_cast
  ring

theorem limitFourColumn_bidegree (Q r D : ℕ) : OccupationBidegree Q 4 (D+1) (limitFourColumn Q r D) := by
  intro A hA
  simp only [limitFourColumn,map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero; intro p hp
  apply Finset.sum_eq_zero; intro j hj
  apply Finset.sum_eq_zero; intro k hk
  apply Finset.sum_eq_zero; intro x hx
  apply Finset.sum_eq_zero; intro y hy
  by_cases hS : p+j.val+k.val=D
  · by_cases hP : x.val+y.val=p+1
    · have hv := four_create_bidegree Q x y j k A (by
        rcases hA with hA | hA
        · exact Or.inl hA
        · exact Or.inr (by omega))
      rw [hv,mul_zero]
    · simp [pairLimitCoefficient,hP]
  · simp [limitSliceCoefficient,hS]

theorem occupationInner_vacuum (Q : ℕ) : occupationInner Q (1 : Space Q) 1 = 1 := by
  rw [← occupation_empty Q]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem limitFourColumn_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    occupationInner Q (limitFourColumn Q r D)
      (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) := by
  rw [limitFourColumn_adjoint,source_fourBody_physical_L Q r D hr hor a b c d hab hbc hcd hT,
    occupationInner_smul_right,occupationInner_vacuum,mul_one]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_OccupationCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_basis_right (Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    occupationInner Q x (occupationBasis Q A) = star ((occupationBasis Q).repr x A) := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem limitFourColumn_occupation_coefficient (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (limitFourColumn Q r D) A = (fourOccupationCoefficient Q r D A : ℂ) := by
  by_cases hA : A.card=4
  · by_cases hw : (∑ i ∈ A, i.val)=D+1
    · let l := occupationFourLabels Q A hA
      have h := limitFourColumn_physical_L Q r D hr hor (l 0) (l 1) (l 2) (l 3)
        (l.strictMono (by decide)) (l.strictMono (by decide)) (l.strictMono (by decide))
        (by rw [← occupationFourLabels_sum Q A hA]; exact hw)
      rw [← occupationBasis_four Q A hA,occupationInner_basis_right] at h
      have hs := congrArg star h
      simpa [fourOccupationCoefficient,hA,hw,l] using hs
    · rw [limitFourColumn_bidegree Q r D A (Or.inr hw)]
      simp [fourOccupationCoefficient,hA,hw]
  · rw [limitFourColumn_bidegree Q r D A (Or.inl hA)]
    simp [fourOccupationCoefficient,hA]

theorem limitFourColumn_gram_occupation (Q r s D : ℕ) (hr : r ≤ D) (hs : s ≤ D)
    (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((∑ A : Finset (Fin (Q+1)), fourOccupationCoefficient Q r D A *
        fourOccupationCoefficient Q s D A : ℝ) : ℂ) := by
  simp [occupationInner,limitFourColumn_occupation_coefficient Q r D hr hor,
    limitFourColumn_occupation_coefficient Q s D hs hos]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Quadruples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

private theorem quadTail_nodup (D a b : ℕ) : (quadTail D a b).Nodup := by
  apply List.Nodup.filterMap _ List.nodup_range
  intro c c' t hc hc'
  dsimp only at hc hc'
  split_ifs at hc with h
  · split_ifs at hc' with h'
    · simp only [Option.mem_def,Option.some.injEq] at hc hc'
      have he := hc.trans hc'.symm
      exact congrArg (fun u : ℕ×ℕ×ℕ×ℕ => u.2.2.1) he
    · simp at hc'
  · simp at hc

theorem quadruples_nodup (D : ℕ) : (quadruples D).Nodup := by
  change ((List.range (D+2)).flatMap
    (fun a => (List.range (D+2)).flatMap (quadTail D a))).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ha
    apply List.nodup_flatMap.mpr
    constructor
    · intro b hb; exact quadTail_nodup D a b
    · apply List.nodup_range.imp
      intro b b' hne t ht ht'
      obtain ⟨x,y,z,w⟩ := t
      have h := (mem_quadTail D a b x y z w).mp ht
      have h' := (mem_quadTail D a b' x y z w).mp ht'
      exact hne (h.2.1.symm.trans h'.2.1)
  · apply List.nodup_range.imp
    intro a a' hne t ht ht'
    obtain ⟨b,hb,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b',hb',ht'⟩ := List.mem_flatMap.mp ht'
    obtain ⟨x,y,z,w⟩ := t
    have h := (mem_quadTail D a b x y z w).mp ht
    have h' := (mem_quadTail D a' b' x y z w).mp ht'
    exact hne (h.1.symm.trans h'.1)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_FourOccupationEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_fourOccupations (Q D : ℕ) (hQ : D+1 ≤ Q) (f : (ℕ×ℕ×ℕ×ℕ) → ℝ) :
    ∑ A : FourOccupation Q D, f (occupationQuadruple Q D A).val =
      ((Certificate.quadruples D).map f).sum := by
  classical
  let : Fintype {t : ℕ×ℕ×ℕ×ℕ // t ∈ Certificate.quadruples D} :=
    Fintype.ofFinset (Certificate.quadruples D).toFinset (by intro t; change t ∈ (Certificate.quadruples D).toFinset ↔ t ∈ Certificate.quadruples D; simp)
  rw [← List.sum_toFinset f (Certificate.quadruples_nodup D)]
  rw [Finset.sum_subtype (p := fun t => t ∈ Certificate.quadruples D) (Certificate.quadruples D).toFinset (by simp)]
  exact (fourOccupationEquiv Q D hQ).sum_comp (fun t => f t.val)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Spin

private theorem sqrt_weight_product (u v f : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hf : 0 ≤ f) :
    Real.sqrt (u/f)*Real.sqrt (v/f) = Real.sqrt (u*v)/f := by
  rw [Real.sqrt_div hu,Real.sqrt_div hv]

  rw [div_mul_div_comm,Real.mul_self_sqrt hf,← Real.sqrt_mul hu]

private theorem fourOccupation_product (Q r s D : ℕ) (A : FourOccupation Q D) :
    fourOccupationCoefficient Q r D A.val * fourOccupationCoefficient Q s D A.val =
      let t := (occupationQuadruple Q D A).val
      Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        ((Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
          ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial)) := by
  simp only [fourOccupationCoefficient,dite_eq_left A.property.1,ite_eq_left A.property.2,occupationQuadruple]
  have hr : 0 ≤ sourceCopyWeight D r := by unfold sourceCopyWeight; positivity
  have hs : 0 ≤ sourceCopyWeight D s := by unfold sourceCopyWeight; positivity
  have hf : 0 ≤ (((occupationFourLabels Q A.val A.property.1 0).val.factorial : ℝ) *
    (occupationFourLabels Q A.val A.property.1 1).val.factorial *
    (occupationFourLabels Q A.val A.property.1 2).val.factorial *
    (occupationFourLabels Q A.val A.property.1 3).val.factorial) := by positivity
  rw [show ∀ a b c d : ℝ, (a*b)*(c*d)=(a*c)*(b*d) from by intros; ring,
    sqrt_weight_product _ _ _ hr hs hf]
  ring

theorem source_fourBody_physical_Gram (Q r s D : ℕ) (hQ : D+1 ≤ Q)
    (hr : r ≤ D) (hs : s ≤ D) (hor : Odd r) (hos : Odd s) :
    occupationInner Q (limitFourColumn Q r D) (limitFourColumn Q s D) =
      ((Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) *
        (Certificate.Z D r s : ℝ) : ℝ) : ℂ) := by
  classical
  rw [limitFourColumn_gram_occupation Q r s D hr hs hor hos]
  congr 1
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  let f := fun A => fourOccupationCoefficient Q r D A * fourOccupationCoefficient Q s D A
  have hsum : ∑ A, f A = ∑ A ∈ Finset.univ.filter P, f A := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [f,fourOccupationCoefficient,hc,hw]
    · simp [f,fourOccupationCoefficient,hc]
  change ∑ A, f A = _
  rw [hsum,Finset.sum_subtype (p := P) (Finset.univ.filter P) (by simp)]
  change (∑ A : FourOccupation Q D, fourOccupationCoefficient Q r D A.val *
    fourOccupationCoefficient Q s D A.val) = _
  simp_rw [fourOccupation_product]
  rw [← Finset.mul_sum,sum_fourOccupations Q D hQ (fun t =>
    (Certificate.L D r t : ℝ)*(Certificate.L D s t : ℝ) /
      ((t.1.factorial : ℝ)*t.2.1.factorial*t.2.2.1.factorial*t.2.2.2.factorial))]
  simp only [Certificate.Z]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  rfl

theorem source_fourBody_physical_scaledGram (Q D : ℕ) (hQ : D+1 ≤ Q)
    (i j : Fin ((D+1)/2)) :
    occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
      (limitFourColumn Q (Certificate.copyLabel j) D) =
      (Certificate.scaledGram D i j : ℂ) := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  rw [source_fourBody_physical_Gram Q _ _ D hQ hi hj
    ⟨i.val,by unfold Certificate.copyLabel; omega⟩ ⟨j.val,by unfold Certificate.copyLabel; omega⟩,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledGram,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.gramRational,Rat.coe_castHom]
  push_cast
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_ColumnExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem fourOccupation_adjoint (Q D : ℕ) (A : FourOccupation Q D) (x y : Space Q) :
    occupationInner Q x (fourOccupationCreate Q D A y) =
      occupationInner Q (fourOccupationEnd Q D A x) y := by
  simp only [fourOccupationCreate,fourOccupationEnd,Module.End.mul_apply,create_annihilate_adjoint_right]

theorem fourOccupationCreate_mul (Q D : ℕ) (A : FourOccupation Q D) (x : Space Q) :
    fourOccupationCreate Q D A x = occupationBasis Q A.val * x := by
  rw [occupationBasis_four Q A.val A.property.1]
  simp [fourOccupationCreate,create,mul_assoc]

theorem limitFourColumn_mul_adjoint (Q r D : ℕ) (x y : Space Q) :
    occupationInner Q x (limitFourColumn Q r D * y) =
      occupationInner Q (limitFourCopyEnd Q r D x) y := by
  simp only [limitFourColumn,Finset.sum_mul,smul_mul_assoc]
  simp only [limitFourCopyEnd,weightedFourEnd,limitFourEnd,limitPairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal]
  simp only [create,LinearMap.coe_mk,AddHom.coe_mk,mul_one,mul_assoc]
  simp only [show ∀ (i : Fin (Q+1)) (v : Space Q), (ExteriorAlgebra.ι ℂ) (mode i)*v=create i v from by intros; rfl,
    create_annihilate_adjoint_right]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  push_cast
  ring

theorem limitFourColumn_expansion (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) :
    limitFourColumn Q r D = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • occupationBasis Q A.val := by
  classical
  conv_lhs => rw [← (occupationBasis Q).sum_repr (limitFourColumn Q r D)]
  simp_rw [limitFourColumn_occupation_coefficient Q r D hr hor]
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  rw [← Finset.sum_subset (Finset.filter_subset P Finset.univ) (f := fun A =>
    (fourOccupationCoefficient Q r D A : ℂ) • occupationBasis Q A)]
  · exact Finset.sum_subtype _ (by simp [P]) _
  · intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [fourOccupationCoefficient,hc,hw]
    · simp [fourOccupationCoefficient,hc]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_EndExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem occupationInner_left_ext (Q : ℕ) (x y : Space Q)
    (h : ∀ z, occupationInner Q x z = occupationInner Q y z) : x=y := by
  apply (occupationBasis Q).repr.injective
  ext A
  have hA := h (occupationBasis Q A)
  rw [occupationInner_basis_right,occupationInner_basis_right] at hA
  exact star_injective hA

theorem limitFourCopyEnd_expansion (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) (x : Space Q) :
    limitFourCopyEnd Q r D x = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • fourOccupationEnd Q D A x := by
  apply occupationInner_left_ext
  intro y
  rw [← limitFourColumn_mul_adjoint,limitFourColumn_expansion Q r D hr hor]
  simp only [Finset.sum_mul,smul_mul_assoc,occupationInner_sum_right,occupationInner_sum_left,
    occupationInner_smul_right,occupationInner_smul_left,Complex.star_def,Complex.conj_ofReal,
    ← fourOccupationCreate_mul,fourOccupation_adjoint]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

theorem physicalLimitGram_eq (Q D : ℕ) (hQ : D+1 ≤ Q) :
    physicalLimitGram Q D = Certificate.scaledGram D := by
  ext i j
  simp [physicalLimitGram,source_fourBody_physical_scaledGram Q D hQ]

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix D i j

theorem source_physical_four_body_certificates (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalLimitGram Q D * (Certificate.certificateDiagonal D-physicalLimitError D) *
      physicalLimitGram Q D).PosSemidef := by
  rw [physicalLimitGram_eq Q D hQ,physicalLimitError_eq]
  exact Certificate.scaled_four_body_certificates D hD₁ hD₂

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_ComplexCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem complex_compression_positive_iff (W : E →ₗ[ℂ] F) (C : E →ₗ[ℂ] E) :
    (∀ x : E, 0 ≤ (⟪x, W.adjoint (W (C (W.adjoint (W x))))⟫_ℂ).re) ↔
      (∀ y : F, 0 ≤ (⟪y, W (C (W.adjoint y))⟫_ℂ).re) := by
  simp only [W.adjoint_inner_right, ← W.adjoint_inner_left]
  constructor
  · intro h y
    have hy : W.adjoint y ∈ (W.adjoint ∘ₗ W).range := by
      rw [W.range_adjoint_comp_self]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    change W.adjoint (W x) = W.adjoint y at hx
    simpa only [hx] using h x
  · intro h x
    exact h (W x)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_MatrixPhysicalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Matrix InnerProductSpace ComplexOrder
open Matrix

theorem matrix_physical_compression {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix J I ℂ) (C : Matrix I I ℂ)
    (hC : C.IsHermitian) (hG : ((Wᴴ*W)*C*(Wᴴ*W)).PosSemidef) :
    (W*C*Wᴴ).PosSemidef := by
  have hc : (W*C*Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hC
  have hpos : ∀ x : EuclideanSpace ℂ I,
      0 ≤ (⟪x,W.toEuclideanLin.adjoint (W.toEuclideanLin
        (C.toEuclideanLin (W.toEuclideanLin.adjoint (W.toEuclideanLin x))))⟫_ℂ).re := by
    intro x
    have hp := hG.dotProduct_mulVec_nonneg (WithLp.ofLp x)
    have hp' := (Complex.nonneg_iff.mp hp).1
    simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toLpLin,Matrix.toLin'_apply,
      Matrix.mulVec_mulVec,Matrix.mul_assoc,dotProduct_comm] using hp'
  have hout := (complex_compression_positive_iff W.toEuclideanLin C.toEuclideanLin).mp hpos
  rw [← Matrix.isPositive_toEuclideanLin_iff,LinearMap.IsPositive,
    Matrix.isSymmetric_toEuclideanLin_iff]
  refine ⟨hc,?_⟩
  intro y
  have hy := hout y
  rw [inner_re_symm]
  change 0 ≤ (⟪y,(W*C*Wᴴ).toEuclideanLin y⟫_ℂ).re
  simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toLpLin,Matrix.toLin'_apply,
    Matrix.mulVec_mulVec,Matrix.mul_assoc] using hy

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_RealComplexMatrixPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem real_complex_matrix_hermitian {I : Type*} (M : Matrix I I ℝ) (hM : M.IsHermitian) :
    (M.map Complex.ofReal).IsHermitian := by
  ext i j
  have h := congrFun (congrFun hM.eq i) j
  simpa [Matrix.conjTranspose_apply,Matrix.map_apply] using congrArg Complex.ofReal h

theorem real_complex_matrix_positive {I : Type*} [Fintype I]
    (M : Matrix I I ℝ) (hM : M.PosSemidef) : (M.map Complex.ofReal).PosSemidef := by
  have hh := real_complex_matrix_hermitian M hM.isHermitian
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · have hr := hM.dotProduct_mulVec_nonneg (fun i => (z i).re)
    have hi := hM.dotProduct_mulVec_nonneg (fun i => (z i).im)
    have he : (star z ⬝ᵥ ((M.map Complex.ofReal)*ᵥ z)).re =
        (star (fun i => (z i).re) ⬝ᵥ (M*ᵥ (fun i => (z i).re))) +
        (star (fun i => (z i).im) ⬝ᵥ (M*ᵥ (fun i => (z i).im))) := by
      simp [dotProduct,Matrix.mulVec,Complex.mul_re,Complex.mul_im,Complex.re_sum,
        Matrix.map_apply,
        Finset.mul_sum,Finset.sum_add_distrib,sub_eq_add_neg]
    rw [he]
    exact add_nonneg hr hi
  · exact (hh.im_star_dotProduct_mulVec_self z).symm

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_WedgeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem physicalWedgeColumns_gram (Q D : ℕ) (hQ : D+1 ≤ Q) :
    (physicalWedgeColumns Q D)ᴴ * physicalWedgeColumns Q D =
      (physicalLimitGram Q D).map Complex.ofReal := by
  rw [physicalLimitGram_eq Q D hQ]
  ext i j
  change occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
    (limitFourColumn Q (Certificate.copyLabel j) D) = _
  exact source_fourBody_physical_scaledGram Q D hQ i j

theorem physicalLimitMiddle_hermitian (D : ℕ) : (physicalLimitMiddle D).IsHermitian := by
  apply real_complex_matrix_hermitian
  apply Matrix.IsHermitian.sub
  · simp [Certificate.certificateDiagonal,Matrix.IsHermitian]
  · rw [physicalLimitError_eq]
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Certificate.scaledError,
      Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
    rw [Certificate.Y_symm D (Certificate.copyLabel j) (Certificate.copyLabel i)]
    ring

theorem source_physical_wedge_compression (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalWedgeColumns Q D * physicalLimitMiddle D * (physicalWedgeColumns Q D)ᴴ).PosSemidef := by
  apply matrix_physical_compression _ _ (physicalLimitMiddle_hermitian D)
  rw [physicalWedgeColumns_gram Q D hQ]
  have h := real_complex_matrix_positive _ (source_physical_four_body_certificates Q D hQ hD₁ hD₂)
  have hm : ∀ A B : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ,
      (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
    intro A B
    ext i j
    simp [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum]
  simpa only [physicalLimitMiddle,hm] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_LimitPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem physicalFourOccupationColumns_positive (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalFourOccupationColumns Q D * physicalLimitMiddle D *
      (physicalFourOccupationColumns Q D)ᴴ).PosSemidef := by
  have h := (source_physical_wedge_compression Q D hQ hD₁ hD₂).submatrix
    (fun A : FourOccupation Q D => A.val)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext A B
  simp [physicalFourOccupationColumns,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply]

theorem limitFourCopyEnd_matrix_expansion (Q D : ℕ) (i : Fin ((D+1)/2)) (x : Space Q) :
    limitFourCopyEnd Q (Certificate.copyLabel i) D x =
      ∑ A : FourOccupation Q D, star (physicalFourOccupationColumns Q D A i) • fourOccupationEnd Q D A x := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  rw [limitFourCopyEnd_expansion Q _ D hi hoi]
  simp only [physicalFourOccupationColumns,physicalWedgeColumns,
    limitFourColumn_occupation_coefficient Q _ D hi hoi,Complex.star_def,Complex.conj_ofReal]

theorem source_fourBody_limitpositive_oai (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    0 ≤ (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2), physicalLimitMiddle D i j *
      occupationInner Q (limitFourCopyEnd Q (Certificate.copyLabel i) D x)
        (limitFourCopyEnd Q (Certificate.copyLabel j) D x)).re := by
  simp_rw [limitFourCopyEnd_matrix_expansion]
  rw [occupation_matrix_quadratic_factor]
  exact occupation_matrix_quadratic_positive Q _
    (physicalFourOccupationColumns_positive Q D hQ hD₁ hD₂) _

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_fourBody_limitpositive_oai := @OAI.Laughlin.Fock.source_fourBody_limitpositive_oai
