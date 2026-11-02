-- Prove2me | solution 1 for OAI.Laughlin.Fock.fockInclusion_normSq_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:37:50.989201+00:00
-- url     : https://prove2.me/submissions/5304b681-d97b-448d-9d38-dd9110150580

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007
import Definitions.Def_OAIQ050L008

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_Inner
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_SpinRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

theorem occupationInner_basis (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    occupationInner Q (occupationBasis Q A) (occupationBasis Q B) = if A=B then 1 else 0 := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_ModeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem modeInclusion_mode (L Q : ℕ) (h : L ≤ Q) (i : Fin (L+1)) :
    modeInclusion L Q h (mode i) = mode (Fin.castLE (Nat.add_le_add_right h 1) i) := by
  ext j
  change (if hj : j.val ≤ L then (Pi.single i (1 : ℂ) : Orbital L) ⟨j.val,by omega⟩ else 0) =
    (Pi.single (Fin.castLE (Nat.add_le_add_right h 1) i) (1 : ℂ) : Orbital Q) j
  by_cases hj : j.val ≤ L
  · rw [dite_eq_left hj]
    have he : (⟨j.val,by omega⟩ : Fin (L+1)) = i ↔
        j = Fin.castLE (Nat.add_le_add_right h 1) i := by
      constructor <;> intro hh <;> apply Fin.ext
      · exact congrArg (fun k : Fin (L+1) => k.val) hh
      · exact congrArg (fun k : Fin (Q+1) => k.val) hh
    simp only [Pi.single_apply,he]
  · rw [dite_eq_right hj]
    have he : j ≠ Fin.castLE (Nat.add_le_add_right h 1) i := by
      intro hh
      have hv := congrArg (fun k : Fin (Q+1) => k.val) hh
      have := i.isLt
      simp only [Fin.val_castLE] at hv
      omega
    simp [he]

theorem fockInclusion_occupation (L Q : ℕ) (h : L ≤ Q) (A : Finset (Fin (L+1))) :
    fockInclusion L Q h (occupationBasis L A) =
      occupationBasis Q (includedOccupations L Q h A) := by
  let S : Set.powersetCard (Fin (L+1)) A.card := ⟨A,rfl⟩
  let e := (Set.powersetCard.ofFinEmbEquiv.symm S).trans
    (Fin.castLEOrderEmb (Nat.add_le_add_right h 1))
  let T : Set.powersetCard (Fin (Q+1)) A.card := Set.powersetCard.ofFinEmbEquiv e
  have hT : T.val = includedOccupations L Q h A := by
    ext j
    change j ∈ Set.powersetCard.ofFinEmbEquiv e ↔ _
    rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
    simp only [Set.mem_range,includedOccupations,Finset.mem_map]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨Set.powersetCard.ofFinEmbEquiv.symm S i,?_,rfl⟩
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨i,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S i).mpr hi
      exact ⟨a,congrArg (Fin.castLE (Nat.add_le_add_right h 1)) ha⟩
  change fockInclusion L Q h ((Pi.basisFun ℂ (Fin (L+1))).ExteriorAlgebra S.val) = _
  rw [← hT]
  change ExteriorAlgebra.map (modeInclusion L Q h)
    ((Pi.basisFun ℂ (Fin (L+1))).ExteriorAlgebra S.val) =
      (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra T.val
  rw [ExteriorAlgebra.basis_apply_powersetCard,ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.map_apply_ιMulti]
  have he : Set.powersetCard.ofFinEmbEquiv.symm T = e :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply e
  rw [he]
  congr 1
  funext i
  simp only [Function.comp_apply,Pi.basisFun_apply]
  change modeInclusion L Q h (mode (Set.powersetCard.ofFinEmbEquiv.symm S i)) =
    mode (Fin.castLE (Nat.add_le_add_right h 1) (Set.powersetCard.ofFinEmbEquiv.symm S i))
  exact modeInclusion_mode L Q h (Set.powersetCard.ofFinEmbEquiv.symm S i)

theorem includedOccupations_injective (L Q : ℕ) (h : L ≤ Q) :
    Function.Injective (includedOccupations L Q h) := Finset.map_injective _

theorem fockInclusion_inner (L Q : ℕ) (h : L ≤ Q) (x y : Space L) :
    occupationInner Q (fockInclusion L Q h x) (fockInclusion L Q h y) =
      occupationInner L x y := by
  have hb (A B : Finset (Fin (L+1))) :
      occupationInner Q (fockInclusion L Q h (occupationBasis L A))
        (fockInclusion L Q h (occupationBasis L B)) =
          occupationInner L (occupationBasis L A) (occupationBasis L B) := by
    rw [fockInclusion_occupation,fockInclusion_occupation,occupationInner_basis,occupationInner_basis]
    simp only [(includedOccupations_injective L Q h).eq_iff]
  conv_lhs => rw [← (occupationBasis L).sum_repr x,← (occupationBasis L).sum_repr y]
  conv_rhs => rw [← (occupationBasis L).sum_repr x,← (occupationBasis L).sum_repr y]
  simp only [map_sum,map_smul,occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,hb]

theorem fockInclusion_normSq_s50_oai (L Q : ℕ) (h : L ≤ Q) (x : Space L) :
    occupationNormSq Q (fockInclusion L Q h x) = occupationNormSq L x := by
  have hi := fockInclusion_inner L Q h x x
  rw [occupationInner_self,occupationInner_self] at hi
  exact Complex.ofReal_injective hi

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.fockInclusion_normSq_s50_oai := @OAI.Laughlin.Fock.fockInclusion_normSq_s50_oai
