-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceRowFourEntry_physical_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:51:45.496272+00:00
-- url     : https://prove2.me/submissions/56ea3be2-8aab-48ae-9e56-cbba06cbbd69

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j) x) +
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj j)
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

theorem annihilate_sq {Q : ℕ} (i : Fin (Q+1)) : annihilate i * annihilate i = 0 := by
  have h : (2 : ℂ) • (annihilate i * annihilate i) = 0 := by
    simpa only [two_smul] using annihilate_anticommute i i
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

end Laughlin.Fock

end OAI
end

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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_HighestFock
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_SignedCoordinates
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_NormalForm
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Levels
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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_SourceExpansion
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Expansion
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

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_NormalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix

theorem sourceRowFourEntry_physical_s50_oai (Q : ℕ) (hQ : 25 ≤ Q)
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

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceRowFourEntry_physical_s50_oai := @OAI.Laughlin.Fock.sourceRowFourEntry_physical_s50_oai
