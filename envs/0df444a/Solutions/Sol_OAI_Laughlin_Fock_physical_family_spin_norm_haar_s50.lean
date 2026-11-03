-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:21:15.98272+00:00
-- url     : https://prove2.me/submissions/ca404629-8b76-4417-9e70-3cc37027ccd3

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L016
import Theorems.Thm_OAI_Laughlin_Fock_contractionForm_haar_s50
import Theorems.Thm_OAI_Laughlin_Rotation_embedded_spin_haar_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_RankOneHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_outer {I : Type*} [Fintype I] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (v : I → ℂ) (x : Space Q) :
    contractionForm Q minus (complexOuter v v) x =
      (occupationNormSq Q (∑ i, star (v i) • minus i x) : ℂ) := by
  rw [← occupationInner_self]
  simp only [occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,contractionForm,complexOuter,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrix_sandwich_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (W : Matrix I J ℂ) (p : J) :
    W*diagonalUnit p*Wᴴ =
      complexOuter (fun i => W i p) (fun i => W i p) := by
  ext i j
  simp [diagonalUnit,Matrix.mul_apply,complexOuter,Matrix.conjTranspose_apply,ite_and]

theorem physical_family_spin_norm_haar_s50_oai {I : Type*} [Fintype I] [DecidableEq I]
    (Q : ℕ) (ρ : SourceSU2 →* Matrix I I ℂ)
    (hρ : ∀ g, ρ g⁻¹=(ρ g)ᴴ) (hc : ∀ i j, Continuous (fun g => ρ g i j))
    (minus : I → Module.End ℂ (Space Q))
    (hm : ∀ g i x, minus i (exteriorRotation Q g x) =
      ∑ j, ρ g i j • exteriorRotation Q g (minus j x))
    (m : ℕ) (W : Matrix I (Fin (m+1)) ℂ)
    (hW : ∀ g, ρ g*W=W*sourceSpinRepresentation m g)
    (p : Fin (m+1)) (x : Space Q) :
    ((m+1 : ℕ) : ℂ) * (∫ g,
      (occupationNormSq Q (∑ i, star (W i p) • minus i (exteriorRotation Q g⁻¹ x)) : ℂ)
        ∂sourceHaar) = contractionForm Q minus (W*Wᴴ) x := by
  let M : Matrix (Fin (m+1)) (Fin (m+1)) ℂ := fun i j => if i=p ∧ j=p then 1 else 0
  have h := contractionForm_haar_s50 Q ρ hρ hc minus hm (W*M*Wᴴ) x
  rw [embedded_spin_haar_s50 ρ hρ m W hW,contractionForm_smul] at h
  have ht : Matrix.trace M=1 := by simp [M,Matrix.trace,Matrix.diag]
  rw [ht] at h
  have he : W*M*Wᴴ=complexOuter (fun i => W i p) (fun i => W i p) := matrix_sandwich_single W p
  simp_rw [he,contractionForm_outer] at h
  rw [h]
  have hd : ((m+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp

end Laughlin.Fock

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50_oai.{u_1} := @OAI.Laughlin.Fock.physical_family_spin_norm_haar_s50_oai.{u_1}
