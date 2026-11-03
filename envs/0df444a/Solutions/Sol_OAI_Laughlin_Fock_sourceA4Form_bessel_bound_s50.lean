-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:49:12.628536+00:00
-- url     : https://prove2.me/submissions/e27ab560-8ae9-41e2-9a6a-df714560aa8b

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L020
import Definitions.Def_OAIQ050L021
import Theorems.Thm_OAI_Laughlin_Fock_fourPairEmbedding_contract_s50
import Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_retained_bessel_bound_s50
import Theorems.Thm_OAI_Laughlin_Spin_fourPairEmbedding_resolution_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_MatrixQuadratic
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TargetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix ComplexOrder

theorem castSpinColumns_mul_adjoint {I : Type*} (m n : ℕ) (h : m=n)
    (W : Matrix I (Fin (m+1)) ℂ) :
    castSpinColumns m n h W * (castSpinColumns m n h W)ᴴ = W*Wᴴ := by
  subst n
  rfl

theorem fourWedgeProjector_congr (Q r D E : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hA' : E-r ≤ 2*Q-2) (hB' : E-r ≤ genericCoupledWeight Q Q r) (h : D=E) :
    fourWedgeInclusion Q r D hr hA hB*(fourWedgeInclusion Q r D hr hA hB)ᴴ =
      fourWedgeInclusion Q r E hr hA' hB'*(fourWedgeInclusion Q r E hr hA' hB')ᴴ := by
  subst E
  rfl

theorem retainedFirst_projector (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ =
    fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega) *
      (fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega))ᴴ := by
  unfold retainedFourInclusion
  rw [castSpinColumns_mul_adjoint]
  rfl

theorem contractionForm_projector_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    0 ≤ (contractionForm Q L (W*Wᴴ) x).re :=
  occupation_matrix_quadratic_positive Q _ (Matrix.posSemidef_self_mul_conjTranspose W) _

theorem sum_fin_castLE_le (m n : ℕ) (hmn : m ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∑ i : Fin m, f (Fin.castLE hmn i)) ≤ ∑ i : Fin n, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image (Fin.castLE hmn), f i := by
      rw [Finset.sum_image]
      intro i hi j hj he
      exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i hi hnot => hf i)

theorem retainedFourTarget_le_full (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourTarget Q hQ x ≤
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
  let f (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q 1)+1)) : ℝ :=
    (contractionForm Q (sourceFourFamilyEnd Q)
      (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega) *
        (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega))ᴴ) x).re
  have hn : 23 ≤ min (2*Q-2) (genericCoupledWeight Q Q 1)+1 := by
    unfold genericCoupledWeight
    omega
  have hs := sum_fin_castLE_le 23 _ hn f (fun z => contractionForm_projector_nonneg Q _ _ x)
  have hl : (∑ d : Fin 23, f (Fin.castLE hn d)) = retainedFourTarget Q hQ x := by
    unfold retainedFourTarget
    apply Finset.sum_congr rfl
    intro d hd
    rw [retainedFirst_projector]
    dsimp only [f,Fin.val_castLE]
    exact congrArg (fun M => (contractionForm Q (sourceFourFamilyEnd Q) M x).re)
      (fourWedgeProjector_congr Q 1 (1+d.val) (d.val+1) (by omega)
        (by omega) (by unfold genericCoupledWeight; omega)
        (by omega) (by unfold genericCoupledWeight; omega) (Nat.add_comm 1 d.val))
  have hr : (∑ z, f z) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
    rw [fourPairTargetMatrix,fourPairEmbedding_resolution_s50,contractionForm_sum,Complex.re_sum]
  rwa [hl,hr] at hs

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PairTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix Kronecker

theorem contractionForm_factor_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    contractionForm Q L (W*Wᴴ) x =
      (∑ j, (occupationNormSq Q (∑ i, star (W i j) • L i x) : ℂ)) := by
  have h := occupation_matrix_quadratic_factor Q W (1 : Matrix J J ℂ) (fun i => L i x)
  rw [Matrix.mul_one] at h
  change (∑ a, ∑ b, (W*Wᴴ) a b * occupationInner Q (L a x) (L b x)) = _
  rw [← h]
  simp [Matrix.one_apply,occupationInner_self]

theorem fourPairTargetMatrix_Fock (Q : ℕ) (hQ : 1 ≤ Q) (x : Space Q) :
    (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q hQ) x).re =
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  rw [fourPairTargetMatrix,contractionForm_factor_one]
  simp only [Complex.re_sum,Complex.ofReal_re]
  have he : (∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
      occupationNormSq Q (∑ i, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x)) =
      ∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
        occupationNormSq Q (sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x)) :=
    Finset.sum_congr rfl (fun j hj => congrArg (occupationNormSq Q) (fourPairEmbedding_contract_s50 Q hQ j x))
  rw [he,Fintype.sum_prod_type]
  have hw : genericCoupledWeight Q Q 1=2*Q-2 := by unfold genericCoupledWeight; omega
  apply Finset.sum_congr rfl
  intro p hp
  exact Fintype.sum_equiv (finCongr (congrArg (fun m => m+1) hw)) _ _ (fun q => rfl)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_BesselAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators

theorem sourceA4Form_bessel_bound_s50_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤
      (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
      (1222*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := retainedFourTarget_le_full Q hQ x
  rw [fourPairTargetMatrix_Fock] at ht
  have hb := sourceA4Form_retained_bessel_bound_s50 Q hQ x
  linarith

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50_oai := @OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50_oai
