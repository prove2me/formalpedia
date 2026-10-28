-- Prove2me | solution 1 for OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:42:47.457799+00:00
-- url     : https://prove2.me/submissions/a890e654-2de6-4515-861d-314656e3467f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf009
import Definitions.Def_OAIQ15Sf011

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_CStarEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

universe u v w
open scoped ComplexOrder InnerProductSpace BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type u} [CStarAlgebra A] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

lemma norm_sum_mul_le (a b : ι → A) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt ‖∑ i, a i * star (a i)‖ *
      Real.sqrt ‖∑ i, star (b i) * b i‖ := by
  let x : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm (fun i => star (b i))
  let y : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm a
  have h := CStarModule.norm_inner_le (A:=A) (E:=C⋆ᵐᵒᵈ(A, ι → A)) (x:=x) (y:=y)
  simpa only [x,y,WithCStarModule.pi_inner,WithCStarModule.inner_def,
    WithCStarModule.pi_norm,WithCStarModule.equiv_symm_pi_apply,star_star,mul_comm] using h


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular



lemma action_freeGen (n : ℕ) : action (freeGen n) = Equiv.mulLeft (FreeGroup.of (n:ℤ)) := by
  induction n with
  | zero => simp [freeGen]
  | succ n ih =>
    ext w
    simp only [freeGen,map_mul,map_inv,action_a,ih,Equiv.Perm.mul_apply]
    change shift (FreeGroup.of (n:ℤ) * shift.symm w) = FreeGroup.of ((n+1:ℕ):ℤ) * w
    simp

lemma coordinate_freeGen_mul (n : ℕ) (w : F2) :
    coordinate (freeGen n * w) = FreeGroup.of (n:ℤ) * coordinate w := by
  simp [coordinate,action_freeGen]

lemma prefix_disjoint {i j : ℤ} {s t : Bool} {w : FZ}
    (h : Prefix i s w) (k : Prefix j t w) : i = j ∧ s = t := by
  rcases h with ⟨u,hu⟩; rcases k with ⟨v,hv⟩
  simpa using (List.cons.inj (hu.symm.trans hv)).1

lemma prefix_mul_of_not_negative (i : ℤ) (w : FZ) (h : ¬ Prefix i false w) :
    Prefix i true (FreeGroup.of i * w) := by
  unfold Prefix at *
  rw [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.singleton_append,FreeGroup.reduce.cons,
    FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => exact ⟨[],rfl⟩
  | cons z t =>
    rcases z with ⟨j,s⟩
    have hn : ¬ (i = j ∧ true = !s) := by
      rintro ⟨rfl,hs⟩
      cases s with
      | false => exact h ⟨t,hw⟩
      | true => simp at hs
    simp only [hn,ite_false]
    exact ⟨(j,s)::t,rfl⟩

lemma positive_of_not_negative_inverse (n : ℕ) (w : F2)
    (h : ¬ Prefix (n:ℤ) false (coordinate ((freeGen n)⁻¹ * w))) :
    Prefix (n:ℤ) true (coordinate w) := by
  have he := coordinate_freeGen_mul n ((freeGen n)⁻¹ * w)
  simp only [mul_inv_cancel_left] at he
  rw [he]
  exact prefix_mul_of_not_negative _ _ h


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [Group G] [CompleteSpace H] in
lemma diagonal_norm_le (T : H →L[ℂ] H) : ‖diagonal (G:=G) T‖ ≤ ‖T‖ :=
  lp.norm_mapCLM_le _ _ _ _

omit [CompleteSpace H] in
lemma diagonal_left_commute (T : H →L[ℂ] H) (g : G) :
    Commute (diagonal T) (left g) := by ext; rfl

omit [Group G] [CompleteSpace H] in
lemma diagonal_mask_commute (T : H →L[ℂ] H) (P : G → Prop) [DecidablePred P] :
    Commute (diagonal T) (mask P) := by
  ext x g
  simp only [mul_apply_eq_comp,mask_apply,diagonal_apply]
  split_ifs <;> simp

omit [CompleteSpace H] in
lemma left_split (n : ℕ) : left (H:=H) (freeGen n) = creation n + annihilation n := by
  simp [creation,annihilation,mul_sub]

omit [CompleteSpace H] in
lemma creation_support (n : ℕ) (x : HilbertSum F2 H) (w : F2)
    (h : ¬ Prefix (n:ℤ) true (coordinate w)) : creation n x w = 0 := by
  classical
  rw [creation_apply,ite_eq_left]
  exact not_not.mp (h ∘ positive_of_not_negative_inverse n w)

lemma creation_orthogonal {m n : ℕ} (h : m ≠ n) :
    star (creation (H:=H) m) * creation n = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ext_inner_left ℂ)
  intro y
  change inner ℂ y ((creation m).adjoint (creation n x)) = inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right,lp.inner_eq_tsum]
  rw [← (tsum_zero : (∑' _ : F2, (0 : ℂ)) = 0)]
  apply tsum_congr
  intro w
  by_cases hm : Prefix (m:ℤ) true (coordinate w)
  · have hn : ¬ Prefix (n:ℤ) true (coordinate w) := by
      intro hn
      exact h (Int.ofNat_inj.mp (prefix_disjoint hm hn).1)
    rw [creation_support n x w hn,inner_zero_right]
  · rw [creation_support m y w hm,inner_zero_left]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_FreeEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma norm_disjoint_sum_le {E : Type*} [NormedAddCommGroup E] (T : ι → E) (P : ι → Prop)
    (hd : ∀ i j, P i → P j → i = j) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, if P i then T i else 0‖ ≤ c := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i,hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simpa [hi] using hT i
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (hd j i hj hi))
    · simp
  · simp only [not_exists] at h
    simpa [h] using hc

omit [CompleteSpace H] in
lemma cutSum_norm_le (e : ι → ℕ) (he : Function.Injective e)
    (T : ι → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, diagonal (T i) * negative (e i)‖ ≤ c := by
  classical
  let U (w : F2) : H →L[ℂ] H :=
    ∑ i, if Prefix (e i:ℤ) false (coordinate w) then T i else 0
  have hU (w : F2) : ‖U w‖ ≤ c := by
    apply norm_disjoint_sum_le _ _ _ hc hT
    intro i j hi hj
    exact he (Int.ofNat_inj.mp (prefix_disjoint hi hj).1)
  have heq : (∑ i, diagonal (T i) * negative (e i)) = lp.mapCLM 2 U hc hU := by
    ext x w
    change _ = (U w) (x w)
    simp only [sum_apply,lp.coeFn_sum,Finset.sum_apply]
    simp only [mul_apply_eq_comp,diagonal_apply,negative,mask_apply,U,sum_apply]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> simp
  rw [heq]
  exact lp.norm_mapCLM_le _ _ _ _

omit [CompleteSpace H] in
lemma sum_negative_norm_le (e : ι → ℕ) (he : Function.Injective e) :
    ‖∑ i, negative (H:=H) (e i)‖ ≤ 1 := by
  have h := cutSum_norm_le e he (fun _ => (1 : H →L[ℂ] H)) (by norm_num)
    (fun _ => ContinuousLinearMap.norm_id_le)
  simpa using h

omit [CompleteSpace H] in
lemma diagonal_creation_commute (T : H →L[ℂ] H) (n : ℕ) :
    Commute (diagonal T) (creation n) :=
  (diagonal_left_commute T _).mul_right
    ((Commute.one_right _).sub_right (diagonal_mask_commute T _))

lemma diagonal_starCreation_commute (T : H →L[ℂ] H) (n : ℕ) :
    Commute (diagonal T) (star (creation (H := H) n)) := by
  have h := (diagonal_creation_commute (star T) n).star_star
  simpa only [← diagonal_star,star_star] using h

lemma coeff_creation_star_mul (T S : H →L[ℂ] H) (m n : ℕ) :
    star (diagonal T * creation m) * (diagonal S * creation n) =
      diagonal (star T*S) * (star (creation (H := H) m) * creation n) := by
  simp only [star_mul,← diagonal_star,mul_assoc]
  rw [← mul_assoc (diagonal (star T)),← diagonal_mul,
    ← mul_assoc (star (creation (H := H) m)),(diagonal_starCreation_commute (star T*S) m).symm.eq,mul_assoc]

lemma creationSum_star_mul (e f : ι → ℕ) (T : ι → H →L[ℂ] H) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (f j)) =
      ∑ i, ∑ j, diagonal (star (T i)*T j)*(star (creation (H := H) (e i))*creation (f j)) := by
  rw [star_sum (R := HilbertSum F2 H →L[ℂ] HilbertSum F2 H)
    Finset.univ (fun index => diagonal (T index) * creation (e index))]
  simp only [Finset.sum_mul,Finset.mul_sum,coeff_creation_star_mul]
  rw [Finset.sum_comm]

lemma creationSum_gram_self (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hT : ∑ i, star (T i)*T i = 1) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (e j)) =
      1 - ∑ i, diagonal (star (T i)*T i)*negative (e i) := by
  classical
  rw [creationSum_star_mul]
  have hs (i : ι) : (∑ j, diagonal (star (T i)*T j)*(star (creation (H := H) (e i))*creation (e j))) =
      diagonal (star (T i)*T i)*(1-negative (e i)) := by
    rw [Finset.sum_eq_single i,creation_star_mul_self]
    · intro j _ hji
      rw [creation_orthogonal (fun h => hji (he h).symm),mul_zero]
    · simp
  simp_rw [hs,mul_sub,mul_one]
  rw [Finset.sum_sub_distrib]
  congr 1
  change (∑ i, diagonalHom (G:=F2) (H:=H) (star (T i)*T i)) = 1
  rw [← map_sum,hT,map_one]

lemma creationSum_gram_cross (e f : ι → ℕ) (hef : ∀ i j, e i ≠ f j) (T : ι → H →L[ℂ] H) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (f j)) = 0 := by
  rw [creationSum_star_mul]
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  rw [creation_orthogonal (hef i j),mul_zero]


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_NearGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder CStarAlgebra BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

lemma matrix_norm_le_sum {m n : Type*} [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  refine (CStarMatrix.toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [CStarMatrix.toCLM_apply_eq_sum,Finset.sum_mul]
  apply WithCStarModule.pi_norm_le_sum_norm _ |>.trans
  gcongr with i _
  apply norm_sum_le _ _ |>.trans
  gcongr with j _
  apply norm_mul_le _ _ |>.trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

lemma two_isometries_of_near_gram (x : Fin 2 → A)
    (h : ∀ i j, ‖star (x i)*x j - (if i=j then 1 else 0)‖ ≤ (1/16:ℝ)) :
    ∃ s t : A, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin 2) (Fin 2) A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (Fin 2) (Fin 2) A) :=
    CStarAlgebra.instNonnegSpectrumClass
  let X : CStarMatrix (Fin 2) (Fin 2) A :=
    CStarMatrix.ofMatrix fun i j => if i=0 then x j else 0
  let Q := star X * X
  have hQ (i j : Fin 2) : Q i j = star (x i)*x j := by
    change (∑ k : Fin 2, star (X k i) * X k j) = star (x i) * x j
    rw [Fin.sum_univ_two]
    change star (x i) * x j + star (0 : A) * 0 = star (x i) * x j
    simp
  have hb : ‖1-Q‖ ≤ (1/4:ℝ) := by
    apply (matrix_norm_le_sum (1-Q)).trans
    calc
      _ ≤ ∑ _ : Fin 2, ∑ _ : Fin 2, (1/16:ℝ) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro i _
        simpa only [CStarMatrix.sub_apply,CStarMatrix.one_apply,hQ,norm_sub_rev] using h i j
      _ = 1/4 := by norm_num
  have hu : IsUnit Q := by
    have hu := (Units.oneSub (1-Q) (hb.trans_lt (by norm_num))).isUnit
    simpa only [Units.val_oneSub,sub_sub_cancel] using hu
  have hpos : IsStrictlyPositive Q := hu.isStrictlyPositive (star_mul_self_nonneg X)
  let L := Q ^ (-(1/2):ℝ)
  have hL : star L = L := (CFC.rpow_nonneg (a:=Q) (y:=(-(1/2):ℝ))).isSelfAdjoint.star_eq
  let Y := X * L
  have hYY : star Y * Y = 1 := by
    calc
      _ = L * Q * L := by simp only [Y,star_mul,hL,Q,mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half Q hpos
  have hzero (j : Fin 2) : Y 1 j = 0 := by
    change (∑ k : Fin 2, X 1 k * L k j) = 0
    rw [Fin.sum_univ_two]
    change (0 : A) * L 0 j + 0 * L 1 j = 0
    simp
  have he (i j : Fin 2) : star (Y 0 i)*Y 0 j = if i=j then 1 else 0 := by
    have hh := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M i j) hYY
    simpa [CStarMatrix.mul_apply,CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply,Fin.sum_univ_two,hzero,CStarMatrix.one_apply] using hh
  exact ⟨Y 0 0,Y 0 1,by simpa using he 0 0,by simpa using he 1 1,by simpa using he 0 1⟩


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_SlotEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma small_row_norm (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, T i*star (T i)‖ ≤ (1/10000:ℝ) := by
  apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg hr
    (Finset.sum_nonneg fun index _ => mul_star_self_nonneg (T index))).trans
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 1/10000)]
  exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by norm_num)).trans_eq (mul_one _)

lemma small_entry_gram_norm (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) (i : ι) :
    ‖star (T i)*T i‖ ≤ (1/10000:ℝ) := by
  rw [CStarRing.norm_star_mul_self,← CStarRing.norm_self_mul_star]
  apply (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (Finset.single_le_sum (fun index _ => mul_star_self_nonneg (T index)) (Finset.mem_univ i))
    (mul_star_self_nonneg _)).trans
  exact small_row_norm T hr

lemma creationSum_small_defect (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (e j)) - 1‖
      ≤ (1/10000:ℝ) := by
  rw [creationSum_gram_self e he T hc]
  have hid (z : HilbertSum F2 H →L[ℂ] HilbertSum F2 H) : 1-z-1 = -z := by abel
  rw [hid,norm_neg]
  exact cutSum_norm_le e he _ (by norm_num) (small_entry_gram_norm T hr)

lemma creationSum_norm_le_two (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, diagonal (T i)*creation (e i)‖ ≤ 2 := by
  let C := ∑ i, diagonal (T i)*creation (e i)
  have hd : ‖star C*C-1‖ ≤ (1/10000:ℝ) := creationSum_small_defect e he T hc hr
  have hnorm : ‖star C*C‖ ≤ (1/10000:ℝ)+1 := by
    calc
      _ = ‖(star C*C-1)+1‖ := by rw [sub_add_cancel]
      _ ≤ ‖star C*C-1‖+‖(1 : HilbertSum F2 H →L[ℂ] HilbertSum F2 H)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hd ContinuousLinearMap.norm_id_le
  rw [CStarRing.norm_star_mul_self (x := C)] at hnorm
  change ‖C‖ ≤ 2
  nlinarith [norm_nonneg C]

lemma annihilationSum_norm_le (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ‖∑ i, diagonal (T i)*annihilation (e i)‖ ≤ (1/100:ℝ) := by
  have hrow : ‖∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))‖ ≤ (1/10000:ℝ) := by
    have heq : (∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))) =
        diagonal (∑ i, T i*star (T i)) := by
      simp only [← diagonal_star,← diagonal_mul]
      exact (map_sum (diagonalHom (G:=F2) (H:=H)) _ _).symm
    rw [heq]
    exact (diagonal_norm_le _).trans (small_row_norm T hr)
  have hcol : ‖∑ i, star (annihilation (H:=H) (e i))*annihilation (e i)‖ ≤ 1 := by
    simp only [annihilation_star_mul_self]
    exact sum_negative_norm_le e he
  calc
    _ ≤ Real.sqrt ‖∑ i, diagonal (G:=F2) (T i)*star (diagonal (T i))‖ *
        Real.sqrt ‖∑ i, star (annihilation (H:=H) (e i))*annihilation (e i)‖ :=
      norm_sum_mul_le _ _
    _ ≤ Real.sqrt (1/10000:ℝ) * Real.sqrt 1 := by gcongr
    _ = 1/100 := by
      have hsqrt : Real.sqrt (10000 : ℝ) = 100 :=
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
      norm_num [Real.sqrt_div, hsqrt]

lemma small_gram_perturbation {A : Type*} [CStarAlgebra A] (T U S V δ : A)
    (hT : ‖T‖ ≤ 2) (hU : ‖U‖ ≤ 2) (hS : ‖S‖ ≤ (1/100:ℝ)) (hV : ‖V‖ ≤ (1/100:ℝ))
    (hδ : ‖star T*U-δ‖ ≤ (1/10000:ℝ)) :
    ‖star (T+S)*(U+V)-δ‖ ≤ (1/16:ℝ) := by
  have hid : star (T+S)*(U+V)-δ = (star T*U-δ) + star T*V + star S*U + star S*V := by
    simp only [star_add]; noncomm_ring
  rw [hid]
  calc
    _ ≤ ((‖star T*U-δ‖ + ‖T‖*‖V‖) + ‖S‖*‖U‖) + ‖S‖*‖V‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · apply (norm_add_le _ _).trans
          exact add_le_add le_rfl (by simpa only [norm_star] using norm_mul_le (star T) V)
        · simpa only [norm_star] using norm_mul_le (star S) U
      · simpa only [norm_star] using norm_mul_le (star S) V
    _ ≤ ((1/10000 + 2*(1/100:ℝ)) + (1/100)*2) + (1/100)*(1/100) := by gcongr
    _ ≤ 1/16 := by norm_num

lemma free_rows_near_gram (e : Fin 2 × ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hc : ∑ i, star (T i)*T i = 1)
    (hr : ∑ i, T i*star (T i) ≤ (1/10000:ℝ) • 1) :
    ∀ r s : Fin 2,
      ‖star (∑ i, diagonal (T i)*left (freeGen (e (r,i)))) *
        (∑ j, diagonal (T j)*left (freeGen (e (s,j)))) - (if r=s then 1 else 0)‖ ≤ (1/16:ℝ) := by
  intro r s
  have hei (r : Fin 2) : Function.Injective (fun i => e (r,i)) := by
    intro i j hij
    exact (Prod.mk.inj (he hij)).2
  let C (r : Fin 2) := ∑ i, diagonal (T i)*creation (e (r,i))
  let D (r : Fin 2) := ∑ i, diagonal (T i)*annihilation (e (r,i))
  have hsplit (r : Fin 2) : (∑ i, diagonal (T i)*left (freeGen (e (r,i)))) = C r+D r := by
    simp only [left_split,mul_add,Finset.sum_add_distrib,C,D]
  rw [hsplit,hsplit]
  apply small_gram_perturbation
  · exact creationSum_norm_le_two _ (hei r) T hc hr
  · exact creationSum_norm_le_two _ (hei s) T hc hr
  · exact annihilationSum_norm_le _ (hei r) T hr
  · exact annihilationSum_norm_le _ (hei s) T hr
  · by_cases hrs : r=s
    · subst s
      simpa only [C,ite_true] using creationSum_small_defect _ (hei r) T hc hr
    · rw [ite_eq_right hrs]
      have hh : star (C r)*C s = 0 := creationSum_gram_cross _ _ (fun i j hij => hrs (Prod.mk.inj (he hij)).1) T
      rw [hh,sub_zero,norm_zero]
      norm_num


end KaplanskyConsequences.Regular

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Regular_ReducedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensor_two_isometries_of_small_tuple_oai (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (a : ι → A)
    (hc : ∑ i, star (a i)*a i = 1)
    (hr : ∑ i, a i*star (a i) ≤ (1/10000:ℝ) • (1:A)) :
    ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  let e : Fin 2 × ι → ℕ := fun p => (Fintype.equivFin (Fin 2 × ι) p).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin _).injective
  let x (r : Fin 2) : tensorAlgebra (G:=F2) ρ :=
    ∑ i, tensorCoeff ρ (a i) * tensorGroup ρ (freeGen (e (r,i)))
  apply two_isometries_of_near_gram x
  have hc' : ∑ i, star (ρ (a i))*ρ (a i) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ρ hc
  have hr' : ∑ i, ρ (a i)*star (ρ (a i)) ≤ (1/10000:ℝ) • (1 : H →L[ℂ] H) := by
    have h := map_rel ρ hr
    have hs : ρ ((1/10000:ℝ) • (1:A)) = (1/10000:ℝ) • (1 : H →L[ℂ] H) :=
      (ρ.toAlgHom.map_smul_of_tower (1/10000:ℝ) (1:A)).trans (by rw [map_one])
    rw [hs] at h
    simpa only [map_sum,map_mul,map_star] using h
  intro r s
  have h := free_rows_near_gram e he (fun i => ρ (a i)) hc' hr' r s
  change ‖(tensorAlgebra (G:=F2) ρ).subtype (star (x r)*x s - (if r=s then 1 else 0))‖ ≤ _
  by_cases hrs : r=s
  all_goals
    simp only [hrs,↓reduceIte,map_sub,map_mul,map_star,map_one,map_zero,x,map_sum] at h ⊢
    exact h


end KaplanskyConsequences.Regular

end

end OAI
end

theorem solution.{u_1, u_3, u_4} : type_of% @OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple_oai.{u_1, u_3, u_4} := @OAI.KaplanskyConsequences.Regular.tensor_two_isometries_of_small_tuple_oai.{u_1, u_3, u_4}
