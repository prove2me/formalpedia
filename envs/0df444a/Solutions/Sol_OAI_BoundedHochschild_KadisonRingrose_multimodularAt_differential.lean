-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.multimodularAt_differential
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:06:05.475466+00:00
-- url     : https://prove2.me/submissions/de84b469-3b98-4e86-9d22-b53ebe46d5b8

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma mergeInputs_left_module {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x 0 (r * x 0)) k =
      Function.update (mergeInputs x k) 0 (r * mergeInputs x k 0) := by
  ext i
  by_cases hi : i = 0
  · subst i
    by_cases hk : k = 0
    · subst k
      simp [mergeInputs, mul_assoc]
    · have hkpos : (0 : Fin (n + 1)) < k := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hk)
      simp [mergeInputs, hkpos]
  · have his : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h
      exact hi (Fin.ext (congrArg (fun j : Fin (n + 2) => j.val) h))
    simp only [mergeInputs, Function.update_of_ne hi, Function.update_of_ne his,
      Function.update_of_ne (Fin.succ_ne_zero i)]

lemma mergeInputs_right_module {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x (Fin.last (n + 1)) (x (Fin.last (n + 1)) * r)) k =
      Function.update (mergeInputs x k) (Fin.last n) (mergeInputs x k (Fin.last n) * r) := by
  ext i
  by_cases hi : i = Fin.last n
  · subst i
    by_cases hk : k = Fin.last n
    · subst k
      simp [mergeInputs, mul_assoc]
    · have hklt : k < Fin.last n := lt_of_le_of_ne (Fin.le_last _) hk
      simp [mergeInputs, not_lt_of_ge (Fin.le_last k), Ne.symm hk]
  · have his : i.succ ≠ Fin.last (n + 1) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    simp only [mergeInputs, Function.update_of_ne hi,
      Function.update_of_ne (ne_of_lt (Fin.castSucc_lt_last i)), Function.update_of_ne his]

lemma mergeInputs_balance_at {n : ℕ} (x : Fin (n + 2) → M) (k : Fin (n + 1)) (r : M) :
    mergeInputs (Function.update x k.castSucc (x k.castSucc * r)) k =
      mergeInputs (Function.update x k.succ (r * x k.succ)) k := by
  ext i
  by_cases hik : i = k
  · subst i
    simp [mergeInputs, ne_of_lt (Fin.castSucc_lt_succ (i := k)),
      ne_of_gt (Fin.castSucc_lt_succ (i := k)), mul_assoc]
  · by_cases hlt : i < k
    · have hic : i.castSucc ≠ k.castSucc := by simpa using hik
      have his : i.castSucc ≠ k.succ := ne_of_lt (lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hlt)
        Fin.castSucc_lt_succ)
      simp only [mergeInputs, ite_eq_left hlt, Function.update_of_ne hic, Function.update_of_ne his]
    · have his : i.succ ≠ k.succ := by simpa using hik
      have hic : i.succ ≠ k.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_castSucc] at hv
        have hv' : k.val ≤ i.val := le_of_not_gt hlt
        omega
      simp only [mergeInputs, ite_eq_right hlt, ite_eq_right hik, Function.update_of_ne his, Function.update_of_ne hic]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma merge_balance_before_left {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : k.val < j.val) (hp : p.val + 1 = j.val) (r : M) :
    mergeInputs (Function.update x j.castSucc (x j.castSucc * r)) k =
      Function.update (mergeInputs x k) p.castSucc (mergeInputs x k p.castSucc * r) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  all_goals try simp only [mul_assoc]
  all_goals congr 3 <;> (try apply Fin.ext) <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

lemma merge_balance_before_right {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : k.val < j.val) (hp : p.val + 1 = j.val) (r : M) :
    mergeInputs (Function.update x j.succ (r * x j.succ)) k =
      Function.update (mergeInputs x k) p.succ (r * mergeInputs x k p.succ) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  congr 3
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

lemma merge_balance_after_left {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : j.val < k.val) (hp : p.val = j.val) (r : M) :
    mergeInputs (Function.update x j.castSucc (x j.castSucc * r)) k =
      Function.update (mergeInputs x k) p.castSucc (mergeInputs x k p.castSucc * r) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  congr 3
  apply Fin.ext
  simp only [Fin.val_castSucc]
  omega

lemma merge_balance_after_right {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : j.val < k.val) (hp : p.val = j.val) (r : M) :
    mergeInputs (Function.update x j.succ (r * x j.succ)) k =
      Function.update (mergeInputs x k) p.succ (r * mergeInputs x k p.succ) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  all_goals try simp only [mul_assoc]
  all_goals congr 3 <;> (try apply Fin.ext) <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma MultimodularAt.add {n : ℕ} {f g : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (hg : MultimodularAt g r) : MultimodularAt (f + g) r := by
  constructor
  · intro x
    simp only [add_apply, hf.left, hg.left, mul_add]
  · intro x
    simp only [add_apply, hf.right, hg.right, add_mul]
  · intro x j
    simp only [add_apply, hf.balance x j, hg.balance x j]

lemma MultimodularAt.smul {n : ℕ} {f : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (z : ℂ) : MultimodularAt (z • f) r := by
  constructor
  · intro x
    simp only [smul_apply, hf.left, mul_smul_comm]
  · intro x
    simp only [smul_apply, hf.right, smul_mul_assoc]
  · intro x j
    simp only [smul_apply, hf.balance x j]

lemma MultimodularAt.zero {n : ℕ} (r : M) : MultimodularAt (0 : Cochain M (n + 1)) r := by
  constructor <;> intros <;> simp

lemma MultimodularAt.sum {I : Type*} {n : ℕ} (s : Finset I) (f : I → Cochain M (n + 1)) (r : M)
    (hf : ∀ i ∈ s, MultimodularAt (f i) r) : MultimodularAt (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MultimodularAt.zero (n := n) r
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma multimodularAt_middleCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) (k : Fin (n + 1)) : MultimodularAt (middleCoboundary f k) r := by
  constructor
  · intro x
    simp only [middleCoboundary_apply, mergeInputs_left_module]
    exact hf.left _
  · intro x
    simp only [middleCoboundary_apply, mergeInputs_right_module]
    exact hf.right _
  · intro x j
    simp only [middleCoboundary_apply]
    by_cases hkj : k = j
    · subst k
      rw [mergeInputs_balance_at]
    · rcases lt_or_gt_of_ne hkj with hk | hk
      · let p : Fin n := ⟨j.val - 1, by omega⟩
        have hp : p.val + 1 = j.val := by dsimp [p]; omega
        rw [merge_balance_before_left x k j p hk hp,
          merge_balance_before_right x k j p hk hp]
        exact hf.balance _ p
      · let p : Fin n := ⟨j.val, by omega⟩
        have hp : p.val = j.val := rfl
        rw [merge_balance_after_left x k j p hk hp,
          merge_balance_after_right x k j p hk hp]
        exact hf.balance _ p
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

omit [CStarAlgebra M] in
private lemma tail_update_zero {n : ℕ} (x : Fin (n + 1) → M) (a : M) :
    (fun i : Fin n => Function.update x 0 a i.succ) = (fun i => x i.succ) := by
  ext i
  simp

omit [CStarAlgebra M] in
private lemma tail_update_succ {n : ℕ} (x : Fin (n + 1) → M) (k : Fin n) (a : M) :
    (fun i : Fin n => Function.update x k.succ a i.succ) =
      Function.update (fun i => x i.succ) k a := by
  ext i
  by_cases hi : i = k <;> simp [hi]

omit [CStarAlgebra M] in
private lemma init_update_last {n : ℕ} (x : Fin (n + 1) → M) (a : M) :
    (fun i : Fin n => Function.update x (Fin.last n) a i.castSucc) = (fun i => x i.castSucc) := by
  ext i
  exact Function.update_of_ne (ne_of_lt (Fin.castSucc_lt_last i)) a x

omit [CStarAlgebra M] in
private lemma init_update_castSucc {n : ℕ} (x : Fin (n + 1) → M) (k : Fin n) (a : M) :
    (fun i : Fin n => Function.update x k.castSucc a i.castSucc) =
      Function.update (fun i => x i.castSucc) k a := by
  ext i
  by_cases hi : i = k <;> simp [hi]

lemma multimodularAt_leftCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (leftCoboundary f) r := by
  constructor
  · intro x
    simp only [leftCoboundary_apply, Function.update_self, tail_update_zero, mul_assoc]
  · intro x
    have hlast : Fin.last (n + 1) = (Fin.last n).succ := rfl
    simp only [leftCoboundary_apply, hlast, tail_update_succ,
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero (Fin.last n)))]
    rw [hf.right]
    exact (mul_assoc _ _ _).symm
  · intro x j
    by_cases hj : j = 0
    · subst j
      simp only [leftCoboundary_apply, Fin.castSucc_zero, Function.update_self,
        tail_update_zero, tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero (0 : Fin (n + 1))))]
      rw [hf.left]
      exact mul_assoc _ _ _
    · obtain ⟨p, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      simp only [leftCoboundary_apply, Fin.castSucc_succ, tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero p.castSucc)),
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero p.succ))]
      rw [hf.balance]

lemma multimodularAt_rightCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (rightCoboundary f) r := by
  constructor
  · intro x
    have hzero : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    simp only [rightCoboundary_apply, hzero, init_update_castSucc,
      Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last (0 : Fin (n + 1)))))]
    rw [hf.left]
    exact mul_assoc _ _ _
  · intro x
    simp only [rightCoboundary_apply, Function.update_self, init_update_last, mul_assoc]
  · intro x j
    by_cases hj : j = Fin.last n
    · subst j
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      simp only [rightCoboundary_apply, hlast, init_update_castSucc,
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last (Fin.last n)))),
        init_update_last, Function.update_self]
      rw [hf.right]
      exact mul_assoc _ _ _
    · obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      simp only [rightCoboundary_apply, ← Fin.castSucc_succ, init_update_castSucc,
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last p.castSucc))),
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last p.succ)))]
      rw [hf.balance]

lemma multimodularAt_differential {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (differential f) r := by
  change MultimodularAt
    (leftCoboundary f + ∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary f) r
  exact ((multimodularAt_leftCoboundary f r hf).add
    (MultimodularAt.sum Finset.univ _ r (fun j _ =>
      (multimodularAt_middleCoboundary f r hf j).smul _))).add
    ((multimodularAt_rightCoboundary f r hf).smul _)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u_1} : type_of% @OAI.BoundedHochschild.KadisonRingrose.multimodularAt_differential.{u_1} := @OAI.BoundedHochschild.KadisonRingrose.multimodularAt_differential.{u_1}
