-- Prove2me | solution 1 for MatousekLP.Codes.delsarte_psd
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:29:04.151284+00:00
-- url     : https://prove2.me/submissions/c6c0b04e-b3a9-45e8-85d0-2c52a4527991

import Definitions.Def_MatousekLP_Codes_BoseMesner
import Definitions.Def_MatousekLP_Codes_DelsarteLP

open Finset Polynomial MatousekLP.Codes

-- Reuse the character helpers from the Krawtchouk inequality solution.
-- Copy their proofs, as importing that module would also import its global `solution`.
namespace KrawAux

/-- Coefficients of `(1 - X)^i`. -/
lemma coeff_one_sub_X_pow (i a : ℕ) :
    ((1 - X : ℤ[X]) ^ i).coeff a = (-1 : ℤ) ^ a * (i.choose a : ℤ) := by
  have h : (1 - X : ℤ[X]) ^ i = (C (-1 : ℤ)) ^ i * (X + C (-1 : ℤ)) ^ i := by
    rw [← mul_pow]; congr 1; simp; ring
  rw [h, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  by_cases ha : a ≤ i
  · rw [← mul_assoc, ← pow_add]
    have : i + (i - a) = 2 * (i - a) + a := by omega
    rw [this, pow_add, pow_mul]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma coeff_one_add_X_pow' (k b : ℕ) :
    ((1 + X : ℤ[X]) ^ k).coeff b = (k.choose b : ℤ) := by
  rw [add_comm, ← C_1, coeff_X_add_C_pow]; simp

/-- Character sum over subsets of size `t`: `∑_{|T|=t} (-1)^{|T ∩ U|} = K n t |U|`. -/
theorem char_sum (n t : ℕ) (U : Finset (Fin n)) :
    ∑ T ∈ powersetCard t (univ : Finset (Fin n)), (-1 : ℤ) ^ (T ∩ U).card = K n t U.card := by
  classical
  set c : Fin n → ℤ[X] := fun j => if j ∈ U then -X else X
  -- product form
  have hprod : ∏ j, (1 + c j) = (1 - X) ^ U.card * (1 + X) ^ (n - U.card) := by
    have : (fun j => 1 + c j) = fun j => if j ∈ U then (1 - X : ℤ[X]) else 1 + X := by
      funext j; by_cases h : j ∈ U <;> simp [c, h, sub_eq_add_neg]
    rw [this, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · simp
    · rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_sdiff,
        Fintype.card_fin]
  -- subset expansion
  have hterm : ∀ T : Finset (Fin n), ∏ j ∈ T, c j = C ((-1 : ℤ) ^ (T ∩ U).card) * X ^ T.card := by
    intro T
    have : ∀ j, c j = C (if j ∈ U then (-1 : ℤ) else 1) * X := by
      intro j; by_cases h : j ∈ U <;> simp [c, h]
    simp_rw [this, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
    congr 2
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      Finset.filter_mem_eq_inter]
  have hexp : ∏ j, (1 + c j) = ∑ T ∈ (univ : Finset (Fin n)).powerset,
      C ((-1 : ℤ) ^ (T ∩ U).card) * X ^ T.card := by
    rw [Finset.prod_one_add]; exact Finset.sum_congr rfl fun T _ => hterm T
  -- compare coefficients of X^t
  have hL : (∏ j, (1 + c j)).coeff t = ∑ T ∈ powersetCard t (univ : Finset (Fin n)),
      (-1 : ℤ) ^ (T ∩ U).card := by
    rw [hexp, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun T _ => by split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
  rw [← hL, hprod, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow, coeff_one_add_X_pow']
  unfold K
  -- both sides sum over `j ≤ min |U| t`; extra terms vanish
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (min_le_right U.card t)))]
  intro j hj hj'
  simp only [Finset.mem_range] at hj hj'
  have : U.card < j := by omega
  rw [Nat.choose_eq_zero_of_lt this]; simp

end KrawAux

namespace KrawAux2

open Finset MatousekLP.Codes

/-- The sign of `w` on the positions of `T`. -/
def sgn {n : ℕ} (T : Finset (Fin n)) (w : Word n) : ℤ := ∏ j ∈ T, if w j = true then (-1 : ℤ) else 1

lemma neg_one_pow_card_filter {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (-1 : ℤ) ^ (s.filter p).card = ∏ j ∈ s, if p j then (-1 : ℤ) else 1 := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

lemma sign_pair {n : ℕ} (T : Finset (Fin n)) (w w' : Word n) :
    (-1 : ℤ) ^ (T ∩ univ.filter fun j => w j ≠ w' j).card = sgn T w * sgn T w' := by
  classical
  rw [Finset.inter_filter, Finset.inter_univ, neg_one_pow_card_filter, sgn, sgn,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  cases w j <;> cases w' j <;> simp

end KrawAux2


namespace DelsartePSDAux

private def chi {n : ℕ} (T : Finset (Fin n)) (w : Word n) : ℝ :=
  (KrawAux2.sgn T w : ℝ)

private def word {n : ℕ} (U : Finset (Fin n)) : Word n := fun j => decide (j ∈ U)

private lemma chi_word {n : ℕ} (T U : Finset (Fin n)) :
    chi T (word U) = ((-1 : ℤ) ^ (T ∩ U).card : ℝ) := by
  classical
  unfold chi KrawAux2.sgn word
  rw [← KrawAux2.neg_one_pow_card_filter]
  have hf : T.filter (fun j => decide (j ∈ U) = true) = T ∩ U := by
    ext j
    simp
  rw [hf]
  norm_cast

private lemma orthogonal {n : ℕ} (v w : Word n) :
    ∑ T : Finset (Fin n), chi T v * chi T w = if v = w then (2 : ℝ)^n else 0 := by
  classical
  have hprod : ∑ T : Finset (Fin n), chi T v * chi T w =
      ∏ j : Fin n, (1 + (if v j then (-1 : ℝ) else 1) * (if w j then (-1 : ℝ) else 1)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro T _
    simp only [chi, KrawAux2.sgn, Int.cast_prod, Int.cast_ite, Int.cast_neg, Int.cast_one]
    rw [← Finset.prod_mul_distrib]
  rw [hprod]
  by_cases h : v = w
  · subst w
    simp only [ite_true]
    have : ∀ j, 1 + (if v j then (-1 : ℝ) else 1) * (if v j then (-1 : ℝ) else 1) = 2 := by
      intro j; cases v j <;> norm_num
    simp_rw [this]
    simp
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ w j := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases hv : v j <;> cases hw : w j <;> simp_all

private lemma inverse {n : ℕ} (i : ℕ) (v w : Word n) :
    ∑ T : Finset (Fin n), (K n i T.card : ℝ) * chi T v * chi T w =
      (2 : ℝ)^n * distMatrix n i v w := by
  classical
  have hk (T : Finset (Fin n)) : (K n i T.card : ℝ) =
      ∑ U ∈ powersetCard i (univ : Finset (Fin n)), chi T (word U) := by
    rw [← KrawAux.char_sum n i T, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro U _
    rw [chi_word, inter_comm]
    norm_cast
  simp_rw [hk, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hp (T : Finset (Fin n)) (U : Finset (Fin n)) :
      chi T (word U) * chi T v * chi T w = chi T (word U) * chi T (xorWord v w) := by
    have h : chi T v * chi T w = chi T (xorWord v w) := by
      simp only [chi, KrawAux2.sgn, xorWord, Int.cast_prod, Int.cast_ite, Int.cast_neg,
        Int.cast_one, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      rcases Bool.eq_false_or_eq_true (v j) with hv | hv <;>
        rcases Bool.eq_false_or_eq_true (w j) with hw | hw <;> norm_num [hv, hw]
    rw [mul_assoc, h]
  simp_rw [hp, orthogonal]
  let V : Finset (Fin n) := univ.filter fun j => v j ≠ w j
  have he (U : Finset (Fin n)) : word U = xorWord v w ↔ U = V := by
    constructor
    · intro h
      ext j
      have hj := congrFun h j
      cases hv : v j <;> cases hw : w j <;> simpa [word, xorWord, V, hv, hw] using hj
    · rintro rfl
      funext j
      cases hv : v j <;> cases hw : w j <;> simp [word, xorWord, V, hv, hw]
  simp_rw [he]
  rw [Finset.sum_ite_eq']
  simp [V, distMatrix, hammingDist, eq_comm]

private lemma disjoint_choose (a b c : ℕ) :
    a.choose b * (a-b).choose c = a.choose c * (a-c).choose b := by
  have hb := Nat.choose_mul (n := a) (k := b+c) (s := b) (by omega)
  have hc := Nat.choose_mul (n := a) (k := b+c) (s := c) (by omega)
  have hs : (b+c).choose b = (b+c).choose c := Nat.choose_symm_add
  rw [hs] at hb
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] using hb.symm.trans hc

private lemma reciprocal {n i t : ℕ} (hi : i ≤ n) (ht : t ≤ n) :
    (n.choose i : ℝ) * (K n t i : ℝ) = (n.choose t : ℝ) * (K n i t : ℝ) := by
  have h (j : ℕ) (hj : j ∈ range (min i t + 1)) :
      n.choose i * i.choose j * (n-i).choose (t-j) =
      n.choose t * t.choose j * (n-t).choose (i-j) := by
    have hji : j ≤ i := by simp only [mem_range] at hj; omega
    have hjt : j ≤ t := by simp only [mem_range] at hj; omega
    rw [Nat.choose_mul hji, Nat.choose_mul hjt, mul_assoc, mul_assoc]
    congr 1
    have he1 : n-j-(i-j) = n-i := by omega
    have he2 : n-j-(t-j) = n-t := by omega
    simpa only [he1, he2] using disjoint_choose (n-j) (i-j) (t-j)
  simp only [K, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, Finset.mul_sum]
  rw [min_comm t i]
  apply Finset.sum_congr rfl
  intro j hj
  have he : (n.choose i : ℝ) * (i.choose j : ℝ) * ((n-i).choose (t-j) : ℝ) =
      (n.choose t : ℝ) * (t.choose j : ℝ) * ((n-t).choose (i-j) : ℝ) := by
    exact_mod_cast h j hj
  calc
    _ = (-1 : ℝ)^j * ((n.choose i : ℝ) * (i.choose j : ℝ) * ((n-i).choose (t-j) : ℝ)) := by ring
    _ = (-1 : ℝ)^j * ((n.choose t : ℝ) * (t.choose j : ℝ) * ((n-t).choose (i-j) : ℝ)) := by rw [he]
    _ = _ := by ring

private lemma pair_nonneg {n : ℕ} (C : Finset (Word n)) (t : ℕ) :
    0 ≤ ∑ i ∈ range (n+1), (K n t i : ℝ) *
      (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ) := by
  classical
  have hp : (∑ i ∈ range (n+1), K n t i *
      (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℤ)) =
      ∑ T ∈ powersetCard t (univ : Finset (Fin n)),
        (∑ w ∈ C, KrawAux2.sgn T w) * (∑ w ∈ C, KrawAux2.sgn T w) := by
    have h1 : (∑ i ∈ range (n+1), K n t i *
        (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℤ)) =
        ∑ p ∈ C ×ˢ C, K n t (hammingDist p.1 p.2) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Word n × Word n => hammingDist p.1 p.2)
        (t := range (n+1)) (fun p _ => Finset.mem_range.mpr
          (Nat.lt_succ_of_le (hammingDist_le_card_fintype.trans (by simp))))]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
        Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [h1]
    have h2 (p : Word n × Word n) : K n t (hammingDist p.1 p.2) =
        ∑ T ∈ powersetCard t (univ : Finset (Fin n)), KrawAux2.sgn T p.1 * KrawAux2.sgn T p.2 := by
      rw [hammingDist, ← KrawAux.char_sum n t (univ.filter fun j => p.1 j ≠ p.2 j)]
      exact Finset.sum_congr rfl fun T _ => KrawAux2.sign_pair T p.1 p.2
    rw [Finset.sum_congr rfl fun p _ => h2 p, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hn : (0 : ℤ) ≤ ∑ i ∈ range (n+1), K n t i *
      (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℤ) := by
    rw [hp]
    exact Finset.sum_nonneg fun T _ => mul_self_nonneg _
  exact_mod_cast hn

private noncomputable def eigenweight {n : ℕ} (C : Finset (Word n)) (t : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), ytilde C i * (K n i t : ℝ)

private lemma eigenweight_nonneg {n : ℕ} (C : Finset (Word n)) {t : ℕ} (ht : t ≤ n) :
    0 ≤ eigenweight C t := by
  have hct : (n.choose t : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero ht
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  have he : eigenweight C t = (1 / ((2 : ℝ)^n * (n.choose t : ℝ))) *
      ∑ i ∈ range (n+1), (K n t i : ℝ) *
        (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ) := by
    unfold eigenweight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by simp only [mem_range] at hi; omega
    have hci : (n.choose i : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hin
    have hr := reciprocal hin ht
    unfold ytilde
    field_simp
    nlinarith [hr]
  rw [he]
  exact mul_nonneg (by positivity) (pair_nonneg C t)

private lemma representation {n : ℕ} (C : Finset (Word n)) :
    Mtilde C = (1 / (2 : ℝ)^n) • ∑ T : Finset (Fin n),
      eigenweight C T.card • Matrix.vecMulVec (chi T) (chi T) := by
  classical
  ext v w
  simp only [Mtilde, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  have he (T : Finset (Fin n)) : eigenweight C T.card * (chi T v * chi T w) =
      ∑ i ∈ range (n+1), ytilde C i * ((K n i T.card : ℝ) * chi T v * chi T w) := by
    unfold eigenweight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, inverse]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  field_simp

end DelsartePSDAux

open DelsartePSDAux in
/-- The radialized code correlation matrix is a nonnegative sum of character outer products. -/
theorem solution {n : ℕ} (C : Finset (Word n)) : (Mtilde C).PosSemidef := by
  classical
  rw [representation]
  apply Matrix.PosSemidef.smul _ (by positivity)
  apply Matrix.posSemidef_sum
  intro T _
  apply Matrix.PosSemidef.smul _ (eigenweight_nonneg C (by simpa using T.card_le_univ))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (chi T)
