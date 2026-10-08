-- Prove2me | solution 1 for MatousekLP.Codes.delsarte_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:45:07.230264+00:00
-- url     : https://prove2.me/submissions/b0e8d01b-14cb-4b17-9a88-431770787709

import Definitions.Def_MatousekLP_Codes_DelsarteLP
import Mathlib

open Finset Polynomial MatousekLP.Codes

namespace KrawAux

/-- Coefficients of `(1 - X)^i`. -/
lemma coeff_one_sub_X_pow (i a : ℕ) :
    ((1 - X : ℤ[X]) ^ i).coeff a = (-1 : ℤ) ^ a * (i.choose a : ℤ) := by
  have h : (1 - X : ℤ[X]) ^ i = (C (-1 : ℤ)) ^ i * (X + C (-1 : ℤ)) ^ i := by
    rw [← mul_pow]; congr 1; simp [C_neg, C_1]; ring
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
    · simp [Finset.filter_mem_eq_inter]
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

open Finset MatousekLP.Codes KrawAux KrawAux2 in
theorem krawtchouk_ineq {n : ℕ} (C : Finset (Word n)) (t : ℕ) (ht1 : 1 ≤ t)
    (htn : t ≤ n) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), (K n t i : ℝ) * xtilde C i := by
  classical
  -- integer form of the pair sum
  set S : ℤ := ∑ i ∈ range (n + 1), K n t i * (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℤ)
  have hS : S = ∑ T ∈ powersetCard t (univ : Finset (Fin n)),
      (∑ w ∈ C, sgn T w) * (∑ w ∈ C, sgn T w) := by
    -- regroup by distance
    have h1 : S = ∑ p ∈ C ×ˢ C, K n t (hammingDist p.1 p.2) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Word n × Word n => hammingDist p.1 p.2)
        (t := range (n + 1)) (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hammingDist_le_card_fintype.trans (by simp))))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2], Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    rw [h1]
    -- expand K by the character identity
    have h2 : ∀ p : Word n × Word n, K n t (hammingDist p.1 p.2) =
        ∑ T ∈ powersetCard t (univ : Finset (Fin n)), sgn T p.1 * sgn T p.2 := by
      intro p
      rw [hammingDist, ← char_sum n t (univ.filter fun j => p.1 j ≠ p.2 j)]
      · exact Finset.sum_congr rfl fun T _ => sign_pair T p.1 p.2
    rw [Finset.sum_congr rfl fun p _ => h2 p, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg fun T _ => mul_self_nonneg _
  have hreal : ∑ i ∈ Finset.range (n + 1), (K n t i : ℝ) * xtilde C i = (1 / (C.card : ℝ)) * (S : ℝ) := by
    simp only [xtilde, S, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hreal]
  exact mul_nonneg (by positivity) (by exact_mod_cast hSnn)

namespace FeasAux

open Finset MatousekLP.Codes

lemma pairs_partition {n : ℕ} (C : Finset (Word n)) :
    ∑ i ∈ range (n + 1), (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ) = (C.card : ℝ) * C.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun p : Word n × Word n => hammingDist p.1 p.2)
    (s := C ×ˢ C) (t := range (n + 1))
    (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hammingDist_le_card_fintype.trans (by simp))))
  rw [Finset.card_product] at h
  exact_mod_cast h.symm

lemma diag_count {n : ℕ} (C : Finset (Word n)) :
    #{p ∈ C ×ˢ C | hammingDist p.1 p.2 = 0} = C.card := by
  have : ((C ×ˢ C).filter fun p : Word n × Word n => hammingDist p.1 p.2 = 0) = C.diag := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag, hammingDist_eq_zero]
    constructor
    · rintro ⟨⟨ha, -⟩, h⟩; exact ⟨ha, h⟩
    · rintro ⟨ha, rfl⟩; exact ⟨⟨ha, ha⟩, rfl⟩
  rw [this, Finset.diag_card]

end FeasAux

open Finset MatousekLP.Codes FeasAux in
theorem xtilde_feas {n d : ℕ} (C : Finset (Word n)) (hC : C.Nonempty)
    (hd : HasDistance C d) :
    delsarteObjective (fun i : Fin (n + 1) => xtilde C i) = (C.card : ℝ) ∧
      IsDelsarteFeasible n d (fun i : Fin (n + 1) => xtilde C i) := by
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [delsarteObjective, xtilde]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = i} : ℝ)),
      pairs_partition]
    field_simp
  · show (1 / (C.card : ℝ)) * (#{p ∈ C ×ˢ C | hammingDist p.1 p.2 = 0} : ℝ) = 1
    rw [diag_count]; field_simp
  · intro i hi1 hid
    simp only [xtilde]
    have : #{p ∈ C ×ˢ C | hammingDist p.1 p.2 = (i : ℕ)} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨a, b⟩ hab hdist
      rw [Finset.mem_product] at hab
      by_cases h : a = b
      · subst h; simp at hdist; omega
      · have := hd a hab.1 b hab.2 h; simp only at hdist; omega
    rw [this]; simp
  · intro t ht1 htn
    have := krawtchouk_ineq C t ht1 htn
    rwa [← Fin.sum_univ_eq_sum_range (fun i => (K n t i : ℝ) * xtilde C i)] at this
  · intro i
    simp only [xtilde]; positivity

open Finset MatousekLP.Codes in
theorem solution (n d : ℕ) (v : ℝ)
    (hv : ∀ x : Fin (n + 1) → ℝ, IsDelsarteFeasible n d x → delsarteObjective x ≤ v) :
    (A n d : ℝ) ≤ v := by
  classical
  -- the point e₀ is feasible with objective 1, so v ≥ 1
  set e0 : Fin (n + 1) → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0
  have hK0 : ∀ t, K n t 0 = (n.choose t : ℤ) := by intro t; simp [K]
  have he0 : IsDelsarteFeasible n d e0 := by
    refine ⟨by simp [e0], fun i hi1 _ => by simp only [e0]; rw [if_neg (by omega)], fun t _ _ => ?_, fun i => by
      simp only [e0]; split_ifs <;> norm_num⟩
    rw [Finset.sum_eq_single (0 : Fin (n + 1)) (fun i _ hi => by
      simp [e0, Fin.val_eq_zero_iff, hi]) (by simp)]
    simp [e0, hK0]
  have hv1 : 1 ≤ v := by
    have := hv e0 he0
    simp only [delsarteObjective] at this
    rwa [Finset.sum_eq_single (0 : Fin (n + 1)) (fun i _ hi => by simp [e0, Fin.val_eq_zero_iff, hi])
      (by simp), show e0 0 = 1 by simp [e0]] at this
  -- an optimal code
  set F := (Finset.univ : Finset (Finset (Word n))).filter (fun C => HasDistance C d)
  have hF : F.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw => absurd hw (Finset.notMem_empty w)⟩⟩
  obtain ⟨C, hCF, hCmax⟩ := Finset.exists_mem_eq_sup F hF Finset.card
  have hA : A n d = C.card := by unfold A; exact hCmax
  rw [hA]
  rcases C.eq_empty_or_nonempty with h | h
  · simp [h]; linarith
  · obtain ⟨hobj, hfeas⟩ := xtilde_feas C h (Finset.mem_filter.mp hCF).2
    rw [← hobj]; exact hv _ hfeas
