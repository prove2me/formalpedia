-- Prove2me | solution 1 for MvPowerSeries.exists_algEquiv_apply_X_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bb742038-a89c-5058-bbaa-4812e76e07fc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_algEquiv_apply_X_eq

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace FormalIFT

variable {W : Type*} [CommRing W] {σ : Type*} [Fintype σ] [DecidableEq σ]

section Order

omit [Fintype σ] [DecidableEq σ] in
theorem le_order_finset_sum {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ W) (n : ℕ∞)
    (h : ∀ i ∈ s, n ≤ order (F i)) : n ≤ order (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ min_order_le_add
    exact le_min (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fintype σ] [DecidableEq σ] in

theorem le_order_pow_sub_pow {u v : MvPowerSeries σ W} (hu : (1 : ℕ∞) ≤ order u) (hv : (1 : ℕ∞) ≤ order v)
    (huv : (2 : ℕ∞) ≤ order (u - v)) (k : ℕ) : ((k + 1 : ℕ) : ℕ∞) ≤ order (u ^ k - v ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [← geom_sum₂_mul]

    have hs : ((k - 1 : ℕ) : ℕ∞) ≤ order (∑ i ∈ Finset.range k, u ^ i * v ^ (k - 1 - i)) := by
      refine le_order_finset_sum _ _ _ fun i hi => ?_
      rw [Finset.mem_range] at hi
      refine le_trans ?_ le_order_mul
      have h1 : ((i : ℕ) : ℕ∞) ≤ order (u ^ i) :=
        le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right hu i) (le_order_pow i))
      have h2 : ((k - 1 - i : ℕ) : ℕ∞) ≤ order (v ^ (k - 1 - i)) :=
        le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right hv (k - 1 - i)) (le_order_pow _))
      calc ((k - 1 : ℕ) : ℕ∞) = ((i : ℕ) : ℕ∞) + ((k - 1 - i : ℕ) : ℕ∞) := by
            rw [← Nat.cast_add]; congr 1; omega
        _ ≤ order (u ^ i) + order (v ^ (k - 1 - i)) := add_le_add h1 h2
    refine le_trans ?_ le_order_mul
    calc ((k + 1 : ℕ) : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]; congr 1; omega
      _ ≤ _ := add_le_add hs (by exact_mod_cast huv)

omit [Fintype σ] [DecidableEq σ] in

theorem le_order_prod_sub_prod {ι : Type*} (t : Finset ι) (A B : ι → MvPowerSeries σ W) (m : ι → ℕ)
    (hA : ∀ i ∈ t, ((m i : ℕ) : ℕ∞) ≤ order (A i)) (hB : ∀ i ∈ t, ((m i : ℕ) : ℕ∞) ≤ order (B i))
    (hAB : ∀ i ∈ t, ((m i + 1 : ℕ) : ℕ∞) ≤ order (A i - B i)) :
    ((∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) ≤ order (∏ i ∈ t, A i - ∏ i ∈ t, B i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hBt : ((∑ i ∈ t, m i : ℕ) : ℕ∞) ≤ order (∏ i ∈ t, B i) := by
      refine le_trans ?_ (le_order_prod _ _)
      push_cast
      exact Finset.sum_le_sum fun i hi => hB i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have e : A a * ∏ i ∈ t, A i - B a * ∏ i ∈ t, B i
        = A a * (∏ i ∈ t, A i - ∏ i ∈ t, B i) + (A a - B a) * ∏ i ∈ t, B i := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      calc ((m a + ∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) = ((m a : ℕ) : ℕ∞) + ((∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) := by
            push_cast; ring
        _ ≤ _ := add_le_add (hA a (Finset.mem_insert_self a t))
              (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)) (fun i hi => hB i (Finset.mem_insert_of_mem hi))
                (fun i hi => hAB i (Finset.mem_insert_of_mem hi)))
    · refine le_trans ?_ le_order_mul
      calc ((m a + ∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) = ((m a + 1 : ℕ) : ℕ∞) + ((∑ i ∈ t, m i : ℕ) : ℕ∞) := by
            push_cast; ring
        _ ≤ _ := add_le_add (hAB a (Finset.mem_insert_self a t)) hBt

omit [DecidableEq σ] in

theorem prod_X_pow_eq_monomial (d : σ →₀ ℕ) :
    ∏ s, (X s : MvPowerSeries σ W) ^ (d s) = monomial d 1 := by
  classical
  have key : ∀ t : Finset σ, ∏ s ∈ t, (X s : MvPowerSeries σ W) ^ (d s)
      = monomial (∑ s ∈ t, Finsupp.single s (d s)) 1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

theorem le_order_prod_pow_sub_monomial (g : σ → MvPowerSeries σ W) (hg0 : ∀ s, constantCoeff (g s) = 0)
    (hg1 : ∀ s, (2 : ℕ∞) ≤ order (g s - X s)) (d : σ →₀ ℕ) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤ order (∏ s, g s ^ (d s) - monomial d 1) := by
  rw [← prod_X_pow_eq_monomial]
  have hX : ∀ s : σ, (1 : ℕ∞) ≤ order (X s : MvPowerSeries σ W) := fun s =>
    one_le_order_iff_constCoeff_eq_zero.mpr (constantCoeff_X _)
  have hg : ∀ s : σ, (1 : ℕ∞) ≤ order (g s) := fun s =>
    one_le_order_iff_constCoeff_eq_zero.mpr (hg0 s)
  have h := le_order_prod_sub_prod (Finset.univ : Finset σ) (fun s => g s ^ (d s)) (fun s => (X s : MvPowerSeries σ W) ^ (d s))
    (fun s => d s)
    (fun s _ => le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right (hg s) (d s)) (le_order_pow _)))
    (fun s _ => le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right (hX s) (d s)) (le_order_pow _)))
    (fun s _ => le_order_pow_sub_pow (hg s) (hX s) (hg1 s) (d s))
  rw [Finsupp.degree_eq_sum]
  exact h

end Order

section Unipotent

variable (g : σ → MvPowerSeries σ W) (hg0 : ∀ s, constantCoeff (g s) = 0)
  (hg1 : ∀ s, (2 : ℕ∞) ≤ order (g s - X s))

include hg0 hg1 in

theorem coeff_prod_pow (d e : σ →₀ ℕ) (hde : e.degree ≤ d.degree) :
    coeff e (∏ s, g s ^ (d s)) = if e = d then 1 else 0 := by
  have h := le_order_prod_pow_sub_monomial g hg0 hg1 d
  have hz : coeff e (∏ s, g s ^ (d s) - monomial d 1) = 0 :=
    coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hde) h)
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, coeff_monomial]

include hg0 hg1 in

theorem coeff_subst_eq_coeff (F : MvPowerSeries σ W) (n : ℕ)
    (hF : ∀ d : σ →₀ ℕ, d.degree < n → coeff d F = 0) (e : σ →₀ ℕ) (he : e.degree ≤ n) :
    coeff e (subst g F) = coeff e F := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hg0)]
  have hterm : ∀ d : σ →₀ ℕ,
      coeff d F • coeff e (d.prod fun s n => g s ^ n) = if d = e then coeff e F else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
    by_cases hde : d = e
    · subst hde
      rw [if_pos rfl]
      by_cases hd : d.degree < n
      · rw [hF d hd, zero_smul]
      · push_neg at hd
        rw [coeff_prod_pow g hg0 hg1 d d le_rfl, if_pos rfl, smul_eq_mul, mul_one]
    · rw [if_neg hde]
      by_cases hd : d.degree < n
      · rw [hF d hd, zero_smul]
      · push_neg at hd
        rw [coeff_prod_pow g hg0 hg1 d e (le_trans he hd), if_neg (Ne.symm hde), smul_zero]
  rw [finsum_congr hterm, finsum_eq_single _ e (fun d hd => if_neg hd), if_pos rfl]

def T (F : MvPowerSeries σ W) : MvPowerSeries σ W := F - subst g F

include hg0 in
theorem T_add (F G : MvPowerSeries σ W) : T g (F + G) = T g F + T g G := by
  simp only [T, subst_add (hasSubst_of_constantCoeff_zero hg0)]
  ring

include hg0 in
theorem T_sum {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ W) :
    T g (∑ i ∈ s, F i) = ∑ i ∈ s, T g (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, T, ← coe_substAlgHom (hasSubst_of_constantCoeff_zero hg0), map_zero,
      sub_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, T_add g hg0, ih]

include hg0 hg1 in

theorem coeff_iterate_T (k : ℕ) : ∀ (G : MvPowerSeries σ W) (e : σ →₀ ℕ), e.degree < k →
    coeff e ((T g)^[k] G) = 0 := by
  induction k with
  | zero => intro G e he; exact absurd he (Nat.not_lt_zero _)
  | succ k ih =>
    intro G e he
    rw [Function.iterate_succ_apply', T, map_sub,
      coeff_subst_eq_coeff g hg0 hg1 _ k (fun d hd => ih G d hd) e (Nat.lt_succ_iff.mp he), sub_self]

include hg0 hg1 in

theorem subst_injective_aux (F : MvPowerSeries σ W) (hF : subst g F = 0) : F = 0 := by
  have hT : T g F = F := by rw [T, hF, sub_zero]
  ext e
  rw [map_zero, ← Function.iterate_fixed hT (e.degree + 1)]
  exact coeff_iterate_T g hg0 hg1 (e.degree + 1) F e (Nat.lt_succ_self _)

def psi (G : MvPowerSeries σ W) : MvPowerSeries σ W :=
  fun e => ∑ k ∈ Finset.range (e.degree + 1), coeff e ((T g)^[k] G)

theorem coeff_psi (G : MvPowerSeries σ W) (e : σ →₀ ℕ) :
    coeff e (psi g G) = ∑ k ∈ Finset.range (e.degree + 1), coeff e ((T g)^[k] G) := rfl

def S (G : MvPowerSeries σ W) (m : ℕ) : MvPowerSeries σ W := ∑ k ∈ Finset.range (m + 1), (T g)^[k] G

include hg0 hg1 in
theorem coeff_psi_eq_coeff_S (G : MvPowerSeries σ W) (m : ℕ) (e : σ →₀ ℕ) (he : e.degree ≤ m) :
    coeff e (psi g G) = coeff e (S g G m) := by
  rw [coeff_psi, S, map_sum]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ he)) fun k _ hk' => ?_
  have hk2 : e.degree < k := by
    simp only [Finset.mem_range, not_lt] at hk'
    omega
  exact coeff_iterate_T g hg0 hg1 k G e hk2

include hg0 in

theorem subst_S (G : MvPowerSeries σ W) (m : ℕ) : subst g (S g G m) = G - (T g)^[m + 1] G := by
  have e1 : subst g (S g G m) = S g G m - T g (S g G m) := by rw [T]; ring
  rw [e1, S, T_sum g hg0]
  have e2 : ∑ k ∈ Finset.range (m + 1), T g ((T g)^[k] G) = ∑ k ∈ Finset.range (m + 1), (T g)^[k + 1] G :=
    Finset.sum_congr rfl fun k _ => by rw [Function.iterate_succ_apply']
  rw [e2, ← sub_eq_zero]
  have e3 := Finset.sum_range_sub (fun k => (T g)^[k] G) (m + 1)
  rw [Function.iterate_zero_apply, Finset.sum_sub_distrib] at e3
  linear_combination -e3

include hg0 hg1 in

theorem subst_psi (G : MvPowerSeries σ W) : subst g (psi g G) = G := by
  ext e
  set m := e.degree with hm
  have hvan : ∀ d : σ →₀ ℕ, d.degree < m + 1 → coeff d (psi g G - S g G m) = 0 := by
    intro d hd
    rw [map_sub, coeff_psi_eq_coeff_S g hg0 hg1 G m d (Nat.lt_succ_iff.mp hd), sub_self]
  have h1 : coeff e (subst g (psi g G - S g G m)) = 0 := by
    rw [coeff_subst_eq_coeff g hg0 hg1 _ (m + 1) hvan e (by omega), hvan e (by omega)]
  rw [subst_sub (hasSubst_of_constantCoeff_zero hg0), map_sub, sub_eq_zero] at h1
  rw [h1, subst_S g hg0, map_sub, coeff_iterate_T g hg0 hg1 (m + 1) G e (by omega), sub_zero]

include hg0 hg1 in

theorem bijective_substAlgHom : Function.Bijective (substAlgHom (hasSubst_of_constantCoeff_zero hg0) :
    MvPowerSeries σ W →ₐ[W] MvPowerSeries σ W) := by
  rw [coe_substAlgHom]
  constructor
  · intro F₁ F₂ h
    have h' : subst g (F₁ - F₂) = 0 := by
      rw [subst_sub (hasSubst_of_constantCoeff_zero hg0)]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (subst_injective_aux g hg0 hg1 _ h')
  · intro G
    exact ⟨psi g G, subst_psi g hg0 hg1 G⟩

end Unipotent

section Linear

omit [Fintype σ] [DecidableEq σ] in
theorem substAlgHom_congr {a b : σ → MvPowerSeries σ W} (ha : HasSubst a) (hb : HasSubst b) (h : a = b)
    (F : MvPowerSeries σ W) : substAlgHom ha F = substAlgHom hb F := by
  subst h
  rfl

def lin (M : Matrix σ σ W) : σ → MvPowerSeries σ W := fun i => ∑ j, M i j • (X j : MvPowerSeries σ W)

omit [DecidableEq σ] in
theorem lin_apply (M : Matrix σ σ W) (i : σ) : lin M i = ∑ j, M i j • (X j : MvPowerSeries σ W) := rfl

theorem coeff_single_lin (M : Matrix σ σ W) (i k : σ) : coeff (Finsupp.single k 1) (lin M i) = M i k := by
  rw [lin_apply, map_sum]
  simp only [coeff_smul, coeff_index_single_X, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ k (fun j => M i j), if_pos (Finset.mem_univ k)]

theorem constantCoeff_lin (M : Matrix σ σ W) (i : σ) : constantCoeff (lin M i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, lin_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_smul, coeff_X, if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)), mul_zero]

theorem hasSubst_lin (M : Matrix σ σ W) : HasSubst (lin M) := hasSubst_of_constantCoeff_zero (constantCoeff_lin M)

def φL (M : Matrix σ σ W) : MvPowerSeries σ W →ₐ[W] MvPowerSeries σ W := substAlgHom (hasSubst_lin M)

theorem φL_X (M : Matrix σ σ W) (i : σ) : φL M (X i) = lin M i := by
  rw [φL, substAlgHom_X]

theorem φL_lin (M N : Matrix σ σ W) (i : σ) : φL N (lin M i) = lin (M * N) i := by
  simp only [lin_apply, map_sum, map_smul, φL_X]
  simp only [lin_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem φL_comp (M N : Matrix σ σ W) (F : MvPowerSeries σ W) : φL N (φL M F) = φL (M * N) F := by
  rw [φL, φL, substAlgHom_comp_substAlgHom_apply]
  refine substAlgHom_congr _ _ ?_ F
  funext i
  exact φL_lin M N i

theorem lin_one : lin (1 : Matrix σ σ W) = fun s => (X s : MvPowerSeries σ W) := by
  funext i
  rw [lin_apply]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq Finset.univ i (fun j => (X j : MvPowerSeries σ W)), if_pos (Finset.mem_univ i)]

theorem φL_one (F : MvPowerSeries σ W) : φL (1 : Matrix σ σ W) F = F := by
  rw [φL, substAlgHom_congr (hasSubst_lin 1) HasSubst.X lin_one F]
  change (⇑(substAlgHom HasSubst.X)) F = F
  rw [coe_substAlgHom, subst_self, id]

def linEquiv (M : Matrix σ σ W) (hM : IsUnit M.det) : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W :=
  AlgEquiv.ofAlgHom (φL M) (φL M⁻¹)
    (AlgHom.ext fun F => by rw [AlgHom.comp_apply, φL_comp, Matrix.nonsing_inv_mul _ hM, φL_one]; rfl)
    (AlgHom.ext fun F => by rw [AlgHom.comp_apply, φL_comp, Matrix.mul_nonsing_inv _ hM, φL_one]; rfl)

theorem linEquiv_X (M : Matrix σ σ W) (hM : IsUnit M.det) (i : σ) : linEquiv M hM (X i) = lin M i :=
  φL_X M i

end Linear

section Main

omit [Fintype σ] [DecidableEq σ] in
theorem exists_single_of_degree_eq_one (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ k, d = Finsupp.single k 1 := by
  have hd : d ∈ {d : σ →₀ ℕ | d.degree = 1} := h
  rw [← Finsupp.range_single_one] at hd
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, hk.symm⟩

theorem exists_algEquiv (f : σ → MvPowerSeries σ W) (h0 : ∀ i, constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : σ => coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W, ∀ i, e (X i) = f i := by
  set M : Matrix σ σ W := Matrix.of fun i j : σ => coeff (Finsupp.single j 1) (f i) with hMdef
  have hM : ∀ i j, M i j = coeff (Finsupp.single j 1) (f i) := fun i j => rfl

  set g : σ → MvPowerSeries σ W := fun i => ∑ j, M⁻¹ i j • f j with hgdef
  have hg0 : ∀ i, constantCoeff (g i) = 0 := by
    intro i
    rw [hgdef, ← coeff_zero_eq_constantCoeff_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_smul, coeff_zero_eq_constantCoeff_apply, h0 j, mul_zero]
  have hglin : ∀ i k, coeff (Finsupp.single k 1) (g i) = if k = i then 1 else 0 := by
    intro i k
    rw [hgdef, map_sum]
    simp only [coeff_smul, ← hM]
    have e : ∑ j, M⁻¹ i j * M j k = (M⁻¹ * M) i k := (Matrix.mul_apply).symm
    rw [e, Matrix.nonsing_inv_mul _ h1, Matrix.one_apply]
    by_cases hik : i = k
    · subst hik; simp
    · rw [if_neg hik, if_neg (Ne.symm hik)]
  have hg1 : ∀ i, (2 : ℕ∞) ≤ order (g i - X i) := by
    intro i
    refine nat_le_order fun d hd => ?_
    rw [map_sub]
    rcases Nat.lt_succ_iff.mp hd |>.lt_or_eq with hlt | heq
    ·
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.lt_one_iff.mp hlt)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hg0 i, constantCoeff_X, sub_self]
    · obtain ⟨k, rfl⟩ := exists_single_of_degree_eq_one d heq
      rw [hglin i k, coeff_index_single_X, sub_self]

  let eg : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W :=
    AlgEquiv.ofBijective (substAlgHom (hasSubst_of_constantCoeff_zero hg0)) (bijective_substAlgHom g hg0 hg1)
  have heg : ∀ i, eg (X i) = g i := fun i => by
    show substAlgHom (hasSubst_of_constantCoeff_zero hg0) (X i) = g i
    rw [substAlgHom_X]
  refine ⟨(linEquiv M h1).trans eg, fun i => ?_⟩
  rw [AlgEquiv.trans_apply, linEquiv_X, lin_apply, map_sum]
  simp only [map_smul, heg, hgdef, Finset.smul_sum, smul_smul]

  rw [Finset.sum_comm]
  have e : ∀ l, ∑ j, (M i j * M⁻¹ j l) • f l = ((M * M⁻¹) i l) • f l := fun l => by
    rw [← Finset.sum_smul, ← Matrix.mul_apply]
  simp only [e, Matrix.mul_nonsing_inv _ h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq Finset.univ i f, if_pos (Finset.mem_univ i)]

end Main

end FormalIFT

end

theorem solution
    {W : Type*} [CommRing W] (f : Fin 2 → MvPowerSeries (Fin 2) W)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 => MvPowerSeries.coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W, ∀ i, e (MvPowerSeries.X i) = f i :=
  FormalIFT.exists_algEquiv f h0 h1

end S_MvPowerSeries_exists_algEquiv_apply_X_eq
end P2MW
export P2MW.S_MvPowerSeries_exists_algEquiv_apply_X_eq (solution)
