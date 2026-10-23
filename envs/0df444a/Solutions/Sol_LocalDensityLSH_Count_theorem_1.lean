-- Prove2me | solution 1 for LocalDensityLSH.Count.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T08:07:35.161353+00:00
-- url     : https://prove2.me/submissions/c0ce858b-7000-4b7a-9798-2d04f99ac51a

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

set_option autoImplicit false

namespace LSHAux

open Finset

/-- expectation of `F` under `K` i.i.d. draws with weights `w`. -/
noncomputable def iE {α : Type*} [Fintype α] {K : ℕ} (w : α → ℝ) (F : (Fin K → α) → ℝ) : ℝ :=
  ∑ τ : Fin K → α, (∏ k, w (τ k)) * F τ

section
variable {α : Type*} [Fintype α] {K : ℕ} (w : α → ℝ)

lemma iE_prod (h : Fin K → α → ℝ) :
    iE w (fun τ => ∏ k, h k (τ k)) = ∏ k, ∑ x, w x * h k x := by
  unfold iE
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [← Finset.prod_mul_distrib]

lemma iE_add (F G : (Fin K → α) → ℝ) :
    iE w (fun τ => F τ + G τ) = iE w F + iE w G := by
  unfold iE; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_); ring

lemma iE_cmul (c : ℝ) (F : (Fin K → α) → ℝ) :
    iE w (fun τ => c * F τ) = c * iE w F := by
  unfold iE; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_); ring

lemma iE_sum {ι : Type*} (s : Finset ι) (F : ι → (Fin K → α) → ℝ) :
    iE w (fun τ => ∑ i ∈ s, F i τ) = ∑ i ∈ s, iE w (F i) := by
  unfold iE; simp_rw [Finset.mul_sum]; exact Finset.sum_comm

lemma iE_mono {F G : (Fin K → α) → ℝ} (hw0 : ∀ x, 0 ≤ w x) (h : ∀ τ, F τ ≤ G τ) :
    iE w F ≤ iE w G := by
  unfold iE
  refine Finset.sum_le_sum (fun τ _ => ?_)
  exact mul_le_mul_of_nonneg_left (h τ) (Finset.prod_nonneg (fun k _ => hw0 _))

variable {w}

lemma iE_const (hw : ∑ x, w x = 1) (c : ℝ) : iE (K := K) w (fun _ => c) = c := by
  have h1 := iE_prod (K := K) w (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, hw] at h1
  have : iE (K := K) w (fun _ => c) = c * iE (K := K) w (fun _ => 1) := by
    rw [← iE_cmul]; simp
  rw [this, h1]; simp

lemma iE_single (hw : ∑ x, w x = 1) (a : Fin K) (f : α → ℝ) :
    iE w (fun τ => f (τ a)) = ∑ x, w x * f x := by
  have h1 := iE_prod w (fun k x => if k = a then f x else 1)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at h1
  rw [h1, Finset.prod_eq_single a]
  · simp
  · intro b _ hb; simp [hb, hw]
  · simp

lemma iE_pair (hw : ∑ x, w x = 1) (a b : Fin K) (hab : a ≠ b) (f g : α → ℝ) :
    iE w (fun τ => f (τ a) * g (τ b)) = (∑ x, w x * f x) * ∑ x, w x * g x := by
  have h1 := iE_prod w (fun k x => (if k = a then f x else 1) * (if k = b then g x else 1))
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true] at h1
  rw [h1, Finset.prod_eq_mul a b hab]
  · simp [hab, hab.symm]
  · intro c _ hc; simp [hc.1, hc.2, hw]
  · simp
  · simp

lemma iE_pair' (hw : ∑ x, w x = 1) (a b : Fin K) (f : α → ℝ) :
    iE w (fun τ => f (τ a) * f (τ b)) =
      if a = b then ∑ x, w x * f x ^ 2 else (∑ x, w x * f x) ^ 2 := by
  split_ifs with hab
  · subst hab
    have := iE_single hw a (fun x => f x ^ 2)
    rw [← this]; congr 1; ext τ; ring
  · rw [iE_pair hw a b hab]; ring

/-- the i.i.d. mean-square identity. -/
lemma iE_meansq (hw : ∑ x, w x = 1) (hK : 1 ≤ K) (f : α → ℝ) (c : ℝ) :
    iE (K := K) w (fun τ => ((∑ k : Fin K, f (τ k)) / K - c) ^ 2) =
      ((∑ x, w x * f x) - c) ^ 2 + ((∑ x, w x * f x ^ 2) - (∑ x, w x * f x) ^ 2) / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have key : ∀ τ : Fin K → α, ((∑ k, f (τ k)) / K - c) ^ 2 =
      (1 / (K : ℝ) ^ 2) * (∑ k, ∑ k', f (τ k) * f (τ k')) +
        ((-(2 * c / K)) * (∑ k, f (τ k)) + c ^ 2) := by
    intro τ; rw [← Finset.sum_mul_sum]; field_simp; ring
  simp_rw [key]
  rw [iE_add, iE_cmul, iE_add, iE_cmul, iE_const hw, iE_sum]
  simp_rw [iE_sum, iE_pair' hw, iE_single hw]
  set E1 := ∑ x, w x * f x
  set E2 := ∑ x, w x * f x ^ 2
  have hs : ∀ k : Fin K, (∑ k' : Fin K, if k = k' then E2 else E1 ^ 2) = E2 + (K - 1) * E1 ^ 2 := by
    intro k
    have : ∀ k' : Fin K, (if k = k' then E2 else E1 ^ 2) = E1 ^ 2 + (if k = k' then E2 - E1 ^ 2 else 0) := by
      intro k'; split_ifs <;> ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp; ring
  simp_rw [hs]
  simp
  field_simp
  ring

end

end LSHAux

namespace LSHAux
open Finset MeasureTheory LocalDensityLSH.Count

section B
variable {n t : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)

noncomputable def ind (τ : Table n t) (i : Fin n) : ℝ := if InBucket I τ i then 1 else 0
noncomputable def f1 (𝒜 : Finset (Fin n)) (τ : Table n t) : ℝ := ∑ i ∈ 𝒜, ind I τ i / p μ I i
noncomputable def cnt (τ : Table n t) : ℝ := ∑ i, ind I τ i
noncomputable def hh (𝒜 : Finset (Fin n)) (τ : Table n t) : ℝ := ∑ i ∈ 𝒜, ind I τ i / p μ I i ^ 2

lemma ind_nonneg (τ : Table n t) (i : Fin n) : 0 ≤ ind I τ i := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (τ : Table n t) (i : Fin n) : ind I τ i ≤ 1 := by unfold ind; split_ifs <;> norm_num
lemma ind_mul_le (τ : Table n t) (i j : Fin n) : ind I τ i * ind I τ j ≤ ind I τ i := by
  unfold ind; split_ifs <;> norm_num

lemma wsum_one : ∑ τ, μ.real {τ} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ]; simp

lemma w_nonneg (τ : Table n t) : 0 ≤ μ.real {τ} := measureReal_nonneg

lemma wind (i : Fin n) : ∑ τ, μ.real {τ} * ind I τ i = p μ I i := by
  have hs : {τ : Table n t | InBucket I τ i} =
      ((Finset.univ.filter (fun τ => InBucket I τ i) : Finset (Table n t)) : Set (Table n t)) := by
    ext; simp
  rw [p, hs, ← sum_measureReal_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  unfold ind; split_ifs <;> simp

variable {I}

lemma Ef1 (𝒜 : Finset (Fin n)) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) :
    ∑ τ, μ.real {τ} * f1 μ I 𝒜 τ = 𝒜.card := by
  unfold f1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i ∈ 𝒜, ∑ τ, μ.real {τ} * (ind I τ i / p μ I i) = 1 := by
    intro i hi
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, wind, div_self (hp i hi).ne']
  rw [Finset.sum_congr rfl this]; simp

lemma pm_le (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) {i : Fin n} (hi : i ∈ 𝒜) :
    pmin μ I h𝒜 ≤ p μ I i := Finset.inf'_le _ hi

lemma pm_pos (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) :
    0 < pmin μ I h𝒜 := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' h𝒜 (p μ I)
  unfold pmin; rw [he]; exact hp i hi

lemma Ef1sq (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) :
    ∑ τ, μ.real {τ} * f1 μ I 𝒜 τ ^ 2 ≤ (𝒜.card : ℝ) ^ 2 / pmin μ I h𝒜 := by
  have hpm := pm_pos μ 𝒜 h𝒜 hp
  have pt : ∀ τ, f1 μ I 𝒜 τ ^ 2 ≤ ∑ i ∈ 𝒜, ∑ j ∈ 𝒜, ind I τ i / (p μ I i * p μ I j) := by
    intro τ
    unfold f1
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
    have := ind_mul_le I τ i j
    have hpi := hp i hi; have hpj := hp j hj
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right this (by positivity)
  calc ∑ τ, μ.real {τ} * f1 μ I 𝒜 τ ^ 2
      ≤ ∑ τ, μ.real {τ} * ∑ i ∈ 𝒜, ∑ j ∈ 𝒜, ind I τ i / (p μ I i * p μ I j) :=
        Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left (pt τ) (w_nonneg μ τ))
    _ = ∑ i ∈ 𝒜, ∑ j ∈ 𝒜, 1 / p μ I j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div, wind]
        have hpi := hp i hi
        field_simp
    _ ≤ ∑ i ∈ 𝒜, ∑ j ∈ 𝒜, 1 / pmin μ I h𝒜 := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j hj => ?_))
        exact one_div_le_one_div_of_le hpm (pm_le μ 𝒜 h𝒜 hj)
    _ = (𝒜.card : ℝ) ^ 2 / pmin μ I h𝒜 := by
        simp; ring

lemma Ecnt : ∑ τ, μ.real {τ} * cnt I τ = EC μ I := by
  unfold cnt EC
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => wind μ I i)

lemma Ehh (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) :
    ∑ τ, μ.real {τ} * hh μ I 𝒜 τ ≤ 𝒜.card / pmin μ I h𝒜 := by
  have hpm := pm_pos μ 𝒜 h𝒜 hp
  unfold hh
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ i ∈ 𝒜, ∑ τ, μ.real {τ} * (ind I τ i / p μ I i ^ 2)
      = ∑ i ∈ 𝒜, 1 / p μ I i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div, wind]
        have hpi := hp i hi
        field_simp
    _ ≤ ∑ i ∈ 𝒜, 1 / pmin μ I h𝒜 :=
        Finset.sum_le_sum (fun i hi => one_div_le_one_div_of_le hpm (pm_le μ 𝒜 h𝒜 hi))
    _ = 𝒜.card / pmin μ I h𝒜 := by simp; ring

lemma Ecnthh (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) :
    ∑ τ, μ.real {τ} * (cnt I τ * hh μ I 𝒜 τ) ≤ EC μ I * 𝒜.card / pmin μ I h𝒜 ^ 2 := by
  have hpm := pm_pos μ 𝒜 h𝒜 hp
  have pt : ∀ τ, cnt I τ * hh μ I 𝒜 τ ≤ ∑ y, ∑ x ∈ 𝒜, ind I τ y / p μ I x ^ 2 := by
    intro τ
    unfold cnt hh
    rw [Finset.sum_mul_sum]
    refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun x hx => ?_))
    have := ind_mul_le I τ y x
    have hpx := hp x hx
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right this (by positivity)
  calc ∑ τ, μ.real {τ} * (cnt I τ * hh μ I 𝒜 τ)
      ≤ ∑ τ, μ.real {τ} * ∑ y, ∑ x ∈ 𝒜, ind I τ y / p μ I x ^ 2 :=
        Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left (pt τ) (w_nonneg μ τ))
    _ = ∑ y, ∑ x ∈ 𝒜, p μ I y / p μ I x ^ 2 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div, wind]
    _ ≤ ∑ y, ∑ x ∈ 𝒜, p μ I y / pmin μ I h𝒜 ^ 2 := by
        refine Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun x hx => ?_))
        have hy : 0 ≤ p μ I y := measureReal_nonneg
        exact div_le_div_of_nonneg_left hy (by positivity)
          (pow_le_pow_left₀ hpm.le (pm_le μ 𝒜 h𝒜 hx) 2)
    _ = EC μ I * 𝒜.card / pmin μ I h𝒜 ^ 2 := by
        unfold EC
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring

end B

end LSHAux

namespace LSHAux
open Finset MeasureTheory LocalDensityLSH.Count

section Csec
variable {n t K : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) (𝒜 : Finset (Fin n))
  (τs : Fin K → Table n t)

lemma sum_pool (g : Fin K × Fin n → ℝ) :
    ∑ y ∈ pool I τs, g y = ∑ y, if InBucket I (τs y.1) y.2 then g y else 0 := by
  rw [← Finset.sum_filter]
  first | rfl | (congr 1; ext y; simp [pool])

lemma C_eq : (C I τs : ℝ) = ∑ k, cnt I (τs k) := by
  unfold C
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, sum_pool, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [cnt, ind]

lemma W_eq : W μ I 𝒜 τs = (∑ k, f1 μ I 𝒜 (τs k)) / K := by
  simp only [W, f1, ind]; ring

lemma empty_pool (h : ¬(pool I τs).Nonempty) (k : Fin K) (i : Fin n) : ¬ InBucket I (τs k) i := by
  intro hb
  exact h ⟨(k, i), by simp [pool, hb]⟩

lemma C_zero_of_empty (h : ¬(pool I τs).Nonempty) : C I τs = 0 := by
  unfold C; rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp

lemma f1_zero_of_empty (h : ¬(pool I τs).Nonempty) (k : Fin K) : f1 μ I 𝒜 (τs k) = 0 := by
  unfold f1
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp [ind, empty_pool I τs h k i]

noncomputable def w2 (y : Fin K × Fin n) : ℝ := (samplerWeight I τs y).toReal

lemma w2_nonneg (y : Fin K × Fin n) : 0 ≤ w2 I τs y := ENNReal.toReal_nonneg

lemma w2_ne (h : (pool I τs).Nonempty) (y : Fin K × Fin n) :
    w2 I τs y = if y ∈ pool I τs then ((pool I τs).card : ℝ)⁻¹ else 0 := by
  unfold w2 samplerWeight
  rw [if_pos h]
  split_ifs <;> simp [ENNReal.toReal_inv]

lemma w2_moment (g : Fin K × Fin n → ℝ) (hg : ¬(pool I τs).Nonempty → ∀ y, g y = 0) :
    ∑ y, w2 I τs y * g y = (∑ y ∈ pool I τs, g y) / C I τs := by
  by_cases h : (pool I τs).Nonempty
  · simp_rw [w2_ne I τs h, ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.mul_sum]
    unfold C; rw [inv_mul_eq_div]
  · have := hg h
    simp [this]

lemma w2_sum (hK : 1 ≤ K) (hn : 1 ≤ n) : ∑ y, w2 I τs y = 1 := by
  by_cases h : (pool I τs).Nonempty
  · have := w2_moment I τs (fun _ => 1) (fun h' => absurd h h')
    simp only [mul_one] at this
    rw [this]
    have hc : (C I τs : ℝ) ≠ 0 := by
      unfold C; exact_mod_cast (Finset.card_pos.mpr h).ne'
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    unfold C at hc ⊢
    exact div_self hc
  · have hKn : ((K : ℝ) * n) ≠ 0 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    simp only [w2, samplerWeight, if_neg h]
    simp [Finset.card_univ, ENNReal.toReal_inv]
    field_simp

lemma Zval_zero_of_empty (h : ¬(pool I τs).Nonempty) (y : Fin K × Fin n) :
    Zval μ I 𝒜 τs y = 0 := by
  simp [Zval, C_zero_of_empty I τs h]

lemma sum_mem_ite (F : Fin n → ℝ) : ∑ i ∈ 𝒜, F i = ∑ i, if i ∈ 𝒜 then F i else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext; simp

lemma pool_Z : ∑ y ∈ pool I τs, Zval μ I 𝒜 τs y =
    (C I τs / K) * ∑ k, f1 μ I 𝒜 (τs k) := by
  rw [sum_pool, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold f1
  rw [sum_mem_ite 𝒜 (fun i => ind I (τs k) i / p μ I i), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hb : InBucket I (τs k) i <;> by_cases hi : i ∈ 𝒜 <;> simp [hb, hi, Zval, ind] <;> ring

lemma pool_Z2 : ∑ y ∈ pool I τs, Zval μ I 𝒜 τs y ^ 2 =
    (C I τs / K) ^ 2 * ∑ k, hh μ I 𝒜 (τs k) := by
  rw [sum_pool, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold hh
  rw [sum_mem_ite 𝒜 (fun i => ind I (τs k) i / p μ I i ^ 2), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hb : InBucket I (τs k) i <;> by_cases hi : i ∈ 𝒜 <;> simp [hb, hi, Zval, ind] <;> ring

lemma EZ : ∑ y, w2 I τs y * Zval μ I 𝒜 τs y = W μ I 𝒜 τs := by
  rw [w2_moment I τs _ (fun h => Zval_zero_of_empty μ I 𝒜 τs h), pool_Z, W_eq]
  by_cases h : (pool I τs).Nonempty
  · have hc : (C I τs : ℝ) ≠ 0 := by
      unfold C; exact_mod_cast (Finset.card_pos.mpr h).ne'
    field_simp
  · simp [C_zero_of_empty I τs h, f1_zero_of_empty μ I 𝒜 τs h]

lemma EZ2 : ∑ y, w2 I τs y * Zval μ I 𝒜 τs y ^ 2 =
    (C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k) := by
  have := w2_moment I τs (fun y => Zval μ I 𝒜 τs y ^ 2)
    (fun h y => by simp [Zval_zero_of_empty μ I 𝒜 τs h y])
  try simp only at this
  rw [this, pool_Z2]
  rcases eq_or_ne (C I τs : ℝ) 0 with h0 | h0
  · simp [h0]
  · field_simp

end Csec

end LSHAux

namespace LSHAux
open Finset MeasureTheory LocalDensityLSH.Count

section Dalg
variable {α : Type*} [Fintype α] {K : ℕ} {w : α → ℝ}

lemma iE_cross (hw : ∑ x, w x = 1) (f g : α → ℝ) :
    iE (K := K) w (fun τ => (∑ k, f (τ k)) * (∑ k, g (τ k))) =
      K * (∑ x, w x * (f x * g x)) + ((K : ℝ) ^ 2 - K) * ((∑ x, w x * f x) * ∑ x, w x * g x) := by
  have e : ∀ τ : Fin K → α, (∑ k, f (τ k)) * (∑ k, g (τ k)) = ∑ k, ∑ k', f (τ k) * g (τ k') :=
    fun τ => Finset.sum_mul_sum _ _ _ _
  simp_rw [e]
  rw [iE_sum]
  simp_rw [iE_sum]
  have hpair : ∀ k k' : Fin K, iE w (fun τ => f (τ k) * g (τ k')) =
      (∑ x, w x * f x) * (∑ x, w x * g x) +
        (if k = k' then (∑ x, w x * (f x * g x)) - (∑ x, w x * f x) * (∑ x, w x * g x) else 0) := by
    intro k k'
    split_ifs with hkk
    · subst hkk
      have := iE_single hw k (fun x => f x * g x)
      try simp only at this
      rw [this]; ring
    · rw [iE_pair hw k k' hkk]; ring
  simp_rw [hpair, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Dalg

lemma arith_bound (N pm EC ε K S : ℝ) (hN : 0 < N) (hpm : 0 < pm) (hEC : 0 < EC) (hε : 0 < ε)
    (hK : 8 / (ε ^ 2 * pm) ≤ K) (hS : 8 * (1 + ε ^ 2) * EC / (ε ^ 2 * N * pm) ≤ S) :
    N ^ 2 / pm / K + (EC * N / pm ^ 2 / K + EC * N / pm) / S ≤ ε ^ 2 * N ^ 2 / 4 := by
  have hK0 : 0 < 8 / (ε ^ 2 * pm) := by positivity
  have hS0 : 0 < 8 * (1 + ε ^ 2) * EC / (ε ^ 2 * N * pm) := by positivity
  have hKp : 0 < K := lt_of_lt_of_le hK0 hK
  have hSp : 0 < S := lt_of_lt_of_le hS0 hS
  have ha : 1 / K ≤ ε ^ 2 * pm / 8 := by
    have := one_div_le_one_div_of_le hK0 hK
    simpa [one_div_div] using this
  have hb : 1 / S ≤ ε ^ 2 * N * pm / (8 * (1 + ε ^ 2) * EC) := by
    have := one_div_le_one_div_of_le hS0 hS
    simpa [one_div_div] using this
  have e1 : N ^ 2 / pm / K = N ^ 2 / pm * (1 / K) := by ring
  have e2 : (EC * N / pm ^ 2 / K + EC * N / pm) / S =
      (EC * N / pm) * (1 / pm * (1 / K) + 1) * (1 / S) := by field_simp
  rw [e1, e2]
  have t1 : N ^ 2 / pm * (1 / K) ≤ N ^ 2 / pm * (ε ^ 2 * pm / 8) :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have t2a : 1 / pm * (1 / K) + 1 ≤ 1 + ε ^ 2 := by
    have : 1 / pm * (1 / K) ≤ 1 / pm * (ε ^ 2 * pm / 8) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    have h2 : 1 / pm * (ε ^ 2 * pm / 8) = ε ^ 2 / 8 := by field_simp
    nlinarith [sq_nonneg ε]
  have t2 : (EC * N / pm) * (1 / pm * (1 / K) + 1) * (1 / S) ≤
      (EC * N / pm) * (1 + ε ^ 2) * (ε ^ 2 * N * pm / (8 * (1 + ε ^ 2) * EC)) := by
    have hpos1 : 0 ≤ EC * N / pm := by positivity
    have hS1 : 0 ≤ 1 / S := by positivity
    calc (EC * N / pm) * (1 / pm * (1 / K) + 1) * (1 / S)
        ≤ (EC * N / pm) * (1 + ε ^ 2) * (1 / S) := by gcongr
      _ ≤ (EC * N / pm) * (1 + ε ^ 2) * (ε ^ 2 * N * pm / (8 * (1 + ε ^ 2) * EC)) := by
          gcongr
  have e3 : N ^ 2 / pm * (ε ^ 2 * pm / 8) = ε ^ 2 * N ^ 2 / 8 := by field_simp
  have e4 : (EC * N / pm) * (1 + ε ^ 2) * (ε ^ 2 * N * pm / (8 * (1 + ε ^ 2) * EC)) =
      ε ^ 2 * N ^ 2 / 8 := by field_simp
  linarith

section Dmain
variable {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
  (𝒜 : Finset (Fin n))

/-- the expected squared error of one estimate, as a finite sum. -/
noncomputable def sqErr (c : ℝ) : ℝ :=
  ∑ τs : Fin K → Table n t, ∑ ξ : Fin S → Fin K × Fin n,
    ((∏ k, μ.real {τs k}) * ∏ s, w2 I τs (ξ s)) * (estimate μ I 𝒜 τs ξ - c) ^ 2

lemma sqErr_le (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i) (hK : 1 ≤ K) (hS : 1 ≤ S)
    (hn : 1 ≤ n) :
    sqErr (K := K) (S := S) μ I 𝒜 𝒜.card ≤
      (𝒜.card : ℝ) ^ 2 / pmin μ I h𝒜 / K +
        (EC μ I * 𝒜.card / pmin μ I h𝒜 ^ 2 / K + EC μ I * 𝒜.card / pmin μ I h𝒜) / S := by
  have hEf1 := Ef1 μ 𝒜 hp
  have hEf1sq := Ef1sq μ 𝒜 h𝒜 hp
  have A1 := Ecnthh μ 𝒜 h𝒜 hp
  have A2 := Ehh μ 𝒜 h𝒜 hp
  have hpm : 0 < pmin μ I h𝒜 := pm_pos μ 𝒜 h𝒜 hp
  set N : ℝ := ((𝒜.card : ℕ) : ℝ) with hNdef
  set pm := pmin μ I h𝒜 with hpmdef
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hw := wsum_one μ
  have hEC0 : 0 ≤ EC μ I := by
    unfold EC; exact Finset.sum_nonneg (fun i _ => measureReal_nonneg)
  -- inner sampling step
  have inner : ∀ τs : Fin K → Table n t,
      iE (K := S) (w2 I τs) (fun ξ => ((∑ s, Zval μ I 𝒜 τs (ξ s)) / S - N) ^ 2) ≤
        (W μ I 𝒜 τs - N) ^ 2 + (1 / (S : ℝ)) * ((C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k)) := by
    intro τs
    rw [iE_meansq (w2_sum I τs hK hn) hS, EZ, EZ2]
    have : 0 ≤ W μ I 𝒜 τs ^ 2 / S := by positivity
    have e : ((C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k) - W μ I 𝒜 τs ^ 2) / S =
      (1 / (S : ℝ)) * ((C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k)) - W μ I 𝒜 τs ^ 2 / S := by
      ring
    rw [e]; linarith
  have hsq : sqErr (K := K) (S := S) μ I 𝒜 N =
      iE (K := K) (fun τ => μ.real {τ}) (fun τs => iE (K := S) (w2 I τs)
        (fun ξ => ((∑ s, Zval μ I 𝒜 τs (ξ s)) / S - N) ^ 2)) := by
    unfold sqErr iE estimate
    refine Finset.sum_congr rfl (fun τs _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    ring
  rw [hsq]
  refine le_trans (iE_mono _ (fun τ => measureReal_nonneg) inner) ?_
  rw [iE_add, iE_cmul]
  -- table step 1
  have h1 : iE (K := K) (fun τ => μ.real {τ}) (fun τs => (W μ I 𝒜 τs - N) ^ 2) ≤ N ^ 2 / pm / K := by
    simp_rw [W_eq]
    rw [iE_meansq hw hK, hEf1]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    have : (0 : ℝ) ≤ N ^ 2 / K := by positivity
    rw [sub_div]
    have : (∑ x, μ.real {x} * f1 μ I 𝒜 x ^ 2) / K ≤ N ^ 2 / pm / K :=
      div_le_div_of_nonneg_right hEf1sq hKr.le
    linarith
  -- table step 2
  have h2 : iE (K := K) (fun τ => μ.real {τ}) (fun τs => (C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k))
      ≤ EC μ I * N / pm ^ 2 / K + EC μ I * N / pm := by
    have e : ∀ τs : Fin K → Table n t, (C I τs / (K : ℝ) ^ 2) * ∑ k, hh μ I 𝒜 (τs k) =
        (1 / (K : ℝ) ^ 2) * ((∑ k, cnt I (τs k)) * ∑ k, hh μ I 𝒜 (τs k)) := by
      intro τs; rw [C_eq]; ring
    simp_rw [e]
    rw [iE_cmul, iE_cross hw, Ecnt]
    have hhnn : 0 ≤ ∑ x, μ.real {x} * hh μ I 𝒜 x := by
      refine Finset.sum_nonneg (fun x _ => mul_nonneg measureReal_nonneg ?_)
      unfold hh
      exact Finset.sum_nonneg (fun i hi => div_nonneg (ind_nonneg I x i) (by have := hp i hi; positivity))
    have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 - K := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith
    have B1 : (K : ℝ) * (∑ x, μ.real {x} * (cnt I x * hh μ I 𝒜 x)) ≤ K * (EC μ I * N / pm ^ 2) :=
      mul_le_mul_of_nonneg_left A1 hKr.le
    have B2 : ((K : ℝ) ^ 2 - K) * (EC μ I * ∑ x, μ.real {x} * hh μ I 𝒜 x) ≤
        (K : ℝ) ^ 2 * (EC μ I * (N / pm)) := by
      have : EC μ I * ∑ x, μ.real {x} * hh μ I 𝒜 x ≤ EC μ I * (N / pm) :=
        mul_le_mul_of_nonneg_left A2 hEC0
      have h3 : 0 ≤ EC μ I * (N / pm) := by positivity
      nlinarith
    have e2 : EC μ I * N / pm ^ 2 / K + EC μ I * N / pm =
        1 / (K : ℝ) ^ 2 * (K * (EC μ I * N / pm ^ 2) + (K : ℝ) ^ 2 * (EC μ I * (N / pm))) := by
      field_simp
    rw [e2]
    have : 0 < 1 / (K : ℝ) ^ 2 := by positivity
    gcongr ?_ * ?_
    linarith
  have h2' := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / S by positivity)
  have e3 : (EC μ I * N / pm ^ 2 / K + EC μ I * N / pm) / S =
      1 / (S : ℝ) * (EC μ I * N / pm ^ 2 / K + EC μ I * N / pm) := by ring
  rw [e3]
  linarith

end Dmain

end LSHAux

namespace LSHAux
open Finset MeasureTheory ProbabilityTheory LocalDensityLSH.Count

section Esec
variable {n t K S : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)

lemma run_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n) (h : IsEstimatorRun μ I P T X)
    (F : (Fin K → Table n t) × (Fin S → Fin K × Fin n) → ℝ) :
    ∫ ω, F ((fun k => T k ω), (fun s => X s ω)) ∂P =
      ∑ τs : Fin K → Table n t, ∑ ξ : Fin S → Fin K × Fin n,
        ((∏ k, μ.real {τs k}) * ∏ s, w2 I τs (ξ s)) * F (τs, ξ) := by
  set G : Ω → (Fin K → Table n t) × (Fin S → Fin K × Fin n) :=
    fun ω => ((fun k => T k ω), (fun s => X s ω)) with hGdef
  have hG : Measurable G := (measurable_pi_lambda _ h.1).prodMk (measurable_pi_lambda _ h.2.1)
  have hF : Measurable F := measurable_of_countable F
  have e0 : (∫ ω, F (G ω) ∂P) = ∫ z, F z ∂(P.map G) :=
    (integral_map hG.aemeasurable hF.aestronglyMeasurable).symm
  rw [e0]
  have : IsProbabilityMeasure (P.map G) := Measure.isProbabilityMeasure_map hG.aemeasurable
  rw [integral_fintype (Integrable.of_finite (f := F)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun τs _ => Finset.sum_congr rfl (fun ξ _ => ?_))
  rw [smul_eq_mul, map_measureReal_apply hG (measurableSet_singleton _)]
  congr 1
  have hpre : G ⁻¹' {(τs, ξ)} = {ω | (∀ k, T k ω = τs k) ∧ ∀ s, X s ω = ξ s} := by
    ext ω; simp [G, Prod.ext_iff, funext_iff]
  rw [hpre, measureReal_def, h.2.2, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_prod]
  rfl

lemma run_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n) (h : IsEstimatorRun μ I P T X)
    (𝒜 : Finset (Fin n)) (c r : ℝ) (hr : 0 < r)
    (hb : sqErr (K := K) (S := S) μ I 𝒜 c ≤ r ^ 2 / 4) :
    P.real {ω | r < |estimate μ I 𝒜 (fun k => T k ω) (fun s => X s ω) - c|} ≤ 1 / 4 := by
  set G : Ω → (Fin K → Table n t) × (Fin S → Fin K × Fin n) :=
    fun ω => ((fun k => T k ω), (fun s => X s ω)) with hGdef
  have hG : Measurable G := (measurable_pi_lambda _ h.1).prodMk (measurable_pi_lambda _ h.2.1)
  set F : (Fin K → Table n t) × (Fin S → Fin K × Fin n) → ℝ :=
    fun z => (estimate μ I 𝒜 z.1 z.2 - c) ^ 2 with hFdef
  have : IsProbabilityMeasure (P.map G) := Measure.isProbabilityMeasure_map hG.aemeasurable
  have hint : Integrable (fun ω => F (G ω)) P :=
    (Integrable.of_finite (μ := P.map G) (f := F)).comp_measurable hG
  have hI : ∫ ω, F (G ω) ∂P = sqErr (K := K) (S := S) μ I 𝒜 c := by
    rw [run_integral μ I P T X h F]; rfl
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => F (G ω))
    (ae_of_all _ (fun ω => sq_nonneg _)) hint (r ^ 2)
  rw [hI] at hm
  have hsub : {ω | r < |estimate μ I 𝒜 (fun k => T k ω) (fun s => X s ω) - c|} ⊆
      {ω | r ^ 2 ≤ F (G ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have := pow_le_pow_left₀ hr.le hω.le 2
    rw [sq_abs] at this
    exact this
  have hr2 : 0 < r ^ 2 := by positivity
  have h1 := measureReal_mono (μ := P) hsub
  have h2 : r ^ 2 * P.real {ω | r ^ 2 ≤ F (G ω)} ≤ r ^ 2 * (1 / 4) := by linarith
  have h3 := le_of_mul_le_mul_left h2 hr2
  linarith

end Esec

lemma sum_map_eq_length (l : List ℝ) (Y : ℝ → ℝ) (h : ∀ b ∈ l, Y b = 1) :
    (l.map Y).sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    ring

lemma median_good {M : ℕ} (hM : 1 ≤ M) (e : Fin M → ℝ) (c r : ℝ)
    (h : (∑ m, (if r < |e m - c| then (1 : ℝ) else 0)) < M / 2) :
    |LocalDensityLSH.Count.median e - c| ≤ r := by
  set Y : ℝ → ℝ := fun x => if r < |x - c| then 1 else 0 with hYdef
  have hY0 : ∀ x, 0 ≤ Y x := by intro x; simp only [hYdef]; split_ifs <;> norm_num
  obtain ⟨L, hL⟩ : ∃ L, L = (List.ofFn e).insertionSort (· ≤ ·) := ⟨_, rfl⟩
  have hperm : L.Perm (List.ofFn e) := by rw [hL]; exact List.perm_insertionSort _ _
  have hsorted : L.Pairwise (· ≤ ·) := by rw [hL]; exact List.pairwise_insertionSort _ _
  have hlen : L.length = M := by rw [hperm.length_eq, List.length_ofFn]
  set j := (M - 1) / 2 with hjdef
  have hj : j < L.length := by rw [hlen]; omega
  have hmed : LocalDensityLSH.Count.median e = L[j] := by
    have : LocalDensityLSH.Count.median e = L.getD j 0 := by rw [hL]; rfl
    rw [this, List.getD_eq_getElem _ _ hj]
  have hsum : (L.map Y).sum = ∑ m, Y (e m) := by
    rw [(hperm.map Y).sum_eq, List.map_ofFn, List.sum_ofFn]; rfl
  have hsplit := List.take_append_drop j L
  have hpw : (L.take j ++ L.drop j).Pairwise (· ≤ ·) := by rw [hsplit]; exact hsorted
  rw [List.pairwise_append] at hpw
  have hdrop : L.drop j = L[j] :: L.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hsumsplit : (L.map Y).sum = ((L.take j).map Y).sum + ((L.drop j).map Y).sum := by
    conv_lhs => rw [← hsplit]
    rw [List.map_append, List.sum_append]
  have hnn : ∀ l : List ℝ, 0 ≤ (l.map Y).sum := fun l =>
    List.sum_nonneg (fun x hx => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hY0 a)
  have hS : (∑ m, Y (e m)) < M / 2 := h
  rw [hmed]
  by_contra hcon
  rw [not_le] at hcon
  rcases lt_abs.mp hcon with h1 | h1
  · -- upper: every element of `drop j` is bad
    have hall : ∀ b ∈ L.drop j, Y b = 1 := by
      intro b hb
      have hle : L[j] ≤ b := by
        rw [hdrop] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact le_rfl
        · have hpw2 : (L.drop j).Pairwise (· ≤ ·) := hsorted.sublist (List.drop_sublist _ _)
          rw [hdrop, List.pairwise_cons] at hpw2
          exact hpw2.1 b hb'
      simp only [hYdef]
      rw [if_pos]
      rw [lt_abs]; left; linarith
    have hd := sum_map_eq_length _ Y hall
    rw [List.length_drop, hlen] at hd
    have hc : (2 : ℝ) * ((M - j : ℕ) : ℝ) ≥ M + 1 := by
      have : 2 * (M - j) ≥ M + 1 := by omega
      exact_mod_cast this
    have := hnn (L.take j)
    linarith
  · -- lower: every element of `take j`, and `L[j]`, is bad
    have hall : ∀ a ∈ L.take j, Y a = 1 := by
      intro a ha
      have hle : a ≤ L[j] := hpw.2.2 a ha L[j] (by rw [hdrop]; exact List.mem_cons_self)
      simp only [hYdef]
      rw [if_pos]
      rw [lt_abs]; right; linarith
    have ht := sum_map_eq_length _ Y hall
    rw [List.length_take, hlen, min_eq_left (by omega)] at ht
    have hYj : Y L[j] = 1 := by
      simp only [hYdef]; rw [if_pos]; rw [lt_abs]; right; linarith
    have hd : ((L.drop j).map Y).sum = Y L[j] + ((L.drop (j + 1)).map Y).sum := by
      rw [hdrop, List.map_cons, List.sum_cons]
    have := hnn (L.drop (j + 1))
    have hc : (2 : ℝ) * ((j : ℕ) : ℝ) + 2 ≥ M := by
      have : 2 * j + 2 ≥ M := by omega
      exact_mod_cast this
    linarith

end LSHAux

namespace LSHAux
open Finset MeasureTheory ProbabilityTheory LocalDensityLSH.Count

set_option maxHeartbeats 1000000 in
lemma main {n t K S M : ℕ} (μ : Measure (Table n t)) [IsProbabilityMeasure μ] (I : Finset ℕ)
    (𝒜 : Finset (Fin n)) (h𝒜 : 𝒜.Nonempty) (hp : ∀ i ∈ 𝒜, 0 < p μ I i)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hK : 8 / (ε ^ 2 * pmin μ I h𝒜) ≤ (K : ℝ))
    (hS : 8 * (1 + ε ^ 2) * EC μ I / (ε ^ 2 * (𝒜.card : ℝ) * pmin μ I h𝒜) ≤ (S : ℝ))
    (hM : 11 * Real.log (1 / δ) ≤ (M : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin M → Fin K → Ω → Table n t) (X : Fin M → Fin S → Ω → Fin K × Fin n)
    (hrun : IsRun μ I P T X) :
    1 - δ ≤ P.real {ω |
      |median (fun m => estimate μ I 𝒜 (fun k => T m k ω) (fun s => X m s ω))
          - 𝒜.card| ≤ ε * 𝒜.card} := by
  have hn : 1 ≤ n := by
    obtain ⟨i, _⟩ := h𝒜
    have := i.pos; omega
  have hpm := pm_pos μ 𝒜 h𝒜 hp
  have hNpos : (0 : ℝ) < 𝒜.card := by exact_mod_cast h𝒜.card_pos
  have hEC : 0 < EC μ I := by
    obtain ⟨i, hi⟩ := h𝒜
    unfold EC
    exact lt_of_lt_of_le (hp i hi)
      (Finset.single_le_sum (f := fun j => p μ I j) (fun j _ => measureReal_nonneg) (Finset.mem_univ i))
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ hδ1)
  have hMr : (0 : ℝ) < M := by linarith
  have hM1 : 1 ≤ M := by
    have : 0 < M := by exact_mod_cast hMr
    omega
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK
    have : 0 < K := by exact_mod_cast this
    omega
  have hS1 : 1 ≤ S := by
    have : (0 : ℝ) < S := lt_of_lt_of_le (by positivity) hS
    have : 0 < S := by exact_mod_cast this
    omega
  -- one estimator fails with probability at most 1/4
  have htail : ∀ m, P.real {ω | ε * (𝒜.card : ℝ) <
      |estimate μ I 𝒜 (fun k => T m k ω) (fun s => X m s ω) - 𝒜.card|} ≤ 1 / 4 := by
    intro m
    refine run_tail μ I P (T m) (X m) (hrun.1 m) 𝒜 𝒜.card (ε * 𝒜.card) (by positivity) ?_
    have h1 := sqErr_le (K := K) (S := S) μ I 𝒜 h𝒜 hp hK1 hS1 hn
    have h2 := arith_bound (𝒜.card : ℝ) (pmin μ I h𝒜) (EC μ I) ε K S hNpos hpm hEC hε hK hS
    calc _ ≤ _ := h1
      _ ≤ ε ^ 2 * (𝒜.card : ℝ) ^ 2 / 4 := h2
      _ = (ε * 𝒜.card) ^ 2 / 4 := by ring
  -- indicators of failure
  let G : Fin M → Ω → (Fin K → Table n t) × (Fin S → Fin K × Fin n) :=
    fun m ω => ((fun k => T m k ω), (fun s => X m s ω))
  have hG : ∀ m, Measurable (G m) := fun m =>
    (measurable_pi_lambda _ (hrun.1 m).1).prodMk (measurable_pi_lambda _ (hrun.1 m).2.1)
  let Yf : Fin M → ((Fin K → Table n t) × (Fin S → Fin K × Fin n)) → ℝ :=
    fun _ z => if ε * (𝒜.card : ℝ) < |estimate μ I 𝒜 z.1 z.2 - 𝒜.card| then 1 else 0
  let Y : Fin M → Ω → ℝ := fun m => Yf m ∘ G m
  have hind : iIndepFun Y P := hrun.2.comp Yf (fun m => measurable_of_countable _)
  have hYm : ∀ m, Measurable (Y m) := fun m => (measurable_of_countable _).comp (hG m)
  have hY01 : ∀ m ω, Y m ω = if ε * (𝒜.card : ℝ) <
      |estimate μ I 𝒜 (fun k => T m k ω) (fun s => X m s ω) - 𝒜.card| then 1 else 0 :=
    fun m ω => rfl
  have hmgf : ∀ m, mgf (Y m) P (Real.log 3) ≤ 3 / 2 := by
    intro m
    have hexp : ∀ ω, Real.exp (Real.log 3 * Y m ω) = 1 + 2 * Y m ω := by
      intro ω; rw [hY01]; split_ifs
      · rw [mul_one, Real.exp_log (by norm_num)]; norm_num
      · simp
    set B : Set Ω := {ω | ε * (𝒜.card : ℝ) <
      |estimate μ I 𝒜 (fun k => T m k ω) (fun s => X m s ω) - 𝒜.card|} with hBdef
    have hY_ind : Y m = Set.indicator B 1 := by
      funext ω; rw [hY01, Set.indicator_apply]; rfl
    have hmeas : MeasurableSet B := by
      have : B = G m ⁻¹' {z | ε * (𝒜.card : ℝ) < |estimate μ I 𝒜 z.1 z.2 - 𝒜.card|} := rfl
      rw [this]; exact hG m MeasurableSet.of_discrete
    have hYint : Integrable (Y m) P := by
      rw [hY_ind]; exact (integrable_const (1 : ℝ)).indicator hmeas
    have hint_ind : ∫ ω, Y m ω ∂P = P.real B := by
      rw [hY_ind]; exact integral_indicator_one hmeas
    calc mgf (Y m) P (Real.log 3) = ∫ ω, (1 + 2 * Y m ω) ∂P := by
          unfold mgf; congr 1; funext ω; exact hexp ω
      _ = 1 + 2 * ∫ ω, Y m ω ∂P := by
          rw [integral_add (integrable_const 1) (hYint.const_mul 2), integral_const,
            integral_const_mul]
          simp
      _ ≤ 3 / 2 := by rw [hint_ind]; linarith [htail m]
  have hmgfsum : mgf (∑ m, Y m) P (Real.log 3) = ∏ m, mgf (Y m) P (Real.log 3) :=
    hind.mgf_sum hYm Finset.univ
  have hprod : ∏ m, mgf (Y m) P (Real.log 3) ≤ (3 / 2) ^ M := by
    calc ∏ m, mgf (Y m) P (Real.log 3) ≤ ∏ _m : Fin M, (3 / 2 : ℝ) :=
          Finset.prod_le_prod (fun m _ => mgf_nonneg) (fun m _ => hmgf m)
      _ = (3 / 2) ^ M := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hSum_le : ∀ ω, (∑ m, Y m) ω ≤ M := by
    intro ω
    rw [Finset.sum_apply]
    calc ∑ m, Y m ω ≤ ∑ _m : Fin M, (1 : ℝ) :=
          Finset.sum_le_sum (fun m _ => by rw [hY01]; split_ifs <;> norm_num)
      _ = M := by simp
  have hexpint : Integrable (fun ω => Real.exp (Real.log 3 * (∑ m, Y m) ω)) P := by
    refine Integrable.of_bound ?_ (Real.exp (Real.log 3 * M)) (ae_of_all _ (fun ω => ?_))
    · have hsm : Measurable (∑ m, Y m) := by
        have h := Finset.measurable_sum (f := Y) Finset.univ (fun m _ => hYm m)
        convert h using 1
        funext ω
        exact Finset.sum_apply ω _ _
      exact (Measurable.exp (measurable_const.mul hsm)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hSum_le ω) (Real.log_nonneg (by norm_num)))
  have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ m, Y m) ((M : ℝ) / 2)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)) hexpint
  have hfinal : Real.exp (-Real.log 3 * ((M : ℝ) / 2)) * (3 / 2) ^ M ≤ δ := by
    have h32 : ((3 : ℝ) / 2) ^ M = Real.exp (M * Real.log (3 / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h32, ← Real.exp_add]
    conv_rhs => rw [← Real.exp_log hδ]
    apply Real.exp_le_exp.mpr
    have hl32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
    have hl43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have h14 : 1 / 4 ≤ Real.log (4 / 3) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
      norm_num at this ⊢; linarith
    have hLd : Real.log (1 / δ) = - Real.log δ := by rw [one_div, Real.log_inv]
    have e : -Real.log 3 * ((M : ℝ) / 2) + M * Real.log (3 / 2) = -((M : ℝ) / 2) * Real.log (4 / 3) := by
      rw [hl32, hl43]; ring
    rw [e]
    have : (M : ℝ) / 2 * (1 / 4) ≤ (M : ℝ) / 2 * Real.log (4 / 3) :=
      mul_le_mul_of_nonneg_left h14 (by positivity)
    nlinarith
  have hbad : P.real {ω | (M : ℝ) / 2 ≤ (∑ m, Y m) ω} ≤ δ := by
    calc _ ≤ _ := hchern
      _ ≤ Real.exp (-Real.log 3 * ((M : ℝ) / 2)) * (3 / 2) ^ M := by
          rw [hmgfsum]; exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ ≤ δ := hfinal
  have hcover : Set.univ ⊆ {ω | |median (fun m => estimate μ I 𝒜 (fun k => T m k ω)
      (fun s => X m s ω)) - 𝒜.card| ≤ ε * 𝒜.card} ∪ {ω | (M : ℝ) / 2 ≤ (∑ m, Y m) ω} := by
    intro ω _
    by_cases hω : (M : ℝ) / 2 ≤ (∑ m, Y m) ω
    · right; exact hω
    · left
      rw [not_le] at hω
      rw [Finset.sum_apply] at hω
      exact median_good hM1 _ _ _ hω
  have h1 := measureReal_mono (μ := P) hcover
  have h2 := measureReal_union_le (μ := P)
    {ω | |median (fun m => estimate μ I 𝒜 (fun k => T m k ω)
      (fun s => X m s ω)) - 𝒜.card| ≤ ε * 𝒜.card} {ω | (M : ℝ) / 2 ≤ (∑ m, Y m) ω}
  have hU : P.real (Set.univ : Set Ω) = 1 := by simp
  linarith

end LSHAux

open LocalDensityLSH.Count MeasureTheory ProbabilityTheory in
theorem solution {n d t K S M : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1) (A : Set ℝ) (I : Finset ℕ)
    (μ : Measure (Table n t)) [IsProbabilityMeasure μ]
    (hA : (Aq v q A).Nonempty) (hp : ∀ i ∈ Aq v q A, 0 < p μ I i)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hK : 8 / (ε ^ 2 * pmin μ I hA) ≤ (K : ℝ))
    (hS : 8 * (1 + ε ^ 2) * EC μ I / (ε ^ 2 * ((Aq v q A).card : ℝ) * pmin μ I hA) ≤ (S : ℝ))
    (hM : 11 * Real.log (1 / δ) ≤ (M : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin M → Fin K → Ω → Table n t) (X : Fin M → Fin S → Ω → Fin K × Fin n)
    (hrun : IsRun μ I P T X) :
    1 - δ ≤ P.real {ω |
      |median (fun m => estimate μ I (Aq v q A) (fun k => T m k ω) (fun s => X m s ω))
          - (Aq v q A).card| ≤ ε * (Aq v q A).card} := by
  exact LSHAux.main μ I (Aq v q A) hA hp ε δ hε hδ hδ1 hK hS hM P T X hrun
