-- Prove2me | solution 1 for NarrowDNF.Approx.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:26.244827+00:00
-- url     : https://prove2.me/submissions/9d79c10f-105a-492b-9e46-7198affe7b05

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Shifts

section
set_option autoImplicit false
namespace NarrowDNF.Dev.L31
open NarrowDNF.Approx

noncomputable def wt {n : ℕ} (p : ℝ) (x : Cube n) : ℝ := ∏ i : Fin n, FriedgutCoalition.bern p (x i)

lemma prob_eq {n : ℕ} (p : ℝ) (E : Cube n → Prop) [DecidablePred E] :
    prob p E = ∑ x : Cube n, if E x then wt p x else 0 := by
  unfold prob FriedgutCoalition.wProb wt
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : E x <;> simp [h]

/-- sum over x with x i = false, adding the true partner -/
lemma sum_split {n : ℕ} (i : Fin n) (F : Cube n → ℝ) :
    ∑ x : Cube n, F x = ∑ x : Cube n,
      (if x i = false then F x + F (Function.update x i true) else 0) := by
  have h1 : ∑ x : Cube n, F x = ∑ x : Cube n, (if x i = false then F x else 0)
      + ∑ x : Cube n, (if x i = true then F x else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    cases h : x i <;> simp [h]
  have h2 : ∑ x : Cube n, (if x i = true then F x else 0)
      = ∑ x : Cube n, (if x i = false then F (Function.update x i true) else 0) := by
    let e : Cube n ≃ Cube n :=
      { toFun := fun x => Function.update x i (!x i)
        invFun := fun x => Function.update x i (!x i)
        left_inv := fun x => by
          funext j; by_cases h : j = i
          · subst h; simp
          · simp [Function.update_of_ne h]
        right_inv := fun x => by
          funext j; by_cases h : j = i
          · subst h; simp
          · simp [Function.update_of_ne h] }
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    cases h : x i <;> simp [e, h]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : x i = false <;> simp [h]

noncomputable def rest {n : ℕ} (p : ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, FriedgutCoalition.bern p (x j)

lemma wt_update {n : ℕ} (p : ℝ) (i : Fin n) (x : Cube n) (b : Bool) :
    wt p (Function.update x i b) = FriedgutCoalition.bern p b * rest p i x := by
  unfold wt rest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

noncomputable def ind (a b : Bool) : ℝ := if a ≠ b then 1 else 0

lemma error_split {n : ℕ} (p : ℝ) (i : Fin n) (f g : Cube n → Bool) :
    error p f g = ∑ x : Cube n, if x i = false then
      rest p i x * ((1 - p) * ind (f (Function.update x i false)) (g (Function.update x i false))
        + p * ind (f (Function.update x i true)) (g (Function.update x i true))) else 0 := by
  classical
  unfold error
  rw [prob_eq, sum_split i]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : x i = false
  · have hx : Function.update x i false = x := by simpa using h
    have := wt_update p i x true
    have h0 : wt p x = (1 - p) * rest p i x := by
      have := wt_update p i x false
      rwa [hx] at this
    simp only [h, if_true, ind, hx, h0, this, FriedgutCoalition.bern]
    by_cases h1 : f x = g x <;> by_cases h2 : f (Function.update x i true) = g (Function.update x i true) <;>
      simp [h1, h2] <;> ring
  · simp [h]

lemma upper_f {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) :
    upper i v (Function.update x i false) = v (Function.update x i false) := by
  simp [upper]

lemma upper_t {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) :
    upper i v (Function.update x i true) =
      (v (Function.update x i false) || v (Function.update x i true)) := by
  simp [upper]

lemma lower_f {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) :
    lower i v (Function.update x i false) =
      (v (Function.update x i false) && v (Function.update x i true)) := by
  simp [lower]

lemma lower_t {n : ℕ} (i : Fin n) (v : Cube n → Bool) (x : Cube n) :
    lower i v (Function.update x i true) = v (Function.update x i true) := by
  simp [lower]

lemma pt_ineq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f0 f1 v0 v1 : Bool) (hf : f0 ≤ f1) :
    (1 - p) * ((1 - p) * ind f0 v0 + p * ind f1 (v0 || v1)) +
      p * ((1 - p) * ind f0 (v0 && v1) + p * ind f1 v1)
    ≤ (1 - p) * ind f0 v0 + p * ind f1 v1 := by
  have hq : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have key : ind f1 (v0 || v1) + ind f0 (v0 && v1) ≤ ind f0 v0 + ind f1 v1 := by
    revert hf; cases f0 <;> cases f1 <;> cases v0 <;> cases v1 <;> simp [ind]
  nlinarith


end NarrowDNF.Dev.L31

namespace NarrowDNF.Approx
open NarrowDNF.Dev.L31 in
theorem chk_lemma_3_1 {n : ℕ} (p : ℝ) (i : Fin n) (f v : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (hf : Monotone f) :
    (1 - p) * error p f (upper i v) + p * error p f (lower i v) ≤ error p f v ∧
    CoordinateMonotone (upper i v) i ∧ CoordinateMonotone (lower i v) i ∧
    (∀ j : Fin n, j ≠ i → CoordinateMonotone v j →
      CoordinateMonotone (upper i v) j ∧ CoordinateMonotone (lower i v) j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [error_split p i f (upper i v), error_split p i f (lower i v), error_split p i f v,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun x _ => ?_)
    by_cases h : x i = false
    · simp only [h, if_true, upper_f, upper_t, lower_f, lower_t]
      have hr : 0 ≤ rest p i x := Finset.prod_nonneg (fun j _ => by
        simp only [FriedgutCoalition.bern]; split_ifs <;> linarith)
      have hm : f (Function.update x i false) ≤ f (Function.update x i true) :=
        hf (fun j => by
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj])
      have := pt_ineq p hp hp_one _ _ (v (Function.update x i false))
        (v (Function.update x i true)) hm
      have := mul_le_mul_of_nonneg_left this hr
      nlinarith
    · simp [h]
  · intro x
    rw [upper_f, upper_t]
    generalize v (Function.update x i false) = a
    generalize v (Function.update x i true) = b
    revert a b; decide
  · intro x
    rw [lower_f, lower_t]
    generalize v (Function.update x i false) = a
    generalize v (Function.update x i true) = b
    revert a b; decide
  · intro j hj hv
    have hij : i ≠ j := fun h => hj h.symm
    have hc : ∀ (y : Cube n) (b c : Bool), v (Function.update (Function.update y j b) i c)
        = v (Function.update (Function.update y i c) j b) := fun y b c => by
      rw [Function.update_comm hij]
    constructor
    · intro x
      unfold upper
      simp only [Function.update_of_ne hij]
      by_cases hx : x i = true
      · simp only [hx, if_true, hc]
        have h1 := hv (Function.update x i false)
        have h2 := hv (Function.update x i true)
        revert h1 h2
        generalize v (Function.update (Function.update x i false) j false) = a1
        generalize v (Function.update (Function.update x i false) j true) = a2
        generalize v (Function.update (Function.update x i true) j false) = b1
        generalize v (Function.update (Function.update x i true) j true) = b2
        revert a1 a2 b1 b2; decide
      · simp only [hx, if_false, hc]
        exact hv _
    · intro x
      unfold lower
      simp only [Function.update_of_ne hij]
      by_cases hx : x i = true
      · simp only [hx, if_true, hc]
        exact hv _
      · simp only [hx, if_false, hc]
        have h1 := hv (Function.update x i false)
        have h2 := hv (Function.update x i true)
        revert h1 h2
        generalize v (Function.update (Function.update x i false) j false) = a1
        generalize v (Function.update (Function.update x i false) j true) = a2
        generalize v (Function.update (Function.update x i true) j false) = b1
        generalize v (Function.update (Function.update x i true) j true) = b2
        revert a1 a2 b1 b2; decide

end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_lemma_3_1 := @NarrowDNF.Approx.chk_lemma_3_1
