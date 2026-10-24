-- Prove2me | solution 1 for HiringLP.Parallel.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:23:45.339979+00:00
-- url     : https://prove2.me/submissions/0406f3b3-828a-46a9-88e8-41a2e983e691

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

open HiringLP.Parallel Finset

namespace HLP2L8

variable {n k : ℕ}

/-- weight of the outcome `S` for independent Bernoulli(`x i`), `i ∈ U` -/
def w (x : Fin n → ℝ) (U S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ U, if i ∈ S then x i else 1 - x i

lemma w_insert_out (x : Fin n → ℝ) (a : Fin n) (U S : Finset (Fin n)) (ha : a ∉ U)
    (hS : S ⊆ U) : w x (insert a U) S = (1 - x a) * w x U S := by
  unfold w
  rw [Finset.prod_insert ha, if_neg (fun h => ha (hS h))]

lemma w_insert_in (x : Fin n → ℝ) (a : Fin n) (U S : Finset (Fin n)) (ha : a ∉ U) :
    w x (insert a U) (insert a S) = x a * w x U S := by
  unfold w
  rw [Finset.prod_insert ha, if_pos (Finset.mem_insert_self a S)]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hne : i ≠ a := fun h => ha (h ▸ hi)
  simp [Finset.mem_insert, hne]

lemma sum_insert_split (x : Fin n → ℝ) (a : Fin n) (U : Finset (Fin n)) (ha : a ∉ U)
    (g : Finset (Fin n) → ℝ) :
    ∑ S ∈ (insert a U).powerset, g S =
      ∑ S ∈ U.powerset, g S + ∑ S ∈ U.powerset, g (insert a S) := by
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    intro S hS T hT h
    have hS' : a ∉ S := fun h' => ha (Finset.mem_powerset.mp hS h')
    have hT' : a ∉ T := fun h' => ha (Finset.mem_powerset.mp hT h')
    have := congrArg (fun Z => Z.erase a) h
    simpa [Finset.erase_insert hS', Finset.erase_insert hT'] using this
  · rw [Finset.disjoint_left]
    intro S hS hS2
    obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp hS2
    exact ha (Finset.mem_powerset.mp hS (Finset.mem_insert_self a T))

lemma w_sum_one (x : Fin n → ℝ) (U : Finset (Fin n)) :
    ∑ S ∈ U.powerset, w x U S = 1 := by
  induction U using Finset.induction_on with
  | empty => simp [w]
  | insert a U ha ih =>
    rw [sum_insert_split x a U ha]
    rw [Finset.sum_congr rfl (fun S hS => w_insert_out x a U S ha (Finset.mem_powerset.mp hS)),
      Finset.sum_congr rfl (fun S _ => w_insert_in x a U S ha), ← Finset.mul_sum,
      ← Finset.mul_sum, ih]
    ring

lemma w_nonneg (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (U S : Finset (Fin n)) :
    0 ≤ w x U S := by
  unfold w
  refine Finset.prod_nonneg (fun i _ => ?_)
  split_ifs
  · exact (hx i).1
  · linarith [(hx i).2]

lemma vstar_nonneg (I : Instance n k) (j : Fin k) (hv : ∀ i, 0 ≤ I.v i j) (S : Finset (Fin n)) :
    0 ≤ vstar I j S := by
  unfold vstar
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact le_trans (hv i) (Finset.le_sup' (fun i => I.v i j) hi)
  · exact le_refl 0

lemma vstar_insert_max (I : Instance n k) (j : Fin k) (a : Fin n) (S : Finset (Fin n))
    (hmax : ∀ i ∈ S, I.v i j ≤ I.v a j) : vstar I j (insert a S) = I.v a j := by
  unfold vstar
  rw [dif_pos (Finset.insert_nonempty a S)]
  refine le_antisymm (Finset.sup'_le _ _ (fun i hi => ?_))
    (Finset.le_sup' (fun i => I.v i j) (Finset.mem_insert_self a S))
  rcases Finset.mem_insert.mp hi with h | h
  · rw [h]
  · exact hmax i h

/-- `s_U · E[v*(D̃ ∩ U)] ≥ (1 - e^{-s_U}) Σ_{i∈U} v_i x_i`, with `s_U = Σ_{i∈U} x_i`. -/
lemma key (I : Instance n k) (j : Fin k) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hv : ∀ i, 0 ≤ I.v i j) (U : Finset (Fin n)) :
    0 ≤ ∑ S ∈ U.powerset, w x U S * vstar I j S ∧
    (1 - Real.exp (-(∑ i ∈ U, x i))) * (∑ i ∈ U, I.v i j * x i) ≤
      (∑ i ∈ U, x i) * ∑ S ∈ U.powerset, w x U S * vstar I j S := by
  induction U using Finset.induction_on_max_value (fun i => I.v i j) with
  | empty => simp [w, vstar]
  | insert a U ha hmax ih =>
    obtain ⟨hF0, hF⟩ := ih
    set F := ∑ S ∈ U.powerset, w x U S * vstar I j S with hFdef
    set s := ∑ i ∈ U, x i with hsdef
    set W := ∑ i ∈ U, I.v i j * x i with hWdef
    have hrec : ∑ S ∈ (insert a U).powerset, w x (insert a U) S * vstar I j S
        = x a * I.v a j + (1 - x a) * F := by
      rw [sum_insert_split x a U ha]
      have e1 : ∑ S ∈ U.powerset, w x (insert a U) S * vstar I j S = (1 - x a) * F := by
        rw [hFdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S hS => ?_)
        rw [w_insert_out x a U S ha (Finset.mem_powerset.mp hS)]; ring
      have e2 : ∑ S ∈ U.powerset, w x (insert a U) (insert a S) * vstar I j (insert a S)
          = x a * I.v a j := by
        have : ∀ S ∈ U.powerset, w x (insert a U) (insert a S) * vstar I j (insert a S)
            = x a * I.v a j * w x U S := by
          intro S hS
          rw [w_insert_in x a U S ha,
            vstar_insert_max I j a S (fun i hi => hmax i (Finset.mem_powerset.mp hS hi))]
          ring
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, w_sum_one, mul_one]
      rw [e1, e2]; ring
    rw [hrec, Finset.sum_insert ha, Finset.sum_insert ha]
    rw [← hsdef, ← hWdef]
    have hxa := hx a
    have hva := hv a
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => (hx i).1)
    have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hx i).1)
    have hWle : W ≤ I.v a j * s := by
      rw [hsdef, hWdef, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hmax i hi) (hx i).1)
    refine ⟨by nlinarith, ?_⟩
    -- exponential facts
    have hEa : 1 - x a ≤ Real.exp (-x a) := by
      have := Real.add_one_le_exp (-x a); linarith
    have hE' : 0 < Real.exp (-s) := Real.exp_pos _
    have hEs : Real.exp (-(x a + s)) = Real.exp (-s) * Real.exp (-x a) := by
      rw [← Real.exp_add]; ring_nf
    have hlin : 1 - Real.exp (-(x a + s)) ≤ x a + s := by
      have := Real.add_one_le_exp (-(x a + s)); linarith
    have hE'le : Real.exp (-s) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    rw [hEs] at hlin ⊢
    set E' := Real.exp (-s)
    set ex := Real.exp (-x a)
    rcases eq_or_lt_of_le hs0 with hs | hs
    · -- s = 0, so W = 0
      have hW : W = 0 := by
        rw [← hs] at hWle; simp at hWle; linarith
      rw [← hs, hW]
      rw [← hs] at hlin
      nlinarith [mul_nonneg (mul_nonneg hxa.1 (sub_nonneg.mpr hxa.2)) hF0,
        mul_nonneg hxa.1 hva]
    · -- s > 0: multiply through by s
      have hF' : (1 - x a) * (x a + s) * ((1 - E') * W) ≤ (1 - x a) * (x a + s) * (s * F) :=
        mul_le_mul_of_nonneg_left hF
          (mul_nonneg (sub_nonneg.mpr hxa.2) (by linarith))
      -- affine function of W
      set c := (1 - x a) * (x a + s) * (1 - E') - s * (1 - E' * ex) with hc
      have hf0 : 0 ≤ s * x a * I.v a j * ((x a + s) - (1 - E' * ex)) := by
        have : 0 ≤ (x a + s) - (1 - E' * ex) := by linarith
        exact mul_nonneg (mul_nonneg (mul_nonneg hs.le hxa.1) hva) this
      have hfmax : 0 ≤ s * x a * I.v a j * ((x a + s) - (1 - E' * ex))
          + c * (I.v a j * s) := by
        have h1 : s * x a * I.v a j * ((x a + s) - (1 - E' * ex)) + c * (I.v a j * s)
            = s * I.v a j * (x a + s) * (E' * (ex - (1 - x a))) := by
          rw [hc]; ring
        rw [h1]
        have : 0 ≤ E' * (ex - (1 - x a)) := mul_nonneg hE'.le (by linarith)
        have : 0 ≤ s * I.v a j * (x a + s) := by
          have : 0 ≤ x a + s := by linarith
          exact mul_nonneg (mul_nonneg hs.le hva) this
        exact mul_nonneg this (by assumption)
      have hfW : 0 ≤ s * x a * I.v a j * ((x a + s) - (1 - E' * ex)) + c * W := by
        rcases le_or_gt 0 c with hc0 | hc0
        · nlinarith
        · nlinarith
      have goal_s : s * ((1 - E' * ex) * (I.v a j * x a + W)) ≤
          s * ((x a + s) * (x a * I.v a j + (1 - x a) * F)) := by
        nlinarith
      exact le_of_mul_le_mul_left goal_s hs

end HLP2L8

open HLP2L8 in
theorem solution {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y) (j : Fin k) :
    (1 - Real.exp (-1)) * Lstar I y j ≤ EvDtilde I y j := by
  classical
  set x : Fin n → ℝ := fun i => y i j * I.p i j with hxdef
  have hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
    intro i
    obtain ⟨hp0, hp1⟩ := hI.2.2.2.1 i j
    obtain ⟨hy0, hy1⟩ := hy.2.2.2 i j
    exact ⟨mul_nonneg hy0 hp0, by nlinarith⟩
  have hv : ∀ i, 0 ≤ I.v i j := fun i => hI.2.2.2.2 i j
  have hsum : ∑ i, x i ≤ 1 := hy.2.1 j
  have hE : EvDtilde I y j = ∑ S ∈ (univ : Finset (Fin n)).powerset, w x univ S * vstar I j S := by
    rw [Finset.powerset_univ]; rfl
  have hL : Lstar I y j = ∑ i, I.v i j * x i := by
    unfold Lstar; refine Finset.sum_congr rfl (fun i _ => ?_); simp only [hxdef]; ring
  obtain ⟨hF0, hF⟩ := key I j x hx hv univ
  rw [hE, hL]
  set F := ∑ S ∈ (univ : Finset (Fin n)).powerset, w x univ S * vstar I j S
  set s := ∑ i, x i
  set W := ∑ i, I.v i j * x i
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => (hx i).1)
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hx i).1)
  -- concavity: (1 - e^{-1}) s ≤ 1 - e^{-s} on [0,1]
  have hconc : (1 - Real.exp (-1)) * s ≤ 1 - Real.exp (-s) := by
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (show 0 ≤ 1 - s by linarith) hs0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have : s * -1 = -s := by ring
    rw [this] at hc
    linarith
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- all x i = 0, so W = 0
    have hx0 : ∀ i, x i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hx i).1)).mp hs.symm i (mem_univ i)
      exact this
    have hW : W = 0 := Finset.sum_eq_zero (fun i _ => by rw [hx0 i, mul_zero])
    rw [hW, mul_zero]; exact hF0
  · have h1 : (1 - Real.exp (-1)) * s * W ≤ s * F := by
      calc (1 - Real.exp (-1)) * s * W ≤ (1 - Real.exp (-s)) * W :=
            mul_le_mul_of_nonneg_right hconc hW0
        _ ≤ s * F := hF
    have h2 : s * ((1 - Real.exp (-1)) * W) ≤ s * F := by linarith
    exact le_of_mul_le_mul_left h2 hs
