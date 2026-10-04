-- Prove2me | solution 1 for IncentivesInTeams.Conglomerate.cond_expectation_factorizes
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T12:42:45.56239+00:00
-- url     : https://prove2.me/submissions/f937e2af-f162-48cf-a8b7-67bd7c645e56

import Definitions.Def_IncentivesInTeams_Conglomerate_Model

open IncentivesInTeams.Conglomerate Finset

namespace OwnProfitFactorization

open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S₀ : Type*} [Fintype S₀] {S : ι → Type*} [∀ i, Fintype (S i)]

private theorem sum_product (w₀ : S₀ → ℝ) (w : ∀ i, S i → ℝ) :
    (∑ s : S₀ × ∀ i, S i, w₀ s.1 * ∏ i, w i (s.2 i)) =
      (∑ t, w₀ t) * ∏ i, ∑ t, w i t := by
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sum, ← Fintype.prod_sum]
  rw [sum_mul]

private theorem prod_coordinate (w : ∀ i, S i → ℝ) (j : ι) (f : S j → ℝ)
    (s : ∀ i, S i) :
    (∏ i, w i (s i)) * f (s j) =
      ∏ i, (Function.update w j (fun t => w j t * f t)) i (s i) := by
  rw [← mul_prod_erase univ (fun i => w i (s i)) (mem_univ j),
    ← mul_prod_erase univ (fun i => (Function.update w j (fun t => w j t * f t)) i (s i))
      (mem_univ j)]
  simp only [Function.update_self]
  have he : (∏ i ∈ univ.erase j,
      (Function.update w j (fun t => w j t * f t)) i (s i)) =
      ∏ i ∈ univ.erase j, w i (s i) := by
    apply prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (mem_erase.mp hi).1]
  rw [he]
  ring

private theorem sum_sub (w₀ : S₀ → ℝ) (w : ∀ i, S i → ℝ) (j : ι) (f : S j → ℝ) :
    (∑ s : S₀ × ∀ i, S i, (w₀ s.1 * ∏ i, w i (s.2 i)) * f (s.2 j)) =
      (∑ t, w₀ t) * ((∑ t, w j t * f t) * ∏ i ∈ univ.erase j, ∑ t, w i t) := by
  simp_rw [mul_assoc, prod_coordinate]
  rw [sum_product]
  congr 1
  rw [← mul_prod_erase univ
    (fun i => ∑ t, (Function.update w j (fun t => w j t * f t)) i t) (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro i hi
  simp only [Function.update_of_ne (mem_erase.mp hi).1]

private theorem sum_head (w₀ : S₀ → ℝ) (w : ∀ i, S i → ℝ) (f : S₀ → ℝ) :
    (∑ s : S₀ × ∀ i, S i, (w₀ s.1 * ∏ i, w i (s.2 i)) * f s.1) =
      (∑ t, w₀ t * f t) * ∏ i, ∑ t, w i t := by
  convert sum_product (fun t => w₀ t * f t) w using 1
  apply sum_congr rfl
  intro s _
  ring

variable {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}

private theorem headInfo_eq_iff (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D)
    (s : S₀ × ∀ i, S i) (y : Z₀ × ∀ i, M i) :
    β.headInfo s = y ↔ β.head.obs s.1 = y.1 ∧
      ∀ i, (β.sub i).msg ((β.sub i).obs (s.2 i), β.head.msg i y.1) = y.2 i := by
  constructor
  · intro h
    have h₀ : β.head.obs s.1 = y.1 := congrArg Prod.fst h
    refine ⟨h₀, fun i => ?_⟩
    simpa only [JointStrategy.headInfo, JointStrategy.subInfo, h₀] using
      congrFun (congrArg Prod.snd h) i
  · rintro ⟨h₀, h⟩
    apply Prod.ext h₀
    funext i
    simpa only [JointStrategy.headInfo, JointStrategy.subInfo, h₀] using h i

private theorem masked_prob (T : Model S₀ S Z₀ Z M₀ M D₀ D)
    (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (y : Z₀ × ∀ i, M i)
    (s : S₀ × ∀ i, S i) :
    (if β.headInfo s = y then T.prob s else 0) =
      (if β.head.obs s.1 = y.1 then T.P₀ s.1 else 0) *
        ∏ i, if (β.sub i).msg ((β.sub i).obs (s.2 i), β.head.msg i y.1) = y.2 i
          then T.P i (s.2 i) else 0 := by
  classical
  simp only [headInfo_eq_iff, Fintype.prod_ite_zero]
  by_cases h₀ : β.head.obs s.1 = y.1 <;> simp [h₀, Model.prob, mul_ite]

private theorem fiber_sum (T : Model S₀ S Z₀ Z M₀ M D₀ D)
    (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (y : Z₀ × ∀ i, M i)
    (X : (S₀ × ∀ i, S i) → ℝ) :
    (∑ s ∈ univ.filter (fun s => β.headInfo s = y), T.prob s * X s) =
      ∑ s, ((if β.head.obs s.1 = y.1 then T.P₀ s.1 else 0) *
        ∏ i, if (β.sub i).msg ((β.sub i).obs (s.2 i), β.head.msg i y.1) = y.2 i
          then T.P i (s.2 i) else 0) * X s := by
  rw [sum_filter]
  apply sum_congr rfl
  intro s _
  rw [← masked_prob]
  split_ifs <;> simp

end OwnProfitFactorization

open OwnProfitFactorization

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀]
    {S : ι → Type*} [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*}
    {D₀ : Type*} {D : ι → Type*} (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (y₀ : Z₀ × ∀ k, M k)
    (hpos : 0 < T.expect (Set.indicator {s | βs.headInfo s = y₀} (fun _ => (1 : ℝ)))) :
    (∀ j, T.literalSubCondExp βs j y₀ = T.subFactor βs j y₀) ∧
      T.literalHeadCondExp βs y₀ = T.headFactor βs y₀ := by
  classical
  let w₀ : S₀ → ℝ := fun t => if βs.head.obs t = y₀.1 then T.P₀ t else 0
  let w : ∀ i, S i → ℝ := fun i t =>
    if (βs.sub i).msg ((βs.sub i).obs t, βs.head.msg i y₀.1) = y₀.2 i then T.P i t else 0
  let a₀ : ℝ := ∑ t, w₀ t
  let a : ι → ℝ := fun i => ∑ t, w i t
  let d : ℝ := ∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀), T.prob s
  have hd : d = a₀ * ∏ i, a i := by
    have h := fiber_sum T βs y₀ (fun _ => 1)
    simp only [mul_one] at h
    exact h.trans (sum_product w₀ w)
  have hdp : 0 < d := by
    simpa only [Model.expect, Set.indicator, Set.mem_setOf_eq, mul_ite, mul_one,
      mul_zero, ← sum_filter] using hpos
  have hdne : a₀ * ∏ i, a i ≠ 0 := hd ▸ ne_of_gt hdp
  constructor
  · intro j
    let f : S j → ℝ := fun t => T.v j
      ((βs.sub j).dec ((βs.sub j).obs t, βs.head.msg j y₀.1)) (βs.head.dec y₀) t
    have hn : (∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀),
        T.prob s * T.subPayoff βs j s) =
        a₀ * ((∑ t, w j t * f t) * ∏ i ∈ univ.erase j, a i) := by
      calc
        _ = ∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀), T.prob s * f (s.2 j) := by
          apply sum_congr rfl
          intro s hs
          have he := (mem_filter.mp hs).2
          have h₀ : βs.head.obs s.1 = y₀.1 := congrArg Prod.fst he
          simp only [Model.subPayoff, JointStrategy.subInfo, he, h₀, f]
        _ = _ := (fiber_sum T βs y₀ (fun s => f (s.2 j))).trans (sum_sub w₀ w j f)
    have hf : T.subFactor βs j y₀ = (∑ t, w j t * f t) / a j := by
      simp only [Model.subFactor, condAvg, Set.mem_setOf_eq, sum_filter, a, w, f,
        ite_mul, zero_mul]
    have hds : a₀ * ∏ i, a i = a j * (a₀ * ∏ i ∈ univ.erase j, a i) := by
      rw [← mul_prod_erase univ a (mem_univ j)]
      ring
    have hc : a₀ * ∏ i ∈ univ.erase j, a i ≠ 0 :=
      (mul_ne_zero_iff.mp (hds ▸ hdne)).2
    simp only [Model.literalSubCondExp, condAvg, Set.mem_ofPred_eq]
    change (∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀),
      T.prob s * T.subPayoff βs j s) / d = _
    rw [hn, hd, hds, hf]
    calc
      _ = ((∑ t, w j t * f t) * (a₀ * ∏ i ∈ univ.erase j, a i)) /
          (a j * (a₀ * ∏ i ∈ univ.erase j, a i)) := by ring
      _ = _ := mul_div_mul_right _ _ hc
  · let f : S₀ → ℝ := fun t => T.v₀ (βs.head.dec y₀) t
    have hn : (∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀),
        T.prob s * T.headPayoff βs s) = (∑ t, w₀ t * f t) * ∏ i, a i := by
      calc
        _ = ∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀), T.prob s * f s.1 := by
          apply sum_congr rfl
          intro s hs
          simp only [Model.headPayoff, (mem_filter.mp hs).2, f]
        _ = _ := (fiber_sum T βs y₀ (fun s => f s.1)).trans (sum_head w₀ w f)
    have hf : T.headFactor βs y₀ = (∑ t, w₀ t * f t) / a₀ := by
      simp only [Model.headFactor, condAvg, Set.mem_setOf_eq, sum_filter, a₀, w₀, f,
        ite_mul, zero_mul]
    simp only [Model.literalHeadCondExp, condAvg, Set.mem_ofPred_eq]
    change (∑ s ∈ univ.filter (fun s => βs.headInfo s = y₀),
      T.prob s * T.headPayoff βs s) / d = _
    rw [hn, hd, hf]
    exact mul_div_mul_right _ _ (mul_ne_zero_iff.mp hdne).2
