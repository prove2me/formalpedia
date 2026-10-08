-- Prove2me | solution 1 for HartSchmeidler.Finite.product_strategy_payoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:11.084377+00:00
-- url     : https://prove2.me/submissions/fb99ff2a-6691-4fdb-8d60-ffd1c57dcea5

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_HartSchmeidler_Finite_Game

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HsWork

open Finset

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]

theorem sum_update_eq (i : ι) (a : S i) (g : (∀ j, S j) → ℝ) :
    ∑ s : ∀ j, S j, g (Function.update s i a) =
      (Fintype.card (S i) : ℝ) * ∑ r ∈ Finset.univ.filter (fun r : ∀ j, S j => r i = a), g r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s => Function.update s i a)
    (t := Finset.univ.filter (fun r : ∀ j, S j => r i = a)) (fun s _ => by simp)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hri : r i = a := (Finset.mem_filter.1 hr).2
  have hfib : Finset.univ.filter (fun s : ∀ j, S j => Function.update s i a = r) =
      Finset.univ.image (fun b : S i => Function.update r i b) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hs
      refine ⟨s i, ?_⟩
      rw [← hs]; simp
    · rintro ⟨b, rfl⟩
      simp [hri]
  have hinj : Function.Injective (fun b : S i => Function.update r i b) := by
    intro b b' hbb
    have := congrFun hbb i
    simpa using this
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2]), Finset.sum_const,
    hfib, Finset.card_image_of_injective _ hinj, Finset.card_univ, nsmul_eq_mul]

theorem sum_eq_avg_update [∀ j, Nonempty (S j)] (i : ι) (f : (∀ j, S j) → ℝ) :
    ∑ r, f r = (1 / (Fintype.card (S i) : ℝ)) * ∑ s, ∑ a, f (Function.update s i a) := by
  rw [Finset.sum_comm]
  simp_rw [sum_update_eq]
  rw [← Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun r : ∀ j, S j => r i)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have : (Fintype.card (S i) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (S i) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

theorem prod_update (x : ∀ j, S j → ℝ) (i : ι) (a : S i) (s : ∀ j, S j) :
    ∏ j, x j (Function.update s i a j) = x i a * ∏ j ∈ Finset.univ.erase i, x j (s j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

end


end HsWork

open HartSchmeidler.Finite

namespace HsWork

open Finset

theorem product_strategy_payoff_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (y : Deviation S → ℝ) (hy : AGT.IsLottery y)
    (x : ∀ i, S i → ℝ) (hx : ∀ i, AGT.IsLottery (x i))
    (hbalance : ∀ (i : ι) (s : ∀ j, S j),
      ∑ r : S i, x i r * ∑ t : S i, y ⟨i, (r, t)⟩ *
        (h i (Function.update s i r) - h i (Function.update s i t)) = 0) :
    AGT.IsLottery (fun r : ∀ j, S j => ∏ j, x j (r j)) ∧
      (∑ r, ∑ c, (∏ j, x j (r j)) * y c * auxPayoff h r c) = 0 := by
  set P : (∀ j, S j) → ℝ := fun r => ∏ j, x j (r j) with hP
  constructor
  · refine ⟨fun r => Finset.prod_nonneg fun j _ => (hx j).1 _, ?_⟩
    have := Finset.prod_univ_sum (fun j => (Finset.univ : Finset (S j))) (fun j a => x j a)
    simp only [Fintype.piFinset_univ] at this
    rw [← this]
    exact Finset.prod_eq_one fun j _ => (hx j).2
  · -- reorganize by player
    have step1 : ∑ r, ∑ c, P r * y c * auxPayoff h r c =
        ∑ i, ∑ r, ∑ a, ∑ b, P r * y ⟨i, (a, b)⟩ * auxPayoff h r ⟨i, (a, b)⟩ := by
      have : ∀ r : ∀ j, S j, ∑ c : Deviation S, P r * y c * auxPayoff h r c =
          ∑ i, ∑ a, ∑ b, P r * y ⟨i, (a, b)⟩ * auxPayoff h r ⟨i, (a, b)⟩ := by
        intro r
        show ∑ c : (Σ i : ι, S i × S i), P r * y c * auxPayoff h r c = _
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_prod_type]
      simp_rw [this]
      rw [Finset.sum_comm]
    rw [step1]
    refine Finset.sum_eq_zero fun i _ => ?_
    set F : (∀ j, S j) → ℝ := fun r =>
      ∑ a, ∑ b, P r * y ⟨i, (a, b)⟩ * auxPayoff h r ⟨i, (a, b)⟩ with hF
    have hF' : ∀ r, F r = P r * ∑ b, y ⟨i, (r i, b)⟩ * (h i r - h i (Function.update r i b)) := by
      intro r
      simp only [hF]
      have : ∀ a, ∑ b, P r * y ⟨i, (a, b)⟩ * auxPayoff h r ⟨i, (a, b)⟩ =
          if r i = a then P r * ∑ b, y ⟨i, (a, b)⟩ * (h i r - h i (Function.update r i b)) else 0 := by
        intro a
        by_cases hra : r i = a
        · rw [if_pos hra, Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          have : auxPayoff h r ⟨i, (a, b)⟩ = h i r - h i (Function.update r i b) := by
            unfold auxPayoff; dsimp only; rw [if_pos hra]
          rw [this]; ring
        · rw [if_neg hra]
          refine Finset.sum_eq_zero fun b _ => ?_
          have : auxPayoff h r ⟨i, (a, b)⟩ = 0 := by
            unfold auxPayoff; dsimp only; rw [if_neg hra]
          rw [this, mul_zero]
      simp_rw [this]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    show ∑ r, F r = 0
    rw [sum_eq_avg_update i F]
    have hz : ∀ s : ∀ j, S j, ∑ a, F (Function.update s i a) = 0 := by
      intro s
      have : ∀ a, F (Function.update s i a) = (∏ j ∈ Finset.univ.erase i, x j (s j)) *
          (x i a * ∑ b, y ⟨i, (a, b)⟩ * (h i (Function.update s i a) - h i (Function.update s i b))) := by
        intro a
        rw [hF', hP]
        simp only [prod_update, Function.update_self, Function.update_idem]
        ring
      simp_rw [this]
      rw [← Finset.mul_sum, hbalance i s, mul_zero]
    simp [hz]


end HsWork

open HartSchmeidler.Finite Finset

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]
    [∀ j, Nonempty (S j)] (h : ι → (∀ j, S j) → ℝ)
    (y : Deviation S → ℝ) (hy : AGT.IsLottery y)
    (x : ∀ i, S i → ℝ) (hx : ∀ i, AGT.IsLottery (x i))
    (hbalance : ∀ (i : ι) (s : ∀ j, S j),
      ∑ r : S i, x i r * ∑ t : S i, y ⟨i, (r, t)⟩ *
        (h i (Function.update s i r) - h i (Function.update s i t)) = 0) :
    AGT.IsLottery (fun r : ∀ j, S j => ∏ j, x j (r j)) ∧
      (∑ r, ∑ c, (∏ j, x j (r j)) * y c * auxPayoff h r c) = 0 :=
  HsWork.product_strategy_payoff_zero h y hy x hx hbalance

#print axioms solution
