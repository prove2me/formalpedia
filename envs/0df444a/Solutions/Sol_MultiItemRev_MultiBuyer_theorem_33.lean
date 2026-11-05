-- Prove2me | solution 1 for MultiItemRev.MultiBuyer.theorem_33
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:53:19.173187+00:00
-- url     : https://prove2.me/submissions/d89ba644-4c06-4184-8e43-0d2217b73a2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Theorems.Thm_MultiItemRev_MultiBuyer_remark_b_npt_ds
import Theorems.Thm_MultiItemRev_MultiBuyer_display_19

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.MultiBuyer in
theorem solution (n : ℕ) (hn : 1 ≤ n) (μY μZ : Measure (Fin n → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    (1 / 2 : ℝ≥0∞) * RevDS (twoGoodsN μY μZ) ≤ RevDS (oneGoodN μY) + RevDS (oneGoodN μZ) := by
  classical
  -- the swap of the two goods
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let σ : (Fin n → Fin 2 → ℝ≥0) → (Fin n → Fin 2 → ℝ≥0) := fun x j i => x j (e i)
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x; funext j i; simp [σ, e]
  have hσm : Measurable σ := by
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
    exact (measurable_pi_apply (e i)).comp (measurable_pi_apply j)
  let σE : (Fin n → Fin 2 → ℝ≥0) ≃ᵐ (Fin n → Fin 2 → ℝ≥0) :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ,
      measurable_toFun := hσm, measurable_invFun := hσm }
  have hg : ∀ (ν : Measure (Fin n → ℝ≥0)) (ν' : Measure (Fin n → ℝ≥0)),
      Measurable (fun p : (Fin n → ℝ≥0) × (Fin n → ℝ≥0) => fun j => ![p.1 j, p.2 j]) := by
    intro _ _
    refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => ?_
    fin_cases i
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact (measurable_pi_apply j).comp measurable_snd
  have hswapLaw : twoGoodsN μZ μY = (twoGoodsN μY μZ).map σ := by
    rw [twoGoodsN, twoGoodsN, Measure.map_map hσm (hg μY μZ), ← Measure.prod_swap,
      Measure.map_map (hg μY μZ) measurable_swap]
    congr 1
    funext p j i
    fin_cases i <;> simp [σ, e]
  -- the swapped mechanism
  let swapMech : MechanismN n (Fin 2) → MechanismN n (Fin 2) := fun M =>
    { q := fun x j i => M.q (σ x) j (e i)
      s := fun x j => M.s (σ x) j }
  have hupd : ∀ (x : Fin n → Fin 2 → ℝ≥0) j (x' : Fin 2 → ℝ≥0),
      σ (Function.update x j x') = Function.update (σ x) j (fun i => x' (e i)) := by
    intro x j x'
    funext l i
    by_cases h : l = j
    · subst h; simp [σ]
    · simp [σ, Function.update_of_ne h]
  have hsum : ∀ (M : MechanismN n (Fin 2)) (y x : Fin n → Fin 2 → ℝ≥0) j,
      ∑ i, (swapMech M).q y j i * (x j i : ℝ) = ∑ i, M.q (σ y) j i * ((σ x) j i : ℝ) := by
    intro M y x j
    simp only [swapMech]
    rw [← Equiv.sum_comp e]
    simp [σ, e]
  have hpaySwap : ∀ (M : MechanismN n (Fin 2)) x j, payoffN (swapMech M) x j = payoffN M (σ x) j := by
    intro M x j
    simp only [payoffN]
    rw [hsum]
  have hadmSwap : ∀ M : MechanismN n (Fin 2), IsAdmissibleDS M → IsNPTN M →
      IsAdmissibleDS (swapMech M) ∧ IsNPTN (swapMech M) := by
    intro M hM hN
    refine ⟨⟨⟨fun x j i => hM.1.1 (σ x) j (e i), fun x i => hM.1.2 (σ x) (e i)⟩, ?_, ?_, ?_⟩, ?_⟩
    · intro x j x'
      rw [hpaySwap, hsum]
      have h := hM.2.1 (σ x) j (fun i => x' (e i))
      simp only [swapMech]
      rw [hupd]
      exact h
    · intro x j
      rw [hpaySwap]; exact hM.2.2.1 _ _
    · intro j
      exact (hM.2.2.2 j).comp hσm
    · intro x j; exact hN _ _
  have hrevSwap : ∀ (M : MechanismN n (Fin 2)) x, sellerRevenue (swapMech M) x = sellerRevenue M (σ x) := by
    intro M x; rfl
  -- measurability of `maxCoord`
  have hmax : Measurable (fun a : Fin n → ℝ≥0 => maxCoord a) := by
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have : (fun a : Fin n → ℝ≥0 => maxCoord a) =
        (Finset.univ.sup' hne (fun j (a : Fin n → ℝ≥0) => a j)) := by
      funext a
      rw [Finset.sup'_apply, maxCoord, ← Finset.sup'_eq_sup hne]
    rw [this]
    exact Finset.measurable_sup' hne fun j _ => measurable_pi_apply j
  have hmaxi : ∀ i : Fin 2, Measurable (fun x : Fin n → Fin 2 → ℝ≥0 => maxCoord (fun j => x j i)) :=
    fun i => hmax.comp (measurable_pi_lambda _ fun j => (measurable_pi_apply i).comp (measurable_pi_apply j))
  let A : Set (Fin n → Fin 2 → ℝ≥0) := {x | maxCoord (fun j => x j 1) ≤ maxCoord (fun j => x j 0)}
  let B : Set (Fin n → Fin 2 → ℝ≥0) := {x | maxCoord (fun j => x j 0) ≤ maxCoord (fun j => x j 1)}
  have hAm : MeasurableSet A := measurableSet_le (hmaxi 1) (hmaxi 0)
  have hAB : σ ⁻¹' A = B := by
    ext x; simp [A, B, σ, e]
  -- main bound for an NPT mechanism
  have key : ∀ M : MechanismN n (Fin 2), IsAdmissibleDS M → IsNPTN M →
      (expRevenueN (twoGoodsN μY μZ) M).toENNReal ≤
        2 * RevDS (oneGoodN μY) + 2 * RevDS (oneGoodN μZ) := by
    intro M hM hN
    have hS0 : ∀ x, 0 ≤ sellerRevenue M x := fun x =>
      Finset.sum_nonneg fun j _ => hN x j
    have hneg : ∫⁻ x, ENNReal.ofReal (-sellerRevenue M x) ∂(twoGoodsN μY μZ) = 0 := by
      have : (fun x => ENNReal.ofReal (-sellerRevenue M x)) = fun _ => 0 := by
        funext x; exact ENNReal.ofReal_of_nonpos (by linarith [hS0 x])
      rw [this, lintegral_zero]
    have hSm : Measurable (fun x => ENNReal.ofReal (sellerRevenue M x)) :=
      (Finset.measurable_sum _ fun j _ => hM.2.2.2 j).ennreal_ofReal
    rw [expRevenueN, hneg]
    simp only [EReal.coe_ennreal_zero, sub_zero, EReal.toENNReal_coe]
    have hunion : A ∪ B = Set.univ := by
      ext x; simp only [A, B, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_total _ _
    calc ∫⁻ x, ENNReal.ofReal (sellerRevenue M x) ∂(twoGoodsN μY μZ)
        = ∫⁻ x in A ∪ B, ENNReal.ofReal (sellerRevenue M x) ∂(twoGoodsN μY μZ) := by
          rw [hunion, Measure.restrict_univ]
      _ ≤ ∫⁻ x in A, ENNReal.ofReal (sellerRevenue M x) ∂(twoGoodsN μY μZ) +
          ∫⁻ x in B, ENNReal.ofReal (sellerRevenue M x) ∂(twoGoodsN μY μZ) :=
          lintegral_union_le _ _ _
      _ ≤ 2 * RevDS (oneGoodN μY) + 2 * RevDS (oneGoodN μZ) := by
          gcongr
          · exact display_19 hn μY μZ M hM hN
          · have h := display_19 hn μZ μY (swapMech M) (hadmSwap M hM hN).1 (hadmSwap M hM hN).2
            have hm' : Measurable (fun x => ENNReal.ofReal (sellerRevenue (swapMech M) x)) :=
              (Finset.measurable_sum _ fun j _ => (hadmSwap M hM hN).1.2.2.2 j).ennreal_ofReal
            rw [hswapLaw, setLIntegral_map hAm hm' hσm, hAB] at h
            simpa only [hrevSwap, hσσ] using h
  have : IsProbabilityMeasure (twoGoodsN μY μZ) := by
    rw [twoGoodsN]; exact Measure.isProbabilityMeasure_map (hg μY μZ).aemeasurable
  have hle : RevDS (twoGoodsN μY μZ) ≤ 2 * (RevDS (oneGoodN μY) + RevDS (oneGoodN μZ)) := by
    rw [(remark_b_npt_ds hn (twoGoodsN μY μZ)).2, mul_add]
    exact iSup₂_le fun M hM => key M hM.1 hM.2
  calc (1 / 2 : ℝ≥0∞) * RevDS (twoGoodsN μY μZ)
      ≤ (1 / 2 : ℝ≥0∞) * (2 * (RevDS (oneGoodN μY) + RevDS (oneGoodN μZ))) := by gcongr
    _ = RevDS (oneGoodN μY) + RevDS (oneGoodN μZ) := by
      rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
