-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.claim_6_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T16:06:12.266213+00:00
-- url     : https://prove2.me/submissions/db2bd5ae-1d94-4b8e-b4e7-1b9a6429ed0e

import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
open Matrix Finset
open ITPIRPreproc.MatchVec

namespace PIRProof
variable {h d : ℕ} {u v : Fin (2^h) → Fin d → ZMod 6}

lemma dot2 (x y : Fin d → ZMod 6) : vec2 x ⬝ᵥ vec2 y = red2 (x ⬝ᵥ y) := by
  change (fun j => red2 (x j)) ⬝ᵥ (fun j => red2 (y j)) = red2 (x ⬝ᵥ y)
  exact (red2.map_dotProduct x y).symm
lemma dot3 (x y : Fin d → ZMod 6) : vec3 x ⬝ᵥ vec3 y = red3 (x ⬝ᵥ y) := by
  change (fun j => red3 (x j)) ⬝ᵥ (fun j => red3 (y j)) = red3 (x ⬝ᵥ y)
  exact (red3.map_dotProduct x y).symm
lemma diag2 (hmv : IsMVFamily (2^h) d u v) (a : Fin (2^h)) :
    vec2 (u a) ⬝ᵥ vec2 (v a) = 1 := by rw [dot2, hmv.diag, map_one]
lemma diag3 (hmv : IsMVFamily (2^h) d u v) (a : Fin (2^h)) :
    vec3 (u a) ⬝ᵥ vec3 (v a) = 1 := by rw [dot3, hmv.diag, map_one]

lemma query_col (i : Pos h) (K : ActKey h d) (c : ZMod 2 × (Fin h → ZMod 2))
    (a : Fin (2^h)) :
    (actQueryMap u i K c).1 *ᵥ vec2 (v a) =
      K.1 *ᵥ vec2 (v a) + (vec2 (u i.1) ⬝ᵥ vec2 (v a)) • c.2 := by
  ext j
  simp [actQueryMap, add_mulVec, mulVec, dotProduct, vecMulVec,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_add, mul_assoc]
lemma query_act (i : Pos h) (K : ActKey h d) (c : ZMod 2 × (Fin h → ZMod 2))
    (a : Fin (2^h)) :
    (actQueryMap u i K c).2 ⬝ᵥ vec2 (v a) =
      K.2 ⬝ᵥ vec2 (v a) + c.1 * (vec2 (u i.1) ⬝ᵥ vec2 (v a)) := by
  simp [actQueryMap, add_dotProduct, smul_dotProduct, smul_eq_mul]

lemma compatible_nonempty (hmv : IsMVFamily (2^h) d u v) (i : Pos h) :
    (actCompat v i).Nonempty := by
  refine ⟨(vecMulVec i.2 (vec2 (u i.1)), vec2 (u i.1)), ?_⟩
  simp only [actCompat, mem_filter, mem_univ, true_and, actSel, Set.mem_setOf_eq]
  constructor
  · simp [vecMulVec_mulVec, diag2 hmv]
  · exact diag2 hmv i.1

lemma hint_difference (hmv : IsMVFamily (2^h) d u v) (D : DB h) (i : Pos h)
    (K : ActKey h d) (hK : actSel v K i) (δ : Fin h → ZMod 2) :
    vec3 (u i.1) ⬝ᵥ (actHint v D K - actHint v D (actQueryMap u i K (1,δ))) =
      bitF3 (D i.1 (colIdx i.2)) := by
  rw [dotProduct_sub]
  simp only [actHint, dotProduct_sum]
  rw [← sum_sub_distrib]
  rw [Finset.sum_eq_single i.1]
  · have hnew : (actQueryMap u i K (1,δ)).2 ⬝ᵥ vec2 (v i.1) = 0 := by
      rw [query_act, hK.2, diag2 hmv]; change (1 : ZMod 2) + 1 * 1 = 0; decide
    simp [hK.1, hK.2, hnew, dotProduct_smul, diag3 hmv]
  · intro a ha hne
    rcases hmv.offdiag a i.1 hne with hzero | hzero
    · have hd : vec2 (u i.1) ⬝ᵥ vec2 (v a) = 0 := by rw [dot2, hzero]
      have hc : (actQueryMap u i K (1,δ)).1 *ᵥ vec2 (v a) = K.1 *ᵥ vec2 (v a) := by
        rw [query_col, hd, zero_smul, add_zero]
      have hr : (actQueryMap u i K (1,δ)).2 ⬝ᵥ vec2 (v a) = K.2 ⬝ᵥ vec2 (v a) := by
        rw [query_act, hd, mul_zero, add_zero]
      simp [hc, hr]
    · have hd : vec3 (u i.1) ⬝ᵥ vec3 (v a) = 0 := by rw [dot3, hzero]
      split_ifs <;> simp_all [dotProduct_smul]
  · intro hf
    exact False.elim (hf (mem_univ _))

lemma decode_coins (hmv : IsMVFamily (2^h) d u v) (D : DB h) (i : Pos h)
    (K : ActKey h d) (hK : actSel v K i) (c : ZMod 2 × (Fin h → ZMod 2)) :
    actDecode u i K (actHint v D K) (actQueryMap u i K c) c.1
      (actAnswer v D (actQueryMap u i K c)) =
      if c.1 = 0 then none else some (bitF3 (D i.1 (colIdx i.2))) := by
  rcases c with ⟨γ,δ⟩
  have hγ : γ = 0 ∨ γ = 1 := by
    have he : (Finset.univ : Finset (ZMod 2)) = {0,1} := by decide
    have hm := Finset.mem_univ γ
    rw [he] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hγ with rfl | rfl
  · simp [actDecode]
  · simp only [actDecode, show (1 : ZMod 2) ≠ 0 from one_ne_zero, if_false, actAnswer]
    rw [hint_difference hmv D i K hK δ]

lemma avg_const {α : Type*} (s : Finset α) (hs : s.Nonempty) (x : ℝ≥0∞) :
    avgOver s (fun _ => x) = x := by
  have hz : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp [avgOver, nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hz (by simp)]

lemma fair_activation (h : ℕ) :
    (PMF.uniformOfFintype (ZMod 2 × (Fin h → ZMod 2))).toOuterMeasure
      {c | c.1 ≠ 0} = (2 : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_apply_fintype]
  simp only [Fintype.sum_prod_type]
  have hz : (Fintype.card (Fin h → ZMod 2) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Set.indicator_apply, Set.mem_setOf_eq, PMF.uniformOfFintype_apply,
    Fintype.card_prod, Nat.cast_mul, ZMod.card]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0,1} by decide]
  have hpz : (2 : ℝ≥0∞)^h ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpt : (2 : ℝ≥0∞)^h ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  simp [nsmul_eq_mul, ENNReal.mul_inv, mul_comm, mul_left_comm, mul_assoc,
    ENNReal.mul_inv_cancel hpz hpt, ENNReal.inv_mul_cancel hpz hpt]
  rw [mul_left_comm, ENNReal.mul_inv_cancel hpz hpt, mul_one]

lemma sound_for_key (hmv : IsMVFamily (2^h) d u v) (D : DB h) (i : Pos h)
    (K : ActKey h d) (hK : actSel v K i) :
    (actQuery u i K).toOuterMeasure
      {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
        some (bitF3 (D i.1 (colIdx i.2))) ∨
        actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) = none} = 1 := by
  rw [actQuery, PMF.toOuterMeasure_map_apply]
  have heq : (fun c => (actQueryMap u i K c,c.1)) ⁻¹'
      {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
        some (bitF3 (D i.1 (colIdx i.2))) ∨
        actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) = none} = Set.univ := by
    ext c
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [decode_coins hmv D i K hK]
    split_ifs <;> simp
  rw [heq]
  exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

lemma recovery_for_key (hmv : IsMVFamily (2^h) d u v) (D : DB h) (i : Pos h)
    (K : ActKey h d) (hK : actSel v K i) :
    (actQuery u i K).toOuterMeasure
      {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
        some (bitF3 (D i.1 (colIdx i.2)))} = (2 : ℝ≥0∞)⁻¹ := by
  rw [actQuery, PMF.toOuterMeasure_map_apply]
  have heq : (fun c => (actQueryMap u i K c,c.1)) ⁻¹'
      {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
        some (bitF3 (D i.1 (colIdx i.2)))} = {c | c.1 ≠ 0} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [decode_coins hmv D i K hK]
    split_ifs <;> simp_all
  rw [heq, fair_activation]
end PIRProof

 theorem solution (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    ∀ (D : DB h) (i : Pos h),
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure
          {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
                some (bitF3 (D i.1 (colIdx i.2))) ∨
              actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) = none}) = 1 ∧
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure
          {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
                some (bitF3 (D i.1 (colIdx i.2)))}) = 2⁻¹ := by
  intro D i
  constructor
  · calc
      _ = avgOver (actCompat v i) (fun _ => 1) := by
        unfold avgOver
        congr 1
        apply sum_congr rfl
        intro K hK
        exact PIRProof.sound_for_key hmv D i K ((mem_filter.mp hK).2)
      _ = 1 := PIRProof.avg_const _ (PIRProof.compatible_nonempty hmv i) _
  · calc
      _ = avgOver (actCompat v i) (fun _ => 2⁻¹) := by
        unfold avgOver
        congr 1
        apply sum_congr rfl
        intro K hK
        exact PIRProof.recovery_for_key hmv D i K ((mem_filter.mp hK).2)
      _ = 2⁻¹ := PIRProof.avg_const _ (PIRProof.compatible_nonempty hmv i) _
