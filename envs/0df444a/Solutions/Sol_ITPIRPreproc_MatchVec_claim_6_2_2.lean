-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.claim_6_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T16:06:42.781948+00:00
-- url     : https://prove2.me/submissions/e6f9ffbb-097d-401c-801e-e9c51680a363

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


def recoverCoins (v : Fin (2^h) → Fin d → ZMod 6) (i : Pos h) (Q : ActKey h d) :
    ZMod 2 × (Fin h → ZMod 2) :=
  (Q.2 ⬝ᵥ vec2 (v i.1) - 1, Q.1 *ᵥ vec2 (v i.1) - i.2)

def recoverKey (u v : Fin (2^h) → Fin d → ZMod 6) (i : Pos h) (Q : ActKey h d) :
    ActKey h d :=
  (Q.1 - vecMulVec (recoverCoins v i Q).2 (vec2 (u i.1)),
   Q.2 - (recoverCoins v i Q).1 • vec2 (u i.1))

lemma recover_compatible (hmv : IsMVFamily (2^h) d u v) (i : Pos h) (Q : ActKey h d) :
    actSel v (recoverKey u v i Q) i := by
  constructor
  · simp [recoverKey, recoverCoins, sub_mulVec, vecMulVec_mulVec, diag2 hmv]
  · simp [recoverKey, recoverCoins, sub_dotProduct, smul_dotProduct, diag2 hmv, smul_eq_mul]

lemma recover_coins_query (hmv : IsMVFamily (2^h) d u v) (i : Pos h)
    (K : ActKey h d) (hK : actSel v K i) (c : ZMod 2 × (Fin h → ZMod 2)) :
    recoverCoins v i (actQueryMap u i K c) = c := by
  apply Prod.ext
  · simp [recoverCoins, query_act, hK.2, diag2 hmv]
  · simp [recoverCoins, query_col, hK.1, diag2 hmv]

noncomputable def queryEquiv (hmv : IsMVFamily (2^h) d u v) (i : Pos h) :
    ({K : ActKey h d // K ∈ actCompat v i} × (ZMod 2 × (Fin h → ZMod 2))) ≃ ActKey h d where
  toFun z := actQueryMap u i z.1.1 z.2
  invFun Q := (⟨recoverKey u v i Q, by
    simp only [actCompat, mem_filter, mem_univ, true_and]
    exact recover_compatible hmv i Q⟩, recoverCoins v i Q)
  left_inv z := by
    have hK : actSel v z.1.1 i := (mem_filter.mp z.1.2).2
    have hc := recover_coins_query hmv i z.1.1 hK z.2
    apply Prod.ext
    · apply Subtype.ext
      change recoverKey u v i (actQueryMap u i z.1.1 z.2) = z.1.1
      unfold recoverKey
      rw [hc]
      simp [actQueryMap]
    · exact hc
  right_inv Q := by
    simp [recoverKey, actQueryMap]

lemma uniform_query (hmv : IsMVFamily (2^h) d u v) (i : Pos h) (Q : ActKey h d) :
    avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure {p | p.1 = Q}) =
      (Fintype.card (ActKey h d) : ℝ≥0∞)⁻¹ := by
  classical
  let e := queryEquiv hmv i
  let w : ℝ≥0∞ := (Fintype.card (ZMod 2 × (Fin h → ZMod 2)) : ℝ≥0∞)⁻¹
  have hs : (∑ K ∈ actCompat v i, ∑ c : ZMod 2 × (Fin h → ZMod 2),
      if actQueryMap u i K c = Q then w else 0) = w := by
    rw [← Finset.sum_coe_sort]
    rw [← Fintype.sum_prod_type (fun z : {K : ActKey h d // K ∈ actCompat v i} ×
      (ZMod 2 × (Fin h → ZMod 2)) => if actQueryMap u i z.1.1 z.2 = Q then w else 0)]
    change (∑ z, if e z = Q then w else 0) = w
    rw [e.sum_comp (fun q => if q = Q then w else 0)]
    simp
  unfold avgOver actQuery
  simp_rw [PMF.toOuterMeasure_map_apply]
  simp only [PMF.toOuterMeasure_apply_fintype,
    Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq, PMF.uniformOfFintype_apply]
  change ((actCompat v i).card : ℝ≥0∞)⁻¹ *
    (∑ K ∈ actCompat v i, ∑ c : ZMod 2 × (Fin h → ZMod 2),
      if actQueryMap u i K c = Q then w else 0) = _
  rw [hs]
  dsimp [w]
  rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), ← Nat.cast_mul]
  congr 2
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_prod, Fintype.card_coe] using hc
end PIRProof

theorem solution (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    ∀ (i : Pos h) (Q₀ : ActKey h d),
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure {p | p.1 = Q₀}) =
        (Fintype.card (ActKey h d) : ℝ≥0∞)⁻¹ := PIRProof.uniform_query hmv
