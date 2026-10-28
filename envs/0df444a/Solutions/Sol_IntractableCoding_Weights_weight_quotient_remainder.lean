-- Prove2me | solution 1 for IntractableCoding.Weights.weight_quotient_remainder
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:32:40.595599+00:00
-- url     : https://prove2.me/submissions/908d2792-a676-4491-8e9e-c4c7fd07d9d8

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights
open PricingWithTips

variable (I : ThreeDMInstance)

lemma hammingNorm_eq_sum {ι : Type} [Fintype ι] (y : ι → ZMod 2) :
    hammingNorm y = ∑ i, if y i ≠ 0 then 1 else 0 := by
  unfold hammingNorm; rw [Finset.card_filter]

lemma hammingNorm_split (t m : ℕ) (x : Fin (t + m) → ZMod 2) :
    hammingNorm x = hammingNorm (fun i : Fin t => x (Fin.castAdd m i)) +
      hammingNorm (fun i : Fin m => x (Fin.natAdd t i)) := by
  simp only [hammingNorm_eq_sum]; rw [Fin.sum_univ_add]

lemma vecMul_subspaceMatrix (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (j : Fin (3 * I.1 * (tCount I + 1))) :
    Matrix.vecMul x (subspaceMatrix I) j =
      Matrix.vecMul (firstPart I x) (subspaceTop I) j + lastPart I x j := by
  simp only [Matrix.vecMul, dotProduct, subspaceMatrix, firstPart, lastPart]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [Matrix.of_apply]
    have hl : Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
        (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) (Fin.castAdd _ i) = subspaceTop I i :=
      Fin.append_left _ _ i
    rw [hl]
  · have hr : ∀ i, Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
        (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) (Fin.natAdd _ i) =
          (1 : Matrix (Fin (3 * I.1 * (tCount I + 1))) (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)) i :=
      fun i => Fin.append_right _ _ i
    simp_rw [Matrix.of_apply, hr]
    simp [Matrix.one_apply]

lemma lastPart_eq (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    lastPart I x = Matrix.vecMul (firstPart I x) (subspaceTop I) := by
  funext j
  have := congrFun hx j
  rw [vecMul_subspaceMatrix, Pi.zero_apply] at this
  rw [eq_neg_of_add_eq_zero_right this, ZMod.neg_eq_self_mod_two]

lemma vecMul_top_left (x₀ : Fin (tCount I) → ZMod 2) (j : Fin (3 * I.1 * (tCount I + 1)))
    (i : Fin (3 * I.1)) (hij : j.val = i.val) :
    Matrix.vecMul x₀ (subspaceTop I) j = Matrix.vecMul x₀ (incidence I) i := by
  simp only [Matrix.vecMul, dotProduct, subspaceTop]
  have hj : j.val < 3 * I.1 := hij ▸ i.isLt
  apply Finset.sum_congr rfl; intro r _; rw [dif_pos hj]
  congr 2; exact Fin.ext hij

lemma vecMul_top_right (x₀ : Fin (tCount I) → ZMod 2) (j : Fin (3 * I.1 * (tCount I + 1)))
    (q : Fin (3 * I.1)) (r : Fin (tCount I)) (hj : j.val = 3 * I.1 + (r.val + tCount I * q.val)) :
    Matrix.vecMul x₀ (subspaceTop I) j = x₀ r := by
  simp only [Matrix.vecMul, dotProduct, subspaceTop]
  have hj' : ¬ j.val < 3 * I.1 := by omega
  simp_rw [dif_neg hj']
  have key : ∀ r' : Fin (tCount I), ((j.val - 3 * I.1) % tCount I = r'.val) ↔ r' = r := by
    intro r'
    rw [hj, Nat.add_sub_cancel_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
    exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
  simp_rw [key]
  simp [Finset.sum_ite_eq']

lemma hammingNorm_vecMul_top (x₀ : Fin (tCount I) → ZMod 2) :
    hammingNorm (Matrix.vecMul x₀ (subspaceTop I)) =
      hammingNorm (Matrix.vecMul x₀ (incidence I)) + 3 * I.1 * hammingNorm x₀ := by
  have hc : 3 * I.1 + 3 * I.1 * tCount I = 3 * I.1 * (tCount I + 1) := by ring
  rw [hammingNorm_eq_sum, ← Equiv.sum_comp (finCongr hc), Fin.sum_univ_add]
  congr 1
  · rw [hammingNorm_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [vecMul_top_left I x₀ _ i (by simp)]
  · rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    have : ∀ (q : Fin (3 * I.1)) (r : Fin (tCount I)),
        (if Matrix.vecMul x₀ (subspaceTop I)
            (finCongr hc (Fin.natAdd (3 * I.1) (finProdFinEquiv (q, r)))) ≠ 0 then 1 else 0) =
          if x₀ r ≠ 0 then 1 else 0 := by
      intro q r
      rw [vecMul_top_right I x₀ _ q r (by simp; ring)]
    simp_rw [this]
    rw [← hammingNorm_eq_sum]
    simp

theorem weight_identity' (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (lastPart I x) =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          3 * I.1 * hammingNorm (firstPart I x) ∧
      hammingNorm x =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          (3 * I.1 + 1) * hammingNorm (firstPart I x) := by
  have h1 : hammingNorm (lastPart I x) =
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
        3 * I.1 * hammingNorm (firstPart I x) := by
    rw [lastPart_eq I x hx, hammingNorm_vecMul_top]
  refine ⟨h1, ?_⟩
  have h2 := hammingNorm_split (tCount I) (3 * I.1 * (tCount I + 1)) x
  change hammingNorm x = hammingNorm (firstPart I x) + hammingNorm (lastPart I x) at h2
  rw [h2, h1]; ring

theorem weight_quotient_remainder' (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 ∧
      hammingNorm (firstPart I x) = hammingNorm x / (3 * I.1 + 1) ∧
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = hammingNorm x % (3 * I.1 + 1) ∧
      (hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 →
        hammingNorm (firstPart I x) = I.1 ∧
          hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = 3 * I.1) := by
  obtain ⟨-, h2⟩ := weight_identity' I x hx
  have hle : hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 := by
    have := hammingNorm_le_card_fintype (x := Matrix.vecMul (firstPart I x) (incidence I))
    simpa using this
  have hlt : hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) < 3 * I.1 + 1 := by omega
  have hdiv : hammingNorm x / (3 * I.1 + 1) = hammingNorm (firstPart I x) := by
    rw [h2, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
  have hmod : hammingNorm x % (3 * I.1 + 1) =
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) := by
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  refine ⟨hle, hdiv.symm, hmod.symm, fun hw => ?_⟩
  have e1 : 3 * I.1 ^ 2 + 4 * I.1 = 3 * I.1 + (3 * I.1 + 1) * I.1 := by ring
  rw [hw, e1, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add] at hdiv
  rw [hw, e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at hmod
  exact ⟨hdiv.symm, hmod.symm⟩

end IntractableCoding.Weights

open IntractableCoding.Weights PricingWithTips in
theorem solution (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 ∧
      hammingNorm (firstPart I x) = hammingNorm x / (3 * I.1 + 1) ∧
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = hammingNorm x % (3 * I.1 + 1) ∧
      (hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 →
        hammingNorm (firstPart I x) = I.1 ∧
          hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = 3 * I.1) :=
  weight_quotient_remainder' I x hx
