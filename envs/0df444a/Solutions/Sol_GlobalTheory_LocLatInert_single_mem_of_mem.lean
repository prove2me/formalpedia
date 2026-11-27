-- Prove2me | solution 1 for GlobalTheory.LocLatInert.single_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:49:30.411092+00:00
-- url     : https://prove2.me/submissions/af8e3445-325b-4d7d-bd90-9541440020a3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.LocLatInert
theorem _root_.solution (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hO : ∀ a : K, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L)
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (u : K) (hu : σ u * u = 1) (hu1 : Valued.v u ≤ 1) (hu2 : Valued.v (σ u) ≤ 1)
    (hu3 : 1 - u ≠ 0) (hu4 : Valued.v (1 - u)⁻¹ ≤ 1)
    (w : Fin n → K) (hw : w ∈ L) (i : Fin n) : Pi.single i (w i) ∈ L := by

  have hdd : ∀ j, Function.update (1 : Fin n → K) i u j * Function.update (1 : Fin n → K) i (σ u) j = 1 := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self, Function.update_self, mul_comm, hu]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Pi.one_apply, mul_one]
  let D : GL (Fin n) K :=
    ⟨Matrix.diagonal (Function.update 1 i u), Matrix.diagonal (Function.update 1 i (σ u)),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; exact congrArg _ (funext hdd),
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        exact congrArg _ (funext fun j => by rw [mul_comm]; exact hdd j)⟩
  have hDU : D ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show ((Matrix.diagonal (Function.update (1 : Fin n → K) i u)).map σ)ᵀ * 1 *
      Matrix.diagonal (Function.update (1 : Fin n → K) i u) = 1
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self, hu]
    · rw [Function.update_of_ne hj, Pi.one_apply, map_one, mul_one]
  have hent : ∀ (c : K), Valued.v c ≤ 1 → ∀ a b,
      Valued.v (Matrix.diagonal (Function.update (1 : Fin n → K) i c) a b) ≤ 1 := by
    intro c hc a b
    rw [Matrix.diagonal_apply]
    split_ifs
    · by_cases ha : a = i
      · rw [ha, Function.update_self]; exact hc
      · rw [Function.update_of_ne ha, Pi.one_apply, map_one]
    · rw [map_zero]; exact zero_le
  have hDw := hU D hDU (hent u hu1) (hent (σ u) hu2) w hw

  have e1 : (D : Matrix (Fin n) (Fin n) K) *ᵥ w - w = Pi.single i ((u - 1) * w i) := by
    funext j
    show (Matrix.diagonal (Function.update (1 : Fin n → K) i u) *ᵥ w) j - w j = _
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · rw [hj, Function.update_self, Pi.single_eq_same]; ring
    · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj, Pi.one_apply, one_mul, sub_self]
  have hsub : Pi.single i ((u - 1) * w i) ∈ L := e1 ▸ L.sub_mem hDw hw

  have hc : Valued.v (-(1 - u)⁻¹) ≤ 1 := by rw [Valuation.map_neg]; exact hu4
  have hfin := hO _ hc _ hsub
  convert hfin using 1
  funext j
  by_cases hj : j = i
  · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
    field_simp
    ring
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
end GlobalTheory.LocLatInert
