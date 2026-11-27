-- Prove2me | solution 1 for GlobalTheory.LocLatInert.single_mem_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:04:35.142332+00:00
-- url     : https://prove2.me/submissions/9d900aa9-2bb0-4f31-a083-e6df15651882

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
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (i j : Fin n) (t : K) (h : Pi.single i t ∈ L) : Pi.single j t ∈ L := by

  have hPP : (Equiv.swap i j).permMatrix K * (Equiv.swap i j).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  let P : GL (Fin n) K := ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K, hPP, hPP⟩
  have hmap : ((Equiv.swap i j).permMatrix K).map σ = (Equiv.swap i j).permMatrix K := by
    ext a b
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact map_one σ
    · exact map_zero σ
  have hPU : P ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show (((Equiv.swap i j).permMatrix K).map σ)ᵀ * 1 * (Equiv.swap i j).permMatrix K = 1
    rw [hmap, Matrix.transpose_permMatrix, Matrix.mul_one, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hent : ∀ a b, Valued.v (((Equiv.swap i j).permMatrix K) a b) ≤ 1 := by
    intro a b
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le
  have hP := hU P hPU hent hent _ h

  have e : (P : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i t = Pi.single j t := by
    show (Equiv.swap i j).permMatrix K *ᵥ Pi.single i t = Pi.single j t
    rw [Matrix.permMatrix_mulVec]
    funext a
    simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  exact e ▸ hP
end GlobalTheory.LocLatInert
