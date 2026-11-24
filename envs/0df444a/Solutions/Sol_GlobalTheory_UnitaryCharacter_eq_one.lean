-- Prove2me | solution 1 for GlobalTheory.UnitaryCharacter.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:09.701281+00:00
-- url     : https://prove2.me/submissions/fb29789d-a13a-43da-a4c9-519026378c78

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
import Theorems.Thm_GlobalTheory_UnitaryCharacter_exists_move
import Theorems.Thm_GlobalTheory_UnitaryCharacter_reflIn_image
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_entries_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_exists_pow_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_form_herm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_GLint_of_unitary
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_mulVec_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_selfDual_image
import Theorems.Thm_GlobalTheory_UnitarySwap_selfDual_intVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.UnitarySwap
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCharacter
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitaryCharacter
theorem _root_.solution {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    (ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle)
    (hν : ∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1)
    (g : UJ σ (J : Matrix (Fin n) (Fin n) L)) : ν g = 1 := by
  obtain ⟨hσσ, hσ, hσϖ, hϖ, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hτ : σ x * (σ x - x)⁻¹ ∈ intL L :=
    mul_mem (by rw [mem_int, hσ]; exact hx) (by rw [mem_int, map_inv₀, hx1, inv_one])
  have hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
    linear_combination mul_inv_cancel₀ hx0
  have hΛ := selfDual_intVec hσ hJ
  have hΛ' := selfDual_image hΛ g.2
  have hR := reflIn_image hσσ hσ hJ hh ν hν 1
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, Set.setOf_mem_eq] at hR
  obtain ⟨N, hN⟩ := exists_pow_mem hϖ (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  obtain ⟨s, ⟨S, hS, es⟩, -, h1⟩ := exists_move hσσ hσ (form_herm hσσ hh) hτ hτ1 hx1
    (by rw [map_sub, hσσ, neg_sub]) hσϖ hϖ (kerEnd ν) _ ⊤ (Nat.lt_succ_self _)
    _ _ hΛ hΛ' hR (reflIn_image hσσ hσ hJ hh ν hν g) ⟨N, fun v hv => by
      have := mulVec_mem (M := ϖ ^ N • (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hN hv
      rwa [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this⟩
  have := hν (g * S) (mem_GLint_of_unitary hσ hJ (g * S).2 (entries_mem fun v hv => by
    simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← es]
    exact h1 v hv))
  rwa [map_mul, hS, mul_one] at this
end GlobalTheory.UnitaryCharacter
