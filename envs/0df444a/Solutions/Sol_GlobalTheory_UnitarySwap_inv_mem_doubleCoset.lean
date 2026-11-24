-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.inv_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:03.440399+00:00
-- url     : https://prove2.me/submissions/fb29f29d-004a-4be1-baba-31ac73102e30

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_exists_swap
import Theorems.Thm_GlobalTheory_UnitarySwap_form_mulVec
import Theorems.Thm_GlobalTheory_UnitarySwap_form_single
import Theorems.Thm_GlobalTheory_UnitarySwap_form_herm
import Theorems.Thm_GlobalTheory_UnitarySwap_mulVec_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_entries_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_selfDual_intVec
import Theorems.Thm_GlobalTheory_UnitarySwap_selfDual_image
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_GLint_of_unitary
import Theorems.Thm_GlobalTheory_UnitarySwap_exists_pow_mem
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
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}
namespace GlobalTheory.UnitarySwap
theorem _root_.solution {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    {g : GL (Fin n) L} (hg : g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂ := by
  obtain ⟨hσσ, hσ, hσϖ, hϖ, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hτ : σ x * (σ x - x)⁻¹ ∈ intL L :=
    mul_mem (by rw [mem_int, hσ]; exact hx) (by rw [mem_int, map_inv₀, hx1, inv_one])
  have hτ1 : σ x * (σ x - x)⁻¹ + σ (σ x * (σ x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
    linear_combination mul_inv_cancel₀ hx0
  have hΛ := selfDual_intVec hσ hJ
  have hΛ' := selfDual_image hΛ hg
  obtain ⟨N, hN⟩ := exists_pow_mem hϖ ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  obtain ⟨s, hs, -, h1, h2⟩ := exists_swap hσ (form_herm hσσ hh) hτ hτ1 hσϖ hϖ _ ⊤ (Nat.lt_succ_self _)
    _ _ hΛ hΛ' ⟨N, fun v hv => by
      have := mulVec_mem (M := ϖ ^ N • ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) hN hv
      rwa [Matrix.smul_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this⟩
  obtain ⟨S, rfl⟩ : ∃ S : Matrix (Fin n) (Fin n) L, Matrix.toLin' S = s := Matrix.toLin'.surjective s
  simp only [Matrix.toLin'_apply] at hs h1 h2
  have hS : cT σ S * J * S = J := by
    ext i j
    rw [← form_single (σ := σ) (cT σ S * (J : Matrix (Fin n) (Fin n) L) * S), ← form_mulVec, hs, form_single]
  have hSi : (((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ S * J)) * S = 1 := by
    rw [Matrix.mul_assoc, hS, Units.inv_mul]
  let S' : GL (Fin n) L := ⟨S, _, mul_eq_one_comm.mp hSi, hSi⟩
  have hS' : S' ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) := hS
  have k1 : g * S' ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L) := by
    refine ⟨mul_mem hg hS', mem_GLint_of_unitary hσ hJ (mul_mem hg hS') (entries_mem fun v hv => ?_)⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact h1 v hv
  have k2 : S' * g⁻¹ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L) := by
    refine ⟨(UJ σ (J : Matrix (Fin n) (Fin n) L)).mul_mem hS' (inv_mem hg),
      mem_GLint_of_unitary hσ hJ (mul_mem hS' (inv_mem hg)) (entries_mem fun v hv => ?_)⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    apply h2
    show _ ∈ intVec L n
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hv
  exact ⟨_, k2, _, inv_mem k1, by group⟩
end GlobalTheory.UnitarySwap
