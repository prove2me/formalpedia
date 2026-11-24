-- Prove2me | solution 1 for GlobalTheory.UnitaryCharacter.reflIn_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:16.68695+00:00
-- url     : https://prove2.me/submissions/076ac0e9-7e86-4903-882c-8d57c2bd013a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_smul
import Theorems.Thm_GlobalTheory_UnitarySwap_entries_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_form_herm
import Theorems.Thm_GlobalTheory_UnitarySwap_form_mulVec
import Theorems.Thm_GlobalTheory_UnitarySwap_form_single
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_GLint_of_unitary
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_refl_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_refl_isom
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
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    (ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle)
    (hν : ∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1)
    (g : UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ReflIn (form σ (J : Matrix (Fin n) (Fin n) L)) (kerEnd ν)
      {v | ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ intVec L n} := by
  intro w hw μ hμ0 hμ hww
  have hσO : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by rw [mem_int, hσ]; exact hx
  have hΛ' := selfDual_image (selfDual_intVec hσ hJ) g.2
  have hs := refl_isom (form_herm hσσ hh) w μ hμ0 hww
  have h2 : ∀ v, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ intVec L n →
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ
        (refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ v) ∈ intVec L n := by
    intro v hv
    rw [refl_apply, sub_eq_add_neg, ← neg_smul]
    exact hΛ'.add hv (hΛ'.smul hσO (neg_mem (mul_mem hμ (hΛ'.pair hw hv))) hw)
  obtain ⟨S, hS'⟩ : ∃ S : Matrix (Fin n) (Fin n) L,
      Matrix.toLin' S = refl (form σ (J : Matrix (Fin n) (Fin n) L)) w μ := Matrix.toLin'.surjective _
  rw [← hS'] at hs h2 ⊢
  simp only [Matrix.toLin'_apply] at hs h2
  have hS : cT σ S * J * S = J := by
    ext i j
    rw [← form_single (σ := σ) (cT σ S * (J : Matrix (Fin n) (Fin n) L) * S), ← form_mulVec, hs, form_single]
  have hSi : (((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ S * J)) * S = 1 := by
    rw [Matrix.mul_assoc, hS, Units.inv_mul]
  let S' : UJ σ (J : Matrix (Fin n) (Fin n) L) := ⟨⟨S, _, mul_eq_one_comm.mp hSi, hSi⟩, hS⟩
  refine ⟨S', ?_, fun v => Matrix.toLin'_apply _ _⟩
  have := hν (g * S' * g⁻¹) (mem_GLint_of_unitary hσ hJ (g * S' * g⁻¹).2 (entries_mem fun v hv => by
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, ← Matrix.mulVec_mulVec]
    apply h2
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hv))
  rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
end GlobalTheory.UnitaryCharacter
