-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.exists_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:31.335858+00:00
-- url     : https://prove2.me/submissions/6b9904ad-32af-4290-a502-4793d0c48d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_single_left
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_of_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_single_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_single
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_unit
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_unit_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_col
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_zpow_unit
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_single_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
private theorem mulVec_single_one_eq_col (M : Matrix (Fin n) (Fin n) L) (j : Fin n) : M *ᵥ Pi.single j 1 = fun k => M k j := by
  ext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
section Levi
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}
end Levi
end GlobalTheory.CompanionTheory.InertCoset
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ (N + 2)) :
    ∃ s : ℤ, ∃ k ∈ KU σ (N + 2), ∀ i, mat (g * k) i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i := by
  obtain ⟨hσσ, hσ, -, hϖ, -⟩ := hU
  set u : Fin (N + 2) → L := mat g⁻¹ *ᵥ Pi.single 0 1 with hu_def
  have hgu : mat g *ᵥ u = Pi.single 0 1 := by
    rw [hu_def, Matrix.mulVec_mulVec]
    have h1 : mat g * mat g⁻¹ = 1 := by
      show mat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  have huu : hf σ u u = 0 := by
    have h := hf_col g⁻¹ 0 0
    rw [hu_def, mulVec_single_one_eq_col, h]
    show (if ((0 : Fin (N + 2)) : ℕ) + ((0 : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) = 0
    rw [if_neg (by simp only [Fin.val_zero]; omega)]
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun k => Valued.v (u k)) Finset.univ_nonempty
  have hu1 : u i₁ ≠ 0 := by
    intro h0
    have hall : u = 0 := by
      ext k
      have hk := hi₁ k (Finset.mem_univ _)
      rw [h0, map_zero] at hk
      exact (Valuation.zero_iff _).1 (le_antisymm hk zero_le')
    rw [hall, Matrix.mulVec_zero] at hgu
    have h2 := congrFun hgu 0
    simp at h2
  obtain ⟨t, ht⟩ := exists_zpow_unit hϖ hu1
  set w : Fin (N + 2) → L := (ϖ ^ t) • u with hw_def
  have hwint : ∀ k, w k ∈ intL L := by
    intro k
    apply mem_intL'.2
    simp only [hw_def, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [map_mul] at ht
    calc Valued.v (ϖ ^ t) * Valued.v (u k) ≤ Valued.v (ϖ ^ t) * Valued.v (u i₁) :=
          mul_le_mul' le_rfl (hi₁ k (Finset.mem_univ _))
      _ = 1 := ht
  have hwi₁ : Valued.v (w i₁) = 1 := by
    simpa [hw_def] using ht
  have hww : hf σ w w = 0 := by
    rw [hw_def, hf_smul, huu, mul_zero]
  obtain ⟨i, hi, hwi⟩ := exists_unit_coord hσ hwint hww hwi₁
  set u0 := w i with hu0
  have hu00 : u0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hwi
    exact zero_ne_one hwi
  set z : L := (σ u0)⁻¹ with hz_def
  have hzv : Valued.v z = 1 := by rw [hz_def, map_inv₀, hσ, hwi, inv_one]
  set e : Fin (N + 2) → L := z • Pi.single i.rev 1 with he_def
  have heint : ∀ k, e k ∈ intL L := by
    intro k
    rw [he_def, Pi.smul_apply, smul_eq_mul]
    exact (intL L).mul_mem (mem_intL'.2 (le_of_eq hzv)) (single_mem _ 1 (intL L).one_mem k)
  have hee : hf σ e e = 0 := by
    rw [he_def, hf_smul, hf_single_left, Fin.rev_rev, Pi.single_eq_of_ne hi, mul_zero]
  have hew : hf σ e w = 1 := by
    have h := hf_smul (σ := σ) z 1 (Pi.single i.rev 1) w
    rw [one_smul, mul_one, hf_single_left, Fin.rev_rev] at h
    rw [he_def, h, hz_def, map_inv₀, hσσ]
    exact inv_mul_cancel₀ hu00
  obtain ⟨k1, hk1, hk1e⟩ := exists_K_of_pair hσσ hσ heint hwint hee hww hew
  have hirev : i.rev ≠ i.rev.rev := by
    rw [Fin.rev_rev]
    exact fun h => hi h.symm
  obtain ⟨k2, hk2, hk2e⟩ := exists_K_single hσσ hσ i.rev hirev
  obtain ⟨k3, hk3, hk3e⟩ := exists_K_unit (N := N) hσσ hσ hzv
  refine ⟨t, k1 * k2 * k3, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk1 hk2) hk3, ?_⟩
  have hkv : mat (k1 * k2 * k3) *ᵥ Pi.single 0 1 = w := by
    show (mat k1 * mat k2 * mat k3) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hk3e, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hk2e, ← Matrix.mulVec_smul,
      ← he_def, hk1e]
  have hfinal : mat (g * (k1 * k2 * k3)) *ᵥ Pi.single 0 1 = ϖ ^ t • Pi.single 0 1 := by
    show (mat g * mat (k1 * k2 * k3)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hkv, hw_def, Matrix.mulVec_smul, hgu]
  intro j
  have hj := congrFun hfinal j
  rw [mulVec_single_one_eq_col] at hj
  simpa using hj
end GlobalTheory.CompanionTheory.InertCoset
