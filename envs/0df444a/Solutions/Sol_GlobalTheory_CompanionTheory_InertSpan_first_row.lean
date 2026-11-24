-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.first_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:39:57.707493+00:00
-- url     : https://prove2.me/submissions/23b0c79e-187c-4b2f-a1cd-ea3010203d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_v_zpow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
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


attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_last
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a : ℤ) (r : Fin N → L) (c : L)
    (R : Submodule (intL L) (Fin (N + 2) → L)) (he : vec3 (1 : L) 0 0 ∈ R)
    (hA : vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R) (hl : vec3 (0 : L) 0 1 ∈ R)
    (hD : vec3 (0 : L) 0 (ϖ ^ (-a)) ∈ R) :
    ∃ q : Fin (N + 2) → L, Valued.v (q 0) = WithZero.exp ((-a).toNat : ℤ) ∧ q ∈ R ∧
      vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R ∧
      (∃ w, Valued.v w = WithZero.exp (a.toNat : ℤ) ∧ vec3 (0 : L) 0 w ∈ R) ∧
      ∀ R' : Submodule (intL L) (Fin (N + 2) → L), q ∈ R' →
        vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' →
        vec3 (1 : L) 0 0 ∈ R' ∧ vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R' := by
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hint : ∀ n : ℕ, ϖ ^ n ∈ intL L := fun n => pow_mem (by
    rw [GlobalTheory.UnitarySwap.mem_int, hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega) n
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have t1 : (n : ℤ).toNat = n := Int.toNat_natCast n
    have t2 : (-(n : ℤ)).toNat = 0 := by omega
    have ew : vec3 ((ϖ ^ (n : ℤ))) (ϖ ^ (n : ℤ) • r) (ϖ ^ (n : ℤ) * c) =
        ϖ ^ n • vec3 (1 : L) 0 0 + vec3 (0 : L) (ϖ ^ n • r) (ϖ ^ n * c) :=
      vec_ext (by simp) (fun j => by simp) (by simp)
    rw [t1, t2]
    refine ⟨vec3 1 0 0, by simp, he, ?_, ⟨ϖ ^ (-(n : ℤ)), ?_, hD⟩, fun R' h1 h2 => ⟨h1, ?_⟩⟩
    · have := R.sub_mem hA (R.smul_mem ⟨ϖ ^ n, hint n⟩ he)
      rw [ew] at this
      convert this using 1
      show _ = ϖ ^ n • vec3 (1 : L) 0 0 + _ - ϖ ^ n • vec3 (1 : L) 0 0
      abel
    · rw [v_zpow hϖ]
      simp
    · rw [ew]
      exact R'.add_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -a by omega)
    obtain rfl : a = -(n : ℤ) := by omega
    have t1 : (-(n : ℤ)).toNat = 0 := by omega
    have t2 : (-(-(n : ℤ))).toNat = n := by simp
    have en : ϖ ^ n * (ϖ ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
    have ew : vec3 (1 : L) 0 0 = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) -
        vec3 (0 : L) r c :=
      vec_ext (by simp [en]) (fun j => by simp [← mul_assoc, en]) (by simp [← mul_assoc, en])
    have ew2 : ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) =
        vec3 (1 : L) 0 0 + vec3 (0 : L) r c :=
      by rw [ew]; abel
    rw [t1, t2]
    simp only [pow_zero, one_smul, one_mul]
    refine ⟨_, ?_, hA, ?_, ⟨1, by simp, hl⟩, fun R' h1 h2 => ⟨?_, h1⟩⟩
    · rw [blockVector_first, v_zpow hϖ]
      simp
    · have := R.sub_mem (R.smul_mem ⟨ϖ ^ n, hint n⟩ hA) he
      convert this using 1
      show _ = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) - _
      rw [ew2]
      abel
    · rw [ew]
      exact R'.sub_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2
end GlobalTheory.CompanionTheory.InertSpan
