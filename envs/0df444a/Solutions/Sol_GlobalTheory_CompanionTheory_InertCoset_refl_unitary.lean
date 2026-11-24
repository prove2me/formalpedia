-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.refl_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:14.803963+00:00
-- url     : https://prove2.me/submissions/3782cfc7-7a07-447b-9814-0cf15fdef7be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_single_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
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
private theorem hform_add_right_orbital_bounds_conclusion (x y y' : Fin n → L) : hf σ x (y + y') = hf σ x y + hf σ x y' := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem hf_single_one_right (x : Fin n → L) (a : Fin n) : hf σ x (Pi.single a 1) = σ (x a.rev) := by
  unfold hf
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem single_one_rev_eq_antiJ_apply (i j : Fin n) : (Pi.single j (1 : L) : Fin n → L) i.rev = antiJ L n i j := by
  by_cases h : i.rev = j
  · subst h
    have hv : (i : ℕ) + (i.rev : ℕ) + 1 = n := by rw [Fin.val_rev]; omega
    show (Pi.single i.rev (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (i.rev : ℕ) + 1 = n then 1 else 0)
    rw [if_pos hv, Pi.single_eq_same]
  · have hv : ¬ ((i : ℕ) + (j : ℕ) + 1 = n) := by
      intro h'
      apply h
      ext
      rw [Fin.val_rev]
      omega
    show (Pi.single j (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0)
    rw [if_neg hv, Pi.single_eq_of_ne h]
private theorem cT_mul_antiJ_mul_apply_eq_hf_col (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ A * antiJ L n * A) i j = hf σ (fun k => A k i) (fun k => A k j) := by
  have key : ∀ l, (cT σ A * antiJ L n) i l = σ (A l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [key]
  rfl
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
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (d : Fin n → L) (hd : hf σ d d = -2) :
    cT σ (refl σ d) * antiJ L n * refl σ d = antiJ L n := by
  ext i j
  rw [cT_mul_antiJ_mul_apply_eq_hf_col]
  have hcol : ∀ i, (fun k => refl σ d k i) = Pi.single i 1 + σ (d i.rev) • d := by
    intro i
    ext k
    simp [refl, Matrix.one_apply, Pi.single_apply, mul_comm]
  rw [hcol i, hcol j, hf_add_left, hf_single_left]
  have h1 : hf σ (σ (d i.rev) • d) (Pi.single j 1 + σ (d j.rev) • d) =
      σ (σ (d i.rev)) * hf σ d (Pi.single j 1 + σ (d j.rev) • d) := by
    simpa using hf_smul (σ := σ) (σ (d i.rev)) 1 d (Pi.single j 1 + σ (d j.rev) • d)
  rw [h1, hform_add_right_orbital_bounds_conclusion, hf_single_one_right]
  have h2 : hf σ d (σ (d j.rev) • d) = σ (d j.rev) * hf σ d d := by
    simpa using hf_smul (σ := σ) 1 (σ (d j.rev)) d d
  rw [h2, hd, hσσ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_one_rev_eq_antiJ_apply]
  ring
end GlobalTheory.CompanionTheory.InertCoset
