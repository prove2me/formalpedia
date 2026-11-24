-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.hf_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:22:03.934323+00:00
-- url     : https://prove2.me/submissions/53b66d47-380c-4ed2-b5b9-f374c6252cc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution (h : GU σ n) (i j : Fin n) :
    hf σ (fun k => mat h k i) (fun k => mat h k j) = antiJ L n i j := by
  have hh : cT σ (mat h) * antiJ L n * mat h = antiJ L n := h.2
  have key : ∀ l, (cT σ (mat h) * antiJ L n) i l = σ (mat h l.rev i) := by
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
  calc hf σ (fun k => mat h k i) (fun k => mat h k j) = (cT σ (mat h) * antiJ L n * mat h) i j := by
        rw [Matrix.mul_apply]
        simp only [key]
        rfl
    _ = antiJ L n i j := by rw [hh]
end GlobalTheory.CompanionTheory.InertCoset
