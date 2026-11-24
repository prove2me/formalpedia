-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.exists_K_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:50.838874+00:00
-- url     : https://prove2.me/submissions/7bd68430-8800-4791-a0be-320e4a4751de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_single_left
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_exists_K_of_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_single_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
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
private theorem hf_single_one_right (x : Fin n → L) (a : Fin n) : hf σ x (Pi.single a 1) = σ (x a.rev) := by
  unfold hf
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
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
theorem _root_.solution {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (a : Fin (N + 2)) (ha : a ≠ a.rev) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = Pi.single a 1 := by
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  have he0int : ∀ k, (Pi.single (0 : Fin (N + 2)) (1 : L) : Fin (N + 2) → L) k ∈ intL L :=
    single_mem 0 1 (intL L).one_mem
  have haint : ∀ k, (Pi.single a (1 : L) : Fin (N + 2) → L) k ∈ intL L := single_mem a 1 (intL L).one_mem
  have hee0 : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) (Pi.single 0 1) = 0 := by
    rw [hf_single_left, Fin.rev_zero, Pi.single_eq_of_ne hN0]
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) *ᵥ _ = _
    rw [Matrix.one_mulVec]
  by_cases hal : a = Fin.last (N + 1)
  · subst hal
    refine exists_K_of_pair hσσ hσ he0int haint hee0 ?_ ?_
    · rw [hf_single_left, Fin.rev_last, Pi.single_eq_of_ne (Ne.symm hN0)]
    · rw [hf_single_left, Fin.rev_zero, Pi.single_eq_same]
  have hbr : a.rev.rev = a := Fin.rev_rev a
  have hb0 : a.rev ≠ 0 := by
    intro h
    apply hal
    rw [← hbr, h, Fin.rev_zero]
  have hbl : a.rev ≠ Fin.last (N + 1) := by
    intro h
    apply ha0
    rw [← hbr, h, Fin.rev_last]
  have hba : a.rev ≠ a := fun h => ha h.symm
  set v : Fin (N + 2) → L := Pi.single (Fin.last (N + 1)) 1 + Pi.single a.rev 1 with hv_def
  have hvint : ∀ k, v k ∈ intL L := fun k =>
    (intL L).add_mem (single_mem _ 1 (intL L).one_mem k) (single_mem _ 1 (intL L).one_mem k)
  have hvv : hf σ v v = 0 := by
    rw [hv_def, hf_add_left, hf_single_left, hf_single_left, Fin.rev_last, hbr]
    simp only [Pi.add_apply]
    rw [Pi.single_eq_of_ne (Ne.symm hN0), Pi.single_eq_of_ne (Ne.symm hb0), Pi.single_eq_of_ne hal,
      Pi.single_eq_of_ne (Ne.symm hba)]
    ring
  have h0v : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) v = 1 := by
    rw [hf_single_left, Fin.rev_zero, hv_def, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hbl),
      add_zero]
  have hva : hf σ v (Pi.single a 1) = 1 := by
    rw [hf_single_one_right, hv_def, Pi.add_apply, Pi.single_eq_of_ne hbl, Pi.single_eq_same, zero_add, map_one]
  have haa : hf σ (Pi.single a (1 : L)) (Pi.single a 1) = 0 := by
    rw [hf_single_left, Pi.single_eq_of_ne hba]
  obtain ⟨k1, hk1, hk1v⟩ := exists_K_of_pair hσσ hσ he0int hvint hee0 hvv h0v
  obtain ⟨k2, hk2, hk2v⟩ := exists_K_of_pair hσσ hσ hvint haint hvv haa hva
  refine ⟨k2 * k1, Subgroup.mul_mem _ hk2 hk1, ?_⟩
  show (mat k2 * mat k1) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, hk1v, hk2v]
end GlobalTheory.CompanionTheory.InertCoset
