-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.exists_K_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:03.297902+00:00
-- url     : https://prove2.me/submissions/c6d26bd8-b9f5-4831-b4b3-9e4bc9b2f110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_sub_left
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_sub_right
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_refl_unitary
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_refl_mulVec
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
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
private theorem mem_KU_of_mat_and_inv_mem_intL {m : ℕ} (A : GU σ m) (h1 : ∀ i j, mat A i j ∈ intL L)
    (h2 : ∀ i j, (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L) :
    A ∈ KU σ m := by
  let X : Matrix (Fin m) (Fin m) (intL L) := Matrix.of fun i j => ⟨mat A i j, h1 i j⟩
  let Y : Matrix (Fin m) (Fin m) (intL L) :=
    Matrix.of fun i j => ⟨(((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j, h2 i j⟩
  have hX : (intL L).subtype.mapMatrix X = mat A := by
    ext i j
    rfl
  have hY : (intL L).subtype.mapMatrix Y = (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) := by
    ext i j
    rfl
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin m) (Fin m) (intL L) → Matrix (Fin m) (Fin m) L) :=
    Matrix.map_injective Subtype.val_injective
  have hXY : X * Y = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).mul_inv)
  have hYX : Y * X = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).inv_mul)
  rw [KU, Subgroup.mem_subgroupOf]
  show (A : GL (Fin m) L) ∈ GU σ m ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨A.2, MonoidHom.mem_range.2 ⟨⟨X, Y, hXY, hYX⟩, ?_⟩⟩
  apply Units.ext
  ext i j
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
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {e w : Fin n → L}
    (he : ∀ i, e i ∈ intL L) (hw : ∀ i, w i ∈ intL L) (hee : hf σ e e = 0) (hww : hf σ w w = 0)
    (hew : hf σ e w = 1) : ∃ k ∈ KU σ n, mat k *ᵥ e = w := by
  set d := e - w with hd_def
  have hwe : hf σ w e = 1 := by rw [← hf_conj hσσ, hew, map_one]
  have hdd : hf σ d d = -2 := by
    rw [hd_def, hf_sub_left, hf_sub_right, hf_sub_right, hee, hew, hwe, hww]
    ring
  have hde : hf σ d e = -1 := by
    rw [hd_def, hf_sub_left, hee, hwe]
    ring
  have hinv : ∀ x, refl σ d *ᵥ (refl σ d *ᵥ x) = x := by
    intro x
    rw [refl_mulVec, refl_mulVec, hform_add_right_orbital_bounds_conclusion]
    have h2 : hf σ d (hf σ d x • d) = hf σ d x * hf σ d d := by
      simpa using hf_smul (σ := σ) 1 (hf σ d x) d d
    rw [h2, hdd]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRR : refl σ d * refl σ d = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => mem_intL'.2 (by rw [hσ]; exact mem_intL'.1 hx)
  have hdint : ∀ i, d i ∈ intL L := fun i => (intL L).sub_mem (he i) (hw i)
  have hRint : ∀ i j, refl σ d i j ∈ intL L := by
    intro i j
    simp only [refl, Matrix.add_apply, Matrix.of_apply]
    refine (intL L).add_mem ?_ ((intL L).mul_mem (hdint i) (hσint _ (hdint j.rev)))
    rw [Matrix.one_apply]
    split_ifs
    · exact (intL L).one_mem
    · exact (intL L).zero_mem
  let R : GL (Fin n) L := ⟨refl σ d, refl σ d, hRR, hRR⟩
  have hRU : R ∈ GU σ n := refl_unitary hσσ d hdd
  refine ⟨⟨R, hRU⟩, mem_KU_of_mat_and_inv_mem_intL _ hRint hRint, ?_⟩
  show refl σ d *ᵥ e = w
  rw [refl_mulVec, hde, hd_def]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring
end GlobalTheory.CompanionTheory.InertCoset
