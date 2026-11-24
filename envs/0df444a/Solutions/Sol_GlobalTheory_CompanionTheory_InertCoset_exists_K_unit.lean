-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.exists_K_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:13.996556+00:00
-- url     : https://prove2.me/submissions/fc32dc9e-72e1-4c27-b729-327f94d8e27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_single_left
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertCoset_mem_intL__232cca9d9091
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
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
theorem _root_.solution {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {z : L}
    (hz : Valued.v z = 1) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = z • Pi.single 0 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have hσz0 : σ z ≠ 0 := by
    intro h
    apply hz0
    rw [← hσσ z, h, map_zero]
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  let δ : Fin (N + 2) → L := fun i => if i = 0 then z else if i = Fin.last (N + 1) then (σ z)⁻¹ else 1
  let δ' : Fin (N + 2) → L := fun i => if i = 0 then z⁻¹ else if i = Fin.last (N + 1) then σ z else 1
  have hδδ' : ∀ i, δ i * δ' i = 1 := by
    intro i
    simp only [δ, δ']
    split_ifs
    · exact mul_inv_cancel₀ hz0
    · exact inv_mul_cancel₀ hσz0
    · exact one_mul 1
  have hD1 : Matrix.diagonal δ * Matrix.diagonal δ' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hδδ' i
  have hD2 : Matrix.diagonal δ' * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hδδ' i
  let D : GL (Fin (N + 2)) L := ⟨Matrix.diagonal δ, Matrix.diagonal δ', hD1, hD2⟩
  have hunit : ∀ i, σ (δ i) * δ i.rev = 1 := by
    intro i
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · simp only [δ, Fin.rev_zero, if_pos rfl, if_neg hN0]
      exact mul_inv_cancel₀ hσz0
    · have h1 : mid j ≠ 0 := mid_ne_zero j
      have h2 : mid j ≠ Fin.last (N + 1) := mid_ne_last j
      have h3 : (mid j).rev ≠ 0 := by rw [← mid_rev]; exact mid_ne_zero _
      have h4 : (mid j).rev ≠ Fin.last (N + 1) := by rw [← mid_rev]; exact mid_ne_last _
      simp only [δ, if_neg h1, if_neg h2, if_neg h3, if_neg h4, map_one, one_mul]
    · simp only [δ, Fin.rev_last, hN0, if_false, if_true, eq_self_iff_true, ↓reduceIte, map_inv₀, hσσ]
      exact inv_mul_cancel₀ hz0
  have hDU : D ∈ GU σ (N + 2) := by
    show cT σ (Matrix.diagonal δ) * antiJ L (N + 2) * Matrix.diagonal δ = antiJ L (N + 2)
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have hc : ∀ i, (fun k => Matrix.diagonal δ k i) = δ i • Pi.single i 1 := by
      intro i
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Matrix.diagonal_apply_ne _ hk, Pi.single_eq_of_ne hk]
    rw [hc i, hc j, hf_smul, hf_single_left, ← single_one_rev_eq_antiJ_apply]
    by_cases h : i.rev = j
    · subst h
      rw [Pi.single_eq_same, mul_one, hunit i]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => mem_intL'.2 (le_of_eq hx)
  have hδint : ∀ i, δ i ∈ intL L := by
    intro i
    simp only [δ]
    split_ifs
    · exact hint _ hz
    · exact hint _ (by rw [map_inv₀, hσ, hz, inv_one])
    · exact (intL L).one_mem
  have hδ'int : ∀ i, δ' i ∈ intL L := by
    intro i
    simp only [δ']
    split_ifs
    · exact hint _ (by rw [map_inv₀, hz, inv_one])
    · exact hint _ (by rw [hσ, hz])
    · exact (intL L).one_mem
  have hdiag : ∀ (f : Fin (N + 2) → L), (∀ i, f i ∈ intL L) → ∀ i j, Matrix.diagonal f i j ∈ intL L := by
    intro f hf i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact (intL L).zero_mem
  refine ⟨⟨D, hDU⟩, mem_KU_of_mat_and_inv_mem_intL _ (hdiag δ hδint) (hdiag δ' hδ'int), ?_⟩
  show Matrix.diagonal δ *ᵥ _ = _
  ext k
  rw [Matrix.mulVec_diagonal]
  by_cases hk : k = 0
  · subst hk
    simp [δ]
  · simp [Pi.single_eq_of_ne hk]
end GlobalTheory.CompanionTheory.InertCoset
