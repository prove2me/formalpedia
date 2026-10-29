-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.K_mPl_mPl_rank_484
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:15:22.662551+00:00
-- url     : https://prove2.me/submissions/3170f55b-4982-4f53-94af-4bf283abdfe7

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace PlGen
open Matrix

noncomputable def yy (x : Fin 23 → ℚ) : Fin 23 → ℚ := fun p => (x p - (∑ q : Fin 23, x q) / 9) / 2

lemma dot (x : Fin 23 → ℚ) (h01 : ∀ p, x p * x p = x p) (hs : ∑ p, x p = 3) :
    yy x ⬝ᵥ x = 1 := by
  unfold dotProduct yy
  rw [hs]
  have : ∀ p, (x p - 3 / 9) / 2 * x p = x p / 3 := by
    intro p; have := h01 p; linear_combination this / 2
  simp_rw [this]
  rw [← Finset.sum_div, hs]; norm_num

lemma idem (x : Fin 23 → ℚ) (h01 : ∀ p, x p * x p = x p) (hs : ∑ p, x p = 3) :
    vecMulVec x (yy x) * vecMulVec x (yy x) = vecMulVec x (yy x) := by
  rw [vecMulVec_mul_vecMulVec, dot x h01 hs, one_smul]

lemma rank_ge {m n : Type} [Fintype n] (A : Matrix m n ℚ) (i : m) (j : n) (h : A i j ≠ 0) :
    1 ≤ A.rank := by
  have hu : IsUnit (A.submatrix (fun _ : Unit => i) (fun _ : Unit => j)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
    simpa using h
  have := rank_submatrix_le A (fun _ : Unit => i) (fun _ : Unit => j)
  rw [rank_of_isUnit _ hu] at this
  simpa using this

lemma rank_one' (x : Fin 23 → ℚ) (hs : ∑ p, x p = 3) (p : Fin 23) (hp : x p = 1) :
    (vecMulVec x (yy x)).rank = 1 := by
  refine le_antisymm (rank_vecMulVec_le _ _) (rank_ge _ p p ?_)
  simp [vecMulVec_apply, yy, hp, hs]; norm_num

lemma compl_idem (x : Fin 23 → ℚ) (h01 : ∀ p, x p * x p = x p) (hs : ∑ p, x p = 3) :
    (1 - vecMulVec x (yy x)) * (1 - vecMulVec x (yy x)) = 1 - vecMulVec x (yy x) := by
  rw [sub_mul, one_mul, mul_sub, mul_one, idem x h01 hs]; abel

lemma rank_add_le' (A B : Matrix (Fin 23) (Fin 23) ℚ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma compl_rank (x : Fin 23 → ℚ) (h01 : ∀ p, x p * x p = x p) (hs : ∑ p, x p = 3)
    (p : Fin 23) (hp : x p = 1) :
    (1 - vecMulVec x (yy x)).rank = 22 := by
  have h1 := rank_one' x hs p hp
  have hz : (1 - vecMulVec x (yy x)) * vecMulVec x (yy x) = 0 := by
    rw [sub_mul, one_mul, idem x h01 hs, sub_self]
  have hup := rank_add_rank_le_card_of_mul_eq_zero hz
  have hlo := rank_add_le' (1 - vecMulVec x (yy x)) (vecMulVec x (yy x))
  rw [sub_add_cancel, Matrix.rank_one] at hlo
  simp only [Fintype.card_fin] at hup hlo
  omega

end PlGen

namespace PlSpec
open Matrix IntMul.Kappa.R8.Bit.Oppbank.Pnd

lemma card3 : ∀ T < 1771,
    (Finset.univ.filter (fun p : Fin 23 => (triL T).testBit p.val = true)).card = 3 := by
  decide +kernel

lemma sum3 {T : ℕ} (hT : T < 1771) : ∑ p : Fin 23, tvQ T p = 3 := by
  unfold tvQ
  rw [Finset.sum_boole, card3 T hT]; norm_num

lemma h01 (T : ℕ) : ∀ p, tvQ T p * tvQ T p = tvQ T p := by
  intro p; unfold tvQ; split_ifs <;> norm_num

lemma hp {T : ℕ} (hT : T < 1771) : ∃ p, tvQ T p = 1 := by
  have h := card3 T hT
  obtain ⟨p, hp⟩ : (Finset.univ.filter (fun p : Fin 23 => (triL T).testBit p.val = true)).Nonempty := by
    rw [← Finset.card_pos, h]; norm_num
  exact ⟨p, by simp only [Finset.mem_filter] at hp; simp [tvQ, hp.2]⟩

lemma Pl_eq (T : ℕ) : Pl T = vecMulVec (tvQ T) (PlGen.yy (tvQ T)) := rfl

end PlSpec


namespace KGen
open Matrix
open scoped Kronecker

lemma rank_idem {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℚ) (hM : M * M = M) :
    (M.rank : ℚ) = M.trace := by
  have he : IsIdempotentElem (Matrix.toLin' M) := by
    show Matrix.toLin' M * Matrix.toLin' M = Matrix.toLin' M
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hM]
  have := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at this
  rw [this]; rfl

lemma rank_conj {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (S : Matrix m n ℚ) (Si : Matrix n m ℚ) (hSi : Si * S = 1) (M : Matrix n n ℚ) :
    (S * M * Si).rank = M.rank := by
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · have : M = Si * (S * M * Si) * S := by
      have e : Si * (S * M * Si) * S = (Si * S) * M * (Si * S) := by
        simp only [Matrix.mul_assoc]
      rw [e, hSi, Matrix.one_mul, Matrix.mul_one]
    conv_lhs => rw [this]
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

lemma rank_kron_idem (A B : Matrix (Fin 23) (Fin 23) ℚ) (hA : A * A = A) (hB : B * B = B) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  have hAB : (A ⊗ₖ B) * (A ⊗ₖ B) = A ⊗ₖ B := by rw [← Matrix.mul_kronecker_mul, hA, hB]
  have h := rank_idem _ hAB
  rw [Matrix.trace_kronecker, ← rank_idem A hA, ← rank_idem B hB] at h
  exact_mod_cast h

lemma K_rank (S : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ) (Si : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ)
    (hSi : Si * S = 1) (A B : Matrix (Fin 23) (Fin 23) ℚ) (hA : A * A = A) (hB : B * B = B) :
    (S * (A ⊗ₖ B) * Si).rank = A.rank * B.rank := by
  rw [rank_conj S Si hSi, rank_kron_idem A B hA hB]

end KGen

namespace KSpec
open Matrix IntMul.Kappa.R8.Bit.Oppbank.Pnd

lemma cidem {a : ℕ} (ha : a < 1771) : (1 - Pl a) * (1 - Pl a) = 1 - Pl a := by
  rw [PlSpec.Pl_eq]; exact PlGen.compl_idem _ (PlSpec.h01 a) (PlSpec.sum3 ha)

lemma crank {a : ℕ} (ha : a < 1771) : (1 - Pl a).rank = 22 := by
  obtain ⟨p, hp⟩ := PlSpec.hp ha
  rw [PlSpec.Pl_eq]; exact PlGen.compl_rank _ (PlSpec.h01 a) (PlSpec.sum3 ha) p hp

noncomputable def e0 : Fin 529 ≃ Pr23 := Fintype.equivOfCardEq (by simp)

noncomputable def S0 : Matrix (Fin 529) Pr23 ℚ := fun i p => if e0 i = p then 1 else 0
noncomputable def Si0 : Matrix Pr23 (Fin 529) ℚ := fun p i => if p = e0 i then 1 else 0

lemma hS0 : S0 * Si0 = 1 := by
  ext i j; simp [Matrix.mul_apply, S0, Si0, Matrix.one_apply, e0.injective.eq_iff]

lemma hSi0 : Si0 * S0 = 1 := by
  ext p q
  simp only [Matrix.mul_apply, S0, Si0, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (e0.symm p)]
  · simp [eq_comm]
  · intro b _ hb; have : p ≠ e0 b := fun h => hb (by simp [h]); simp [this]
  · simp

end KSpec

namespace IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem _root_.solution (S : Matrix (Fin 529) Pr23 ℚ) (Si : Matrix Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a t : ℕ} (ha : a < 1771) (ht : t < 1771) :
    (K S Si (1 - Pl a) (1 - Pl t)).rank = 484 := by
  unfold K
  rw [KGen.K_rank S Si hSi _ _ (KSpec.cidem ha) (KSpec.cidem ht), KSpec.crank ha, KSpec.crank ht]

end IntMul.Kappa.R8.Bit.Oppbank
