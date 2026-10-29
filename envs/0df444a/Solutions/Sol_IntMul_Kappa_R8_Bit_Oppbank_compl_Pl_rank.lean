-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.compl_Pl_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:09:44.499762+00:00
-- url     : https://prove2.me/submissions/4d6265ef-eba7-4a07-a021-b99f9687aae7

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib


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


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem _root_.solution {b : ℕ} (hb : b < v) : (1 - Pl b).rank = 22 := by
  obtain ⟨p, hp⟩ := PlSpec.hp hb
  rw [PlSpec.Pl_eq]; exact PlGen.compl_rank _ (PlSpec.h01 b) (PlSpec.sum3 hb) p hp

end IntMul.Kappa.R8.Bit.Oppbank
