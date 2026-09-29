-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/45cb63cd-2ec8-502e-b081-26be6e4b6ff2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime

set_option autoImplicit false

namespace SL2Card

open Matrix

variable (p : ℕ) [Fact p.Prime]

local notation "F" => ZMod p

theorem range_toGL_eq_ker_det :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range =
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    exact Matrix.SpecialLinearGroup.coeToGL_det s
  · intro hg
    rw [MonoidHom.mem_ker] at hg
    have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have := congrArg Units.val hg
      simpa using this
    refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) F), hdet⟩, ?_⟩
    apply Units.ext
    rfl

theorem det_surjective : Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  let A : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![(u : F), 1]
  have hA : Matrix.det A = (u : F) := by
    simp [A, Matrix.det_diagonal, Fin.prod_univ_two]
  have hA0 : Matrix.det A ≠ 0 := by rw [hA]; exact u.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0, ?_⟩
  apply Units.ext
  show Matrix.det ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = u
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hA]

theorem card_GL_two : Nat.card (GL (Fin 2) F) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [Matrix.card_GL_field 2, Fin.prod_univ_two, ZMod.card p]
  simp

end SL2Card

open SL2Card in
theorem solution (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set detH : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det with hdetH

  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup detH.ker

  have h2 : Nat.card (GL (Fin 2) (ZMod p) ⧸ detH.ker) = p - 1 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange detH).toEquiv,
      MonoidHom.range_eq_top.mpr (det_surjective p), Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]

  have h3 : Nat.card detH.ker = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [hdetH, ← range_toGL_eq_ker_det p]
    exact (Nat.card_congr (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).toEquiv).symm
  rw [card_GL_two p, h2, h3] at h1

  have h4 : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  rw [h4] at h1
  have hp1 : 0 < p - 1 := by omega

  have h5 : (p - 1) * (p * (p ^ 2 - 1)) = (p - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
    calc (p - 1) * (p * (p ^ 2 - 1)) = (p ^ 2 - 1) * (p * (p - 1)) := by ring
      _ = (p - 1) * Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := h1
  exact (Nat.eq_of_mul_eq_mul_left hp1 h5).symm

end S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime (solution)
