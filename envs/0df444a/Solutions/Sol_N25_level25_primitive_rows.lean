-- Prove2me | solution 1 for N25.level25_primitive_rows
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:54.974207+00:00
-- url     : https://prove2.me/submissions/98be36b4-9fa2-4bae-b39b-fdaafe457301

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_row_lift

set_option autoImplicit false

open scoped MatrixGroups

namespace N25

private theorem level25_bottom_row_primitive (A : SL(2, ℤ)) :
    (A 1 0 : ZMod 25).val % 5 ≠ 0 ∨ (A 1 1 : ZMod 25).val % 5 ≠ 0 := by
  let ρ : ZMod 25 →+* ZMod 5 := ZMod.castHom (by decide) (ZMod 5)
  have hzero : ∀ z : ZMod 25, z.val % 5 = 0 → ρ z = 0 := by decide +kernel
  by_contra! h
  have hc := hzero _ h.1
  have hd := hzero _ h.2
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  have hcast := congrArg (fun z : ℤ => (z : ZMod 25)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at hcast
  have hz := congrArg ρ hcast
  simp only [map_sub, map_mul, map_one, hc, hd, mul_zero, sub_self] at hz
  exact (show (0 : ZMod 5) ≠ 1 from by decide) hz

/-- Reduced bottom rows are exactly the primitive residue rows. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let primitive : R → Prop := fun r => r.1.val % 5 ≠ 0 ∨ r.2.val % 5 ≠ 0
    let row : SL(2, ℤ) → R := fun A => ((A 1 0 : ZMod 25), (A 1 1 : ZMod 25))
    (∀ A, primitive (row A)) ∧ ∀ r : R, primitive r → ∃ A, row A = r := by
  dsimp only
  constructor
  · exact level25_bottom_row_primitive
  · intro r hr
    have hunit (z : ZMod 25) : IsUnit z ↔ z.val % 5 ≠ 0 := by
      simpa only [show 5^2 = 25 from rfl, ZMod.natCast_zmod_val,
        Nat.dvd_iff_mod_eq_zero] using
        (ZMod.isUnit_natCast_iff_not_dvd_pow (p := 5) (d := 2) (a := z.val)
          (by decide) (by decide))
    have hu : IsUnit (r.1 : ZMod 25) ∨ IsUnit (r.2 : ZMod 25) :=
      hr.imp (hunit _).mpr (hunit _).mpr
    obtain ⟨A, hc, hd⟩ := level25_row_lift r.1 r.2 hu
    exact ⟨A, Prod.ext hc hd⟩

end N25
