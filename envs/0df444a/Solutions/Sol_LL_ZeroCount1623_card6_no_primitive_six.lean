-- Prove2me | solution 1 for LL_ZeroCount1623.card6_no_primitive_six
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:43:12.971943+00:00
-- url     : https://prove2.me/submissions/dcefdd9e-b708-4488-9af0-4b42aae8e9cf

import Mathlib

/-- The only unit of `ZMod 6` mapping to `1` in `ZMod 3` is `1`. -/
lemma units_six_ker_trivial :
    ∀ u : (ZMod 6)ˣ, ZMod.unitsMap (show (3 : ℕ) ∣ 6 by norm_num) u = 1 → u = 1 := by
  intro u hu
  have h1 : ZMod.castHom (show (3 : ℕ) ∣ 6 by norm_num) (ZMod 3) (u : ZMod 6) = 1 := by
    have := congrArg Units.val hu
    simpa [ZMod.unitsMap_def] using this
  have h2 : (u : ZMod 6) * ((u⁻¹ : (ZMod 6)ˣ) : ZMod 6) = 1 := u.mul_inv
  ext
  generalize (u : ZMod 6) = x at h1 h2
  generalize ((u⁻¹ : (ZMod 6)ˣ) : ZMod 6) = y at h2
  revert x y
  decide

theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q = 6) : ¬ χ.IsPrimitive := by
  subst hq
  intro hprim
  have hker : (ZMod.unitsMap (show (3 : ℕ) ∣ 6 by norm_num)).ker ≤ χ.toUnitHom.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [units_six_ker_trivial u hu, map_one]
  have hf : χ.FactorsThrough 3 :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap _).mpr hker
  have hd : χ.conductor ∣ 3 := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hf
  rw [DirichletCharacter.isPrimitive_def] at hprim
  rw [hprim] at hd
  norm_num at hd
