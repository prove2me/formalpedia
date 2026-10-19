-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.smul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T16:33:32.32916+00:00
-- url     : https://prove2.me/submissions/b2fbc7a0-a1c9-40ab-aeb7-89495e49a35e

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasWeakDeriv Ω α f g) (c : ℝ) :
    HasWeakDeriv Ω α (c • f) (c • g) := by
  refine ⟨h.1.smul c, h.2.1.smul c, ?_⟩
  intro φ hφ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h.2.2 φ hφ]
  ring
