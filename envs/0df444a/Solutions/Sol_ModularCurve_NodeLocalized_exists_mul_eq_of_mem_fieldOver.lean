-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e5f5bbb4-b37f-5e4c-a7da-8cd84fc505d0

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver.ModularCurve ModularCurve.NodeLocalized"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries"
p2m_open "ModularCurve"
namespace D5

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

def fracField (S : Subring LQ) : Subfield LQ where
  carrier := {x | ∃ y z : LQ, y ∈ S ∧ z ∈ S ∧ z ≠ 0 ∧ x * z = y}
  zero_mem' := ⟨0, 1, zero_mem S, one_mem S, one_ne_zero, by ring⟩
  one_mem' := ⟨1, 1, one_mem S, one_mem S, one_ne_zero, by ring⟩
  add_mem' := by
    rintro x x' ⟨y, z, hy, hz, hz0, hxz⟩ ⟨y', z', hy', hz', hz0', hxz'⟩
    refine ⟨y * z' + y' * z, z * z', add_mem (mul_mem hy hz') (mul_mem hy' hz), mul_mem hz hz',
      mul_ne_zero hz0 hz0', ?_⟩
    calc (x + x') * (z * z') = x * z * z' + x' * z' * z := by ring
      _ = y * z' + y' * z := by rw [hxz, hxz']
  neg_mem' := by
    rintro x ⟨y, z, hy, hz, hz0, hxz⟩
    exact ⟨-y, z, neg_mem hy, hz, hz0, by rw [neg_mul, hxz]⟩
  mul_mem' := by
    rintro x x' ⟨y, z, hy, hz, hz0, hxz⟩ ⟨y', z', hy', hz', hz0', hxz'⟩
    refine ⟨y * y', z * z', mul_mem hy hy', mul_mem hz hz', mul_ne_zero hz0 hz0', ?_⟩
    calc x * x' * (z * z') = (x * z) * (x' * z') := by ring
      _ = y * y' := by rw [hxz, hxz']
  inv_mem' := by
    rintro x ⟨y, z, hy, hz, hz0, hxz⟩
    by_cases hx : x = 0
    · exact ⟨0, 1, zero_mem S, one_mem S, one_ne_zero, by rw [hx, inv_zero, zero_mul]⟩
    · refine ⟨z, y, hz, hy, ?_, ?_⟩
      · rw [← hxz]; exact mul_ne_zero hx hz0
      · rw [← hxz, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem mem_fracField_iff (S : Subring LQ) (x : LQ) :
    x ∈ fracField S ↔ ∃ y z : LQ, y ∈ S ∧ z ∈ S ∧ z ≠ 0 ∧ x * z = y := Iff.rfl

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] (red : A →+* k) (a : k)
  (K : IntermediateField ℚ Qb)

theorem fieldOver_le :
    fieldOver (1 * q) K ≤ fracField (modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
  have hmem : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), modularEval (1 * q) (coeffSubring A K) p ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) :=
    fun p => modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) p
  unfold fieldOver
  rw [Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | rfl | rfl)
  ·
    rcases A.mem_or_inv_mem (c : Qb) with hc | hc
    · refine ⟨_, 1, hmem (MvPolynomial.C ⟨(c : Qb), hc, c.2⟩), one_mem _, one_ne_zero, ?_⟩
      rw [mul_one]; simp [modularEval]; rfl
    · by_cases hc0 : (c : Qb) = 0
      · refine ⟨0, 1, zero_mem _, one_mem _, one_ne_zero, ?_⟩
        show algebraMap Qb LQ (c : Qb) * 1 = 0
        rw [mul_one, hc0, map_zero]
      · refine ⟨1, _, one_mem _, hmem (MvPolynomial.C ⟨(c : Qb)⁻¹, hc, K.inv_mem c.2⟩), ?_, ?_⟩
        · simp [modularEval, CharPReduction.constSeries, hc0]
        · show algebraMap Qb LQ (c : Qb) * modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C _) = 1
          rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
          show algebraMap Qb LQ (c : Qb) * algebraMap Qb LQ (c : Qb)⁻¹ = 1
          rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  · exact ⟨_, 1, hmem (MvPolynomial.X 0), one_mem _, one_ne_zero, by rw [mul_one]; simp [modularEval]⟩
  · exact ⟨_, 1, hmem (MvPolynomial.X 1), one_mem _, one_ne_zero, by rw [mul_one]; simp [modularEval]⟩

end D5
end ModularCurve
end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver (1 * q) K) :
    ∃ y z : LaurentSeries (AlgebraicClosure ℚ),
      y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ∧
      z ≠ 0 ∧ x * z = y :=
  ModularCurve.D5.fieldOver_le red a K hx

end S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver (solution)
