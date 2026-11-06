-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_conj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:40.453381+00:00
-- url     : https://prove2.me/submissions/2687f7b4-78f0-485b-a84e-ac0bc1c2273a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_conjO_omega
section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftFiniteGaussFourier
namespace PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
end PoissonChildCRT
namespace PoissonFirstLocal
open scoped Classical
end PoissonFirstLocal
open Finset Complex
namespace ActualCubicChar
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
variable [Fintype F]
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
private theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  simp only [← pow_mul]
  rw [Nat.mul_comm]
end
end ActualEisensteinCubic
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
open NumberField
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, map_zero, zero_pow (by decide)]
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3
end OAI.ActualEisensteinCubic
