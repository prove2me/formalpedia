-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_mem_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:34.532243+00:00
-- url     : https://prove2.me/submissions/6915406d-f990-437d-8184-09fff4934c20

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce
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
private theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
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
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact ActualCubicChar.euler_jacobi_sum_zero m hm
end OAI.ActualEisensteinCubic
