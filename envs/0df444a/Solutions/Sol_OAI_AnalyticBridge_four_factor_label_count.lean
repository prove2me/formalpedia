-- Prove2me | solution 1 for OAI.AnalyticBridge.four_factor_label_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:19.420547+00:00
-- url     : https://prove2.me/submissions/cc94c6ff-d88b-4c75-8ab3-bad7083148b1

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open OAI.AnalyticBridge
variable {Ω : Type*}
namespace OAI.AnalyticBridge
theorem _root_.solution (Q : Finset (ℕ × ℕ × ℕ × ℕ))
    (F : ℕ) (hF : F ≠ 0)
    (hQ : ∀ q ∈ Q, q.1 * q.2.1 * q.2.2.1 * q.2.2.2 = F) :
    Q.card ≤ F.divisors.card ^ 4 := by
  let D := F.divisors
  have hsubset : Q ⊆ D ×ˢ (D ×ˢ (D ×ˢ D)) := by
    intro q hq
    rcases q with ⟨J, C, e, v⟩
    have hprod := hQ (J, C, e, v) hq
    have hJ : J ∣ F := by
      refine ⟨C * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = J * (C * e * v) := by ring
    have hC : C ∣ F := by
      refine ⟨J * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = C * (J * e * v) := by ring
    have he : e ∣ F := by
      refine ⟨J * C * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = e * (J * C * v) := by ring
    have hv : v ∣ F := by
      refine ⟨J * C * e, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = v * (J * C * e) := by ring
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hJ, hF⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hC, hF⟩
    apply Finset.mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩
  have hcard := Finset.card_le_card hsubset
  simpa [D, Finset.card_product, pow_succ, pow_zero, mul_assoc] using hcard
end OAI.AnalyticBridge
