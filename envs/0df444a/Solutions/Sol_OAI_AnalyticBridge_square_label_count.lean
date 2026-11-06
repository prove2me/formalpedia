-- Prove2me | solution 1 for OAI.AnalyticBridge.square_label_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:18.737247+00:00
-- url     : https://prove2.me/submissions/9726d350-df2d-49df-ba97-9d601f43caa8

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
theorem _root_.solution (F : Finset ℕ) (y E : ℕ)
    (hy : y ≠ 0) (hF : ∀ f ∈ F, f ^ 2 * E ∣ y) :
    F.card ≤ y.divisors.card := by
  apply Finset.card_le_card
  intro f hf
  apply Nat.mem_divisors.mpr
  constructor
  · apply Nat.dvd_trans (Nat.dvd_mul_right f (f * E))
    simpa [pow_two, mul_assoc] using hF f hf
  · exact hy
end OAI.AnalyticBridge
