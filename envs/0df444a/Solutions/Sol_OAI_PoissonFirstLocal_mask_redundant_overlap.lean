-- Prove2me | solution 1 for OAI.PoissonFirstLocal.mask_redundant_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:38.024195+00:00
-- url     : https://prove2.me/submissions/44c35681-749b-4dac-ad64-4293e7c50f27

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

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
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution
    (n J B₀ b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ)
    (hB : B₀ ∣ b₀) (hb : b₀ ∣ (B₀ * J) ^ m) :
    (χ (J : ZMod n)) ^ 4 * mask n B₀ =
      (χ (J : ZMod n)) ^ 4 * mask n b₀ := by
  by_cases hJ : n.Coprime J
  · have hiff : n.Coprime B₀ ↔ n.Coprime b₀ := by
      constructor
      · intro hB₀
        have hprod : n.Coprime (B₀ * J) := hB₀.mul_right hJ
        exact Nat.Coprime.of_dvd_right hb (hprod.pow_right m)
      · intro hb₀
        exact Nat.Coprime.of_dvd_right hB hb₀
    simp only [mask]
    split_ifs with h₁ h₂ <;> simp_all
  · have hnu : ¬ IsUnit (J : ZMod n) := by
      intro hu
      exact hJ ((ZMod.isUnit_iff_coprime J n).mp hu).symm
    have hz : χ (J : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [hz]
end OAI.PoissonFirstLocal
