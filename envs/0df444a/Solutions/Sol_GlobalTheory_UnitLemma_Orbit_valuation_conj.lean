-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.valuation_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:28.245062+00:00
-- url     : https://prove2.me/submissions/6a98d1dc-0230-4017-b042-f20674777d2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_conj_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (x : K.E) : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) =
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv
  have hc : ∀ y : K.E, y ≠ 0 → K.c y ≠ 0 := fun y hy => by simpa using hy
  have hmono : ∀ a b : K.E, b ≠ 0 → v a ≤ v b → v (K.c a) ≤ v (K.c b) := by
    intro a b hb h
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ h zero_le'
    have h2 := val_conj_le _ h1
    rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hb))] at h2
    exact h2
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  rw [← hv] at hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : v (K.c π) < 1 := by
    by_contra hn
    have := hmono 1 (K.c π) (hc π hπ0) (by simpa using hn)
    rw [K.c_c, map_one, map_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have h2 : v (K.c π) ≤ v π := by
    rw [hπ]
    have h0 : v (K.c π) ≠ 0 := by simpa using hπ0
    rw [← WithZero.exp_log h0] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]
    omega
  have h3 : v (K.c π) = v π := le_antisymm h2 (by simpa [K.c_c] using hmono _ _ hπ0 h2)
  by_cases hx : x = 0
  · simp [hx]
  have h0 : v x ≠ 0 := by simpa using hx
  have h4 : v x = v (π ^ (-WithZero.log (v x))) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log h0]
  have h5 := le_antisymm (hmono _ _ (zpow_ne_zero _ hπ0) h4.le) (hmono _ _ hx h4.ge)
  rw [h5, map_zpow₀, map_zpow₀, h3, ← map_zpow₀, ← h4]
end GlobalTheory.UnitLemma.Orbit
