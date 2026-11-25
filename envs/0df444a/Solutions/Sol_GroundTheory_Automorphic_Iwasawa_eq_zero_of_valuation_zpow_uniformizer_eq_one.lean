-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.eq_zero_of_valuation_zpow_uniformizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:26.886852+00:00
-- url     : https://prove2.me/submissions/df3d98b8-ac1c-4128-9b35-b9719adb2cb9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {z : ℤ}
    (h : valuation F ((GLnLocal.uniformizer F : F) ^ z) = 1) : z = 0 := by
  have hlt := valuation_uniformizer_lt_one F
  have hpow : ∀ k : ℕ, valuation F (GLnLocal.uniformizer F : F) ^ (k + 1) < 1 := fun k =>
    lt_of_le_of_lt (by simpa using pow_le_pow_right_of_le_one' hlt.le (Nat.le_add_left 1 k)) hlt
  rw [map_zpow₀] at h
  rcases z with k | k
  · rcases k with _ | k
    · rfl
    · change _ ^ ((k + 1 : ℕ) : ℤ) = 1 at h
      rw [zpow_natCast] at h
      exact absurd h (hpow k).ne
  · rw [zpow_negSucc, inv_eq_one] at h
    exact absurd h (hpow k).ne
end GroundTheory.Automorphic.Iwasawa
