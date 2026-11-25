-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.grid_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:16.083688+00:00
-- url     : https://prove2.me/submissions/030526e4-0ef1-4360-b77b-4f643840d9bc

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_GridSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i))
    (n : Fin K → Fin (d + 1)) :
    Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  have hmap : ∀ h : ℝ → ℝ,
      ((List.ofFn fun a => grid a (n a)).map h).prod = ∏ a, h (grid a (n a)) := by
    intro h
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  simp only [hmap]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  have hle : ∏ a, nn (grid a (n a)) * nn (grid a (n a) + 1) / Q (grid a (n a)) ≤
      ∏ _a : Fin K, β ^ 2 := by
    apply Finset.prod_le_prod
    · intro a _
      have h := hpos a (n a)
      exact div_nonneg (mul_nonneg h.1.le h.2.1.le) h.2.2.le
    · intro a _
      rw [div_le_iff₀ (hpos a (n a)).2.2]
      exact hb a (n a)
  calc _ ≤ Real.sqrt (∏ _a : Fin K, β ^ 2) := Real.sqrt_le_sqrt hle
    _ = β ^ K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, pow_mul',
        Real.sqrt_sq (pow_nonneg hβ K)]
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
