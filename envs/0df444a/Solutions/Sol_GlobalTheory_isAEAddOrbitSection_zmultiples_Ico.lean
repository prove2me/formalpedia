-- Prove2me | solution 1 for GlobalTheory.isAEAddOrbitSection_zmultiples_Ico
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:29.695912+00:00
-- url     : https://prove2.me/submissions/5639e8a9-b056-42a1-8c08-3e916ab2c682

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    IsAEAddOrbitSection (AddSubgroup.zmultiples (1 : ℝ)) (Ico (0 : ℝ) 1) volume where
  nullMeasurableSet := measurableSet_Ico.nullMeasurableSet
  ae_covers := Eventually.of_forall fun x =>
    ⟨⟨(-⌊x⌋) • (1 : ℝ), AddSubgroup.zsmul_mem_zmultiples _ _⟩, by
      have h1 := Int.floor_le x
      have h2 := Int.lt_floor_add_one x
      simp only [AddSubgroup.mk_vadd, vadd_eq_add, mem_Ico, zsmul_eq_mul, Int.cast_neg]
      constructor <;> linarith⟩
  ae_unique := Eventually.of_forall fun x hx g hg => by
    obtain ⟨g, n, rfl⟩ := g
    simp only [AddSubgroup.mk_vadd, vadd_eq_add, mem_Ico, zsmul_eq_mul, mul_one] at hg hx ⊢
    have h1 : (n : ℝ) < 1 := by linarith [hg.2, hx.1]
    have h2 : (-1 : ℝ) < n := by linarith [hg.1, hx.2]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    have : n = 0 := by omega
    simp [this]
end GlobalTheory
