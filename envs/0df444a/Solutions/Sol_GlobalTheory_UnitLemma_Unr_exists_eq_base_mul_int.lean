-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_eq_base_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:50.625848+00:00
-- url     : https://prove2.me/submissions/4d98a7bb-383f-44c8-85ab-38c6a3c59a9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerSpanningFamilyOfUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeOverUnramifiedExtIff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_range_of_val_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E) :
    ∃ (e : K.E) (b : K'.O), z = φ e * algebraMap K'.O K'.E b := by
  by_cases hz : z = 0
  · exact ⟨0, 0, by simp [hz]⟩
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hφ0 : φ π ≠ 0 := by simpa using hπ0
  set v := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv
  have h1 : WithZero.log (v (φ π)) = -1 := by
    have := hU.2.2.1 π
    unfold val at this
    rw [hπ, WithZero.log_exp, ← hv] at this
    omega
  have hv0 : v (φ π) ≠ 0 := by simpa using hφ0
  have hz0 : v z ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' (z * φ π ^ (WithZero.log (v z))) (by
    unfold val
    rw [← hv, map_mul, map_zpow₀, WithZero.log_mul hz0 (zpow_ne_zero _ hv0), WithZero.log_zpow, h1]
    simp)
  refine ⟨π ^ (-WithZero.log (v z)), b, ?_⟩
  rw [hb, map_zpow₀, zpow_neg]
  have := zpow_ne_zero (WithZero.log (v z)) hφ0
  field_simp
end GlobalTheory.UnitLemma.Unr
