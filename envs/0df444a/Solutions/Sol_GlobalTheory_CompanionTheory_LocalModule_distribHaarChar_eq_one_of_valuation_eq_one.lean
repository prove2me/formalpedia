-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_eq_one_of_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:55.847927+00:00
-- url     : https://prove2.me/submissions/5b27d5c9-a11d-4bd7-ab29-1acc33956e09

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DistribHaarCharEqOneOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalModule
namespace GlobalTheory.CompanionTheory.LocalModule
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (u : kˣ), valuation k (u : k) = 1 → distribHaarChar k u = 1 := by
  intro k _ _ _ _ u hu
  borelize k
  have hsc : IsCompact {x : k | valuation k x ≤ 1} :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hso : IsOpen {x : k | valuation k x ≤ 1} :=
    Valuation.isOpen_integer (v := valuation k)
  have hus : u • {x : k | valuation k x ≤ 1} = {x : k | valuation k x ≤ 1} := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_ofPred_eq, Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val,
      map_inv₀, hu, inv_one, one_mul]
  have h0 : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ 0 :=
    (hso.measure_pos Measure.addHaar ⟨0, by simp⟩).ne'
  have hfin : (Measure.addHaar : Measure k) {x : k | valuation k x ≤ 1} ≠ ⊤ := hsc.measure_lt_top.ne
  exact distribHaarChar_eq_of_measure_smul_eq_mul h0 hfin (by rw [hus, ENNReal.coe_one, one_mul])
end GlobalTheory.CompanionTheory.LocalModule
