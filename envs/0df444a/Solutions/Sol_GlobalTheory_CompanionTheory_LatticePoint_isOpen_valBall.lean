-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LatticePoint.isOpen_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:33.176872+00:00
-- url     : https://prove2.me/submissions/cac57208-228b-41ac-a780-106dfe1ca66e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCompactOpenSubgroupMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticePoint
namespace GlobalTheory.CompanionTheory.LatticePoint
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx
end GlobalTheory.CompanionTheory.LatticePoint
