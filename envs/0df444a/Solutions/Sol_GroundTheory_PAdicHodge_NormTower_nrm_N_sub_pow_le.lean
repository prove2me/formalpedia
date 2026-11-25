-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.nrm_N_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:17.304081+00:00
-- url     : https://prove2.me/submissions/1adc3546-1856-41d9-9037-1b400e22e6d7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_algEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod_sub_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)
namespace GroundTheory.PAdicHodge.NormTower
theorem _root_.solution (n : ℕ) {y : Ω} (hy : y ∈ t.E (n + 1)) (hy1 : nrm K y ≤ 1) :
    nrm K (t.N n y - y ^ (p ^ t.k n)) ≤ t.c := by
  rw [← t.card_alt n, ← Finset.prod_const, N]
  refine nrm_prod_sub_prod_le _ _ _ t.c_nonneg (fun σ _ ↦ by rwa [nrm_algEquiv]) (fun _ _ ↦ hy1)
    fun σ hσ ↦ ?_
  refine (t.step n σ hσ y hy).trans ?_
  calc t.c * nrm K y ≤ t.c * 1 := mul_le_mul_of_nonneg_left hy1 t.c_nonneg
    _ = t.c := mul_one _
end GroundTheory.PAdicHodge.NormTower
