-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.nrm_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:28.476716+00:00
-- url     : https://prove2.me/submissions/9a5cbb78-c22e-4347-8f5b-d6fbbcf37c71

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_algEquiv

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
theorem _root_.solution (n : ℕ) (y : Ω) : nrm K (t.N n y) = nrm K y ^ (p ^ t.k n) := by
  rw [N, nrm_prod, ← t.card_alt n, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun σ _ ↦ nrm_algEquiv σ y
end GroundTheory.PAdicHodge.NormTower
