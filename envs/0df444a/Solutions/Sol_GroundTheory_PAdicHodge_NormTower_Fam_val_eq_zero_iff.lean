-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.val_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:46.118583+00:00
-- url     : https://prove2.me/submissions/20c63059-3cf3-4fee-859e-129731a160f6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_D_pos
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Fam
variable {t}
namespace GroundTheory.PAdicHodge.NormTower.Fam
theorem _root_.solution (x : t.Fam) (n : ℕ) : x.1 n = 0 ↔ x.1 0 = 0 := by
  rw [← nrm_eq_zero (K := K), ← nrm_eq_zero (K := K) (x := x.1 0), nrm_val_zero x n,
    pow_eq_zero_iff (t.D_pos 0 n).ne']
end GroundTheory.PAdicHodge.NormTower.Fam
