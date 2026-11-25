-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.toFrac_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:40.049852+00:00
-- url     : https://prove2.me/submissions/a7bfbfe4-61f9-4111-9020-0833242035c0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField

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
theorem _root_.solution (x : t.Fam) (m : ℕ) (h : t.value 0 ^ m * nrm K (x.1 0) ≤ 1) :
    toFrac x = IsLocalization.mk' _ (scalePlus x m h) ⟨Plus.unif t ^ m, unif_pow_mem _⟩ := by
  rw [toFrac, IsLocalization.mk'_eq_iff_eq]
  congr 1
  refine Subtype.ext (funext fun n ↦ ?_)
  change (Plus.unif t ^ m).1 n * ((Plus.unif t).1 n ^ _ * x.1 n) =
    (Plus.unif t ^ _).1 n * ((Plus.unif t).1 n ^ m * x.1 n)
  rw [Plus.pow_val, Plus.pow_val]
  ring
end GroundTheory.PAdicHodge.NormTower.Fam
