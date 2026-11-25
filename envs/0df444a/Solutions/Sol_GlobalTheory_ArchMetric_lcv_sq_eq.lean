-- Prove2me | solution 1 for GlobalTheory.ArchMetric.lcv_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:07.18626+00:00
-- url     : https://prove2.me/submissions/62d68619-d9e9-4639-98fe-19989e4f1b35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}
namespace GlobalTheory.ArchMetric
theorem _root_.solution (hA : A.FG) {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → V}
    (he : IsLatticeFrame A e) :
    h.lcv_sq A = (∑ σ : K →+* ℂ, Real.log (h.gramDet σ e)) / finrank ℚ K -
      2 / finrank ℚ K *
        Real.log (Nat.card (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A)) := by
  rw [lcv_sq, degNorm, h.arDeg_eq_frameDeg hA he, frameDeg, ← Finset.mul_sum]
  ring
end GlobalTheory.ArchMetric
