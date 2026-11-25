-- Prove2me | solution 1 for GlobalTheory.ArchMetric.arDeg_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:13.388567+00:00
-- url     : https://prove2.me/submissions/14074746-819e-47ac-9672-9ef52c8c006a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Theorems.Thm_GlobalTheory_ArchMetric_scale_gramDet

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
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchMetric
theorem _root_.solution (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (hA : A.FG) :
    (h.scale c hc).arDeg A =
      h.arDeg A - finrank (𝓞 K) A / 2 * ∑ σ : K →+* ℂ, Real.log (c σ) := by
  obtain ⟨e, he⟩ := exists_isLatticeFrame hA
  have : ∀ σ, 1 / 2 * Real.log ((h.scale c hc).gramDet σ e) =
      finrank (𝓞 K) A / 2 * Real.log (c σ) + 1 / 2 * Real.log (h.gramDet σ e) := fun σ => by
    rw [scale_gramDet, Real.log_mul (pow_pos (hc σ) _).ne'
      (h.gramDet_pos σ he.linearIndependent).ne', Real.log_pow, Fintype.card_fin]
    ring
  rw [arDeg_eq_frameDeg _ hA he, arDeg_eq_frameDeg _ hA he, frameDeg, frameDeg]
  simp only [this, Finset.sum_add_distrib, Finset.mul_sum]
  ring
end GlobalTheory.ArchMetric
