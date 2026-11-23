-- Prove2me | solution 1 for GlobalTheory.exists_bound_of_lattice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:26.10738+00:00
-- url     : https://prove2.me/submissions/a992ff1d-b161-4140-9a4b-994b2459e8c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Theorems.Thm_GlobalTheory_isBounded_latticeCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}
omit [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] {f : E → W}
    (hf : ∀ x ∈ L, Function.Periodic f x) (hc : Continuous f) : ∃ M, ∀ b, ‖f b‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isBounded_latticeCell L).isCompact_closure.exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun b ↦ ?_⟩
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) b
  have hvL : (v : E) ∈ L := ((Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le v.2
  rw [← hf v hvL b, add_comm]
  exact hM _ (subset_closure hv)
end GlobalTheory
