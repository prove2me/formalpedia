-- Prove2me | solution 1 for GlobalTheory.exists_radius_lattice_translate_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:20.889495+00:00
-- url     : https://prove2.me/submissions/0f29bd72-cb91-48c3-9f1a-94714ee44801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : ∃ R : ℝ, 0 < R ∧ ∀ y : V, ∃ l : L, ‖y + l‖ ≤ R := by
  classical
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  refine ⟨∑ i, ‖b i‖ + 1, by positivity, fun y => ?_⟩
  have hmem : (ZSpan.floor b y : V) ∈ L :=
    ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ).le (ZSpan.floor b y).2
  refine ⟨-⟨_, hmem⟩, ?_⟩
  have h := ZSpan.norm_fract_le b y
  rw [ZSpan.fract_apply] at h
  have e : y + ((-⟨_, hmem⟩ : L) : V) = y - (ZSpan.floor b y : V) := by
    rw [Submodule.coe_neg, sub_eq_add_neg]
  rw [e]
  linarith
end GlobalTheory
