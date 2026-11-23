-- Prove2me | solution 1 for GlobalTheory.mem_lattice_iff_of_periods_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:50.795977+00:00
-- url     : https://prove2.me/submissions/91774a31-6e6a-44d3-9b2e-90c20a2bf119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  rw [mem_lattice]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · constructor <;> rintro ⟨m, n, rfl⟩ <;> exact ⟨n, m, by ring⟩
  · simp
end GlobalTheory
