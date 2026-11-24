-- Prove2me | solution 1 for GlobalTheory.LinSchurLatt.isCompact_ball_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:37.222799+00:00
-- url     : https://prove2.me/submissions/d65d1656-9221-4ecb-8feb-142ef8b1fba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.LinSchurLatt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LinSchurLatt
theorem _root_.solution (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
end GlobalTheory.LinSchurLatt
