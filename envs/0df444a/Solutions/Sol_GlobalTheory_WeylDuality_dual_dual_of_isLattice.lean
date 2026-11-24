-- Prove2me | solution 1 for GlobalTheory.WeylDuality.dual_dual_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:47.824841+00:00
-- url     : https://prove2.me/submissions/6677b21d-ff99-413b-b9ca-8c50bb83aba6

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℚ V] (B : LinearMap.BilinForm ℚ V)
    (hB : B.Nondegenerate) (hB' : B.IsSymm) (M : Submodule ℤ V) [M.IsLattice ℚ] :
    B.dualSubmodule (B.dualSubmodule M) = M := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  let b' := b.extendOfIsLattice ℚ
  have hrange : (Set.range b' : Set V) = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    funext k
    simp [b']
  have hM : Submodule.span ℤ (Set.range b') = M := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [← hM]
  exact B.dualSubmodule_dualSubmodule_of_basis hB hB' b'
end GlobalTheory.WeylDuality
