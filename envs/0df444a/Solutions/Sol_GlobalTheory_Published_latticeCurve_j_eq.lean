-- Prove2me | solution 1 for GlobalTheory.Published.latticeCurve_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:47.759927+00:00
-- url     : https://prove2.me/submissions/4a859f0f-027f-465b-8ddd-f551744c10db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Theorems.Thm_P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published
theorem _root_.solution (L : PeriodPair) :
    (_root_.GlobalTheory.latticeCurve L).j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    _root_.GlobalTheory.latticeCurve_c₄, _root_.GlobalTheory.latticeCurve_Δ]
  ring
end _root_.GlobalTheory.Published
end GlobalTheory.Published
