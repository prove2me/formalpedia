-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.nsmul_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:40.628546+00:00
-- url     : https://prove2.me/submissions/25564ade-e2da-46cf-9056-fe9f062a7117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (pt : κ → Q) (h : ∀ i, N • pt i = 0) (t : κ → ZMod N) : N • ev pt h t = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]
end GlobalTheory.TorsionMatrix
