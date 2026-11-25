-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.ev_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:41.112147+00:00
-- url     : https://prove2.me/submissions/ed5d398e-52ee-4232-bb04-92d7bb1bf25c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
import Theorems.Thm_GlobalTheory_TorsionMatrix_nsmul_ev

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
theorem _root_.solution {pt : κ → Q} (h : ∀ i, N • pt i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y) :
    Function.Injective (ev pt h) := fun a b hab =>
  (hb _ (nsmul_ev pt h b)).unique hab rfl
end GlobalTheory.TorsionMatrix
