-- Prove2me | solution 1 for GlobalTheory.FiniteGL.genericChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:09:04.172611+00:00
-- url     : https://prove2.me/submissions/711f67b6-ea90-4520-8314-4634cf19bd44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace GlobalTheory.FiniteGL
theorem _root_.solution (ψ₀ : AddChar k ℂ) (u : uniSub k n) :
    genericChar n ψ₀ u =
      ψ₀ (supd (((u : mirabSub k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) := rfl
end GlobalTheory.FiniteGL
