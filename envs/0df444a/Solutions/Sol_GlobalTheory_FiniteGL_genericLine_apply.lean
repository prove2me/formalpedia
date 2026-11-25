-- Prove2me | solution 1 for GlobalTheory.FiniteGL.genericLine_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:15.420831+00:00
-- url     : https://prove2.me/submissions/63584ccd-50a0-40fc-8dc1-c62c7c1e8a80

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
theorem _root_.solution (ψ₀ : AddChar k ℂ) (u : uniSub k n) (z : ℂ) :
    genericLine n ψ₀ u z = genericChar n ψ₀ u * z := rfl
end GlobalTheory.FiniteGL
