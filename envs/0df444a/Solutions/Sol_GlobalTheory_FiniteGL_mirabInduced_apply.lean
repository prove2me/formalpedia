-- Prove2me | solution 1 for GlobalTheory.FiniteGL.mirabInduced_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:26.021899+00:00
-- url     : https://prove2.me/submissions/38422a54-f5d4-4c91-912a-7b799c5bb1c0

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
theorem _root_.solution (ψ₀ : AddChar k ℂ) (h x : mirabSub k n) (f : MirabInducedSpace n ψ₀) :
    (mirabInduced n ψ₀ h f : mirabSub k n → ℂ) x = (f : mirabSub k n → ℂ) (x * h) := rfl
end GlobalTheory.FiniteGL
