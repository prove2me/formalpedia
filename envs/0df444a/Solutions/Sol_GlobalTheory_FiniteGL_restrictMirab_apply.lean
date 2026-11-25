-- Prove2me | solution 1 for GlobalTheory.FiniteGL.restrictMirab_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:29.728442+00:00
-- url     : https://prove2.me/submissions/ea31aaf9-7a1f-40ed-a7d1-88fc8e4ffea6

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (n + 1)) k) V) (h : mirabSub k n) :
    restrictMirab n ρ h = ρ (h : GL (Fin (n + 1)) k) := rfl
end GlobalTheory.FiniteGL
