-- Prove2me | solution 1 for GlobalTheory.FiniteGL.lineRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:16.027336+00:00
-- url     : https://prove2.me/submissions/aef9b930-3c5c-40d2-91d7-955b6b901577

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
namespace GlobalTheory.FiniteGL
theorem _root_.solution {G : Type} [Group G] (χ : G →* ℂ) (g : G) (v : Fin 1 → ℂ) : lineRep χ g v = χ g • v := rfl
end GlobalTheory.FiniteGL
