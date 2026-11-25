-- Prove2me | solution 1 for GlobalTheory.FiniteGL.mem_unipRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:48.728705+00:00
-- url     : https://prove2.me/submissions/b89b5167-032a-48a8-b084-9fa7ab221aaf

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
variable (k : Type) [Field k] {N : ℕ}
variable {k}
variable (k)
variable {k}
namespace GlobalTheory.FiniteGL
theorem _root_.solution {b : Fin N → ℕ} {u : GL (Fin N) k} :
    u ∈ unipRadical k b ↔ ∀ i j, b j ≤ b i → ((u : Matrix (Fin N) (Fin N) k) - 1) i j = 0 := Iff.rfl
end GlobalTheory.FiniteGL
