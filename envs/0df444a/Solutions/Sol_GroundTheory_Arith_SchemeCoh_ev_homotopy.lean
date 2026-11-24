-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ev_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:09.272133+00:00
-- url     : https://prove2.me/submissions/8ac35af9-94b1-4696-b33d-9d95ace8175f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable (A : X → AddCommGrpCat.{u})

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) (j : Fin (n + 1) → ι)
    (x : X) (hx : x ∈ inter U j) :
    ev A x hx (homotopy U A σ j) = ev A x (mem_inter_cons U j hx)
      (σ (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j)) := rfl
end GroundTheory.Arith.SchemeCoh
