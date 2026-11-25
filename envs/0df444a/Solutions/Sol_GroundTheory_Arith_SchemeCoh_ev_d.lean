-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ev_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:30.589383+00:00
-- url     : https://prove2.me/submissions/99565773-bd44-4eda-b9ec-80db64ccc83b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ev_res

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
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (σ : Cochain (discPresheaf A) U n) (i : Fin (n + 2) → ι) (x : X)
    (hx : x ∈ inter U i) :
    ev A x hx (d (discPresheaf A) U n σ i) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      ev A x (inter_le_comp U i k.succAbove hx) (σ (i ∘ k.succAbove)) := by
  rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, ev_res]
end GroundTheory.Arith.SchemeCoh
