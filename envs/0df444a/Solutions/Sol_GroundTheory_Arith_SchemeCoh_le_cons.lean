-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.le_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:07.838866+00:00
-- url     : https://prove2.me/submissions/5139a874-c848-4e09-b3f7-7dcb78c0b340

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech

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
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (j : ι) (I : Fin (n + 1) → ι) :
    inter U (Fin.cons j I : Fin (n + 2) → ι) ≤ inter U I := by
  intro x hx
  rw [mem_inter_iff] at hx ⊢
  intro a
  simpa using hx a.succ
end GroundTheory.Arith.SchemeCoh
