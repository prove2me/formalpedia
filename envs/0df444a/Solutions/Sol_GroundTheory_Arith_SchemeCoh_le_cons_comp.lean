-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.le_cons_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:08.500245+00:00
-- url     : https://prove2.me/submissions/161c88f6-2ffd-4c28-80a9-3e3f4702ef48

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ


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
theorem _root_.solution {n : ℕ} (j : ι) (J : Fin (n + 2) → ι) (k : Fin (n + 2)) :
    inter U (Fin.cons j J : Fin (n + 3) → ι) ≤
      inter U (Fin.cons j (J ∘ k.succAbove) : Fin (n + 2) → ι) := by
  have := inter_le_comp U (Fin.cons j J : Fin (n + 3) → ι) k.succ.succAbove
  rwa [cons_comp_succAbove_succ] at this
end GroundTheory.Arith.SchemeCoh
