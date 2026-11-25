-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_cons_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:03.916264+00:00
-- url     : https://prove2.me/submissions/de00bcbe-086e-4711-a637-558ec79d8b3a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_eq_prod

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
variable (h : ι → R)
include A
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {m : ℕ} (j : ι) (I : Fin (m + 1) → ι) :
    inter (D ∘ h) (Fin.cons j I : Fin (m + 2) → ι) = D ((∏ a, h (I a)) * h j) := by
  rw [inter_eq_prod A h, Fin.prod_univ_succ, mul_comm]
  simp
end GroundTheory.Arith.SchemeCoh
