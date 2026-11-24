-- Prove2me | solution 1 for GlobalTheory.Doubling.continuous_aOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:45:04.120049+00:00
-- url     : https://prove2.me/submissions/b08f4a8f-d495-42db-bdd1-1a0264db3e1d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_continuous_leviOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)
variable {e mat}
variable [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]
namespace GlobalTheory.Doubling
theorem _root_.solution (h : Continuous mat) : Continuous (aOf e mat) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp (continuous_leviOf h)).matrix_det,
    (Units.continuous_coe_inv.comp (continuous_leviOf (e := e) h)).matrix_det.congr fun p => by
      rw [← map_inv, aOf, MonoidHom.comp_apply, map_inv]; rfl⟩
end GlobalTheory.Doubling
