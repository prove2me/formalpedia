-- Prove2me | solution 1 for GlobalTheory.Doubling.continuous_leviOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:56.754361+00:00
-- url     : https://prove2.me/submissions/a8a413ae-6237-4ce2-87e8-af84318e9e9d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self


attribute [local simp] GlobalTheory.Doubling.val_leviOf

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
theorem _root_.solution (h : Continuous mat) : Continuous (leviOf e mat) := by
  have h1 : Continuous fun M : Matrix ι ι A => leviMat e M :=
    continuous_matrix fun i j => (continuous_id.matrix_elem _ _).add (continuous_id.matrix_elem _ _)
  exact Units.continuous_iff.2 ⟨h1.comp (Units.continuous_val.comp (h.comp continuous_subtype_val)),
    (h1.comp (Units.continuous_coe_inv.comp (h.comp continuous_subtype_val))).congr fun p => by
      rw [← map_inv, val_leviOf, Subgroup.coe_inv, map_inv]; rfl⟩
end GlobalTheory.Doubling
