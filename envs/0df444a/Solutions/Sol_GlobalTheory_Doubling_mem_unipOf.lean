-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_unipOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:12.243417+00:00
-- url     : https://prove2.me/submissions/fdf08f71-9d67-43d5-98fe-ddb8666e215e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
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
attribute [local simp] GlobalTheory.Doubling.val_aOf

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A)
variable {e mat}
namespace GlobalTheory.Doubling
theorem _root_.solution {g : G} : g ∈ unipOf e mat ↔ g ∈ siegelOf e mat ∧ leviMat e (mat g).1 = 1 :=
  ⟨by rintro ⟨p, hp, rfl⟩; exact ⟨p.2, congrArg Units.val hp⟩, fun h => ⟨⟨g, h.1⟩, Units.ext h.2, rfl⟩⟩
end GlobalTheory.Doubling
