-- Prove2me | solution 1 for GlobalTheory.Doubling.isClosed_siegelOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:27.822876+00:00
-- url     : https://prove2.me/submissions/7b963969-fae5-4cd2-95fa-ade319f7bc5f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_mem_siegelOf
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
variable [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]
namespace GlobalTheory.Doubling
theorem _root_.solution [T2Space A] (h : Continuous mat) : IsClosed (siegelOf e mat : Set G) := by
  have h1 : ∀ i j, Continuous fun g => (mat g).1 i j := fun i j => (Units.continuous_val.comp h).matrix_elem i j
  have : (siegelOf e mat : Set G) = ⋂ i, ⋂ j, {g | (mat g).1 (e (.inr i)) (e (.inl j)) + (mat g).1 (e (.inr i)) (e (.inr j)) =
      (mat g).1 (e (.inl i)) (e (.inl j)) + (mat g).1 (e (.inl i)) (e (.inr j))} := by
    ext g; simp [mem_siegelOf, keepsDiag_iff]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ((h1 _ _).add (h1 _ _)) ((h1 _ _).add (h1 _ _))
end GlobalTheory.Doubling
