-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockAssemble_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:27.893677+00:00
-- url     : https://prove2.me/submissions/36d50f94-aeab-4ee9-b991-567d01e39e02

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply_of_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply_of_ne
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable (R : Type*) [CommRing R]
variable {β R}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (d : ∀ a : Set.range β, Fiber β a → R) :
    blockAssemble β R (fun a => diagonal (d a)) =
      diagonal fun i => d (blockOf β i) ⟨i, rfl⟩ := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ (fun e => hij (congrArg Subtype.val e)), diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun e => h (by rw [e])
    rw [blockAssemble_apply_of_ne _ h, diagonal_apply_ne _ hij]
end GroundTheory.Automorphic.Parabolic
