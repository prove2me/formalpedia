-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.card_image_lt_refineFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:55.482243+00:00
-- url     : https://prove2.me/submissions/bd32c8d6-57cc-4287-b19c-5ecf09b947ff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_lt_refineFun_bound
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_refineFun_eq_iff
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {β γ : Fin n → ℕ} (h : ∃ i j, β i = β j ∧ γ i ≠ γ j) :
    (Finset.univ.image β).card < (Finset.univ.image (refineFun β γ)).card := by
  classical
  obtain ⟨i, j, hij, hγ⟩ := h
  set B := Finset.univ.sup γ + 1
  have hdiv : ∀ k, refineFun β γ k / B = β k := by
    intro k
    simp only [refineFun]
    rw [Nat.mul_add_div (Nat.succ_pos _), Nat.div_eq_of_lt (lt_refineFun_bound γ k), add_zero]
  have himg : Finset.univ.image β = (Finset.univ.image (refineFun β γ)).image (· / B) := by
    rw [Finset.image_image]
    congr 1
    funext k
    exact (hdiv k).symm
  rw [himg]
  refine lt_of_le_of_ne Finset.card_image_le fun hc => ?_
  have hinj := Finset.card_image_iff.1 hc
  have : refineFun β γ i = refineFun β γ j :=
    hinj (by simp) (by simp) (by simp only [hdiv, hij])
  exact hγ (refineFun_eq_iff.1 this).2
end GroundTheory.Automorphic.Parabolic
