-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_eq_of_not_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:18.623811+00:00
-- url     : https://prove2.me/submissions/f03a6505-89f3-41fa-847f-68718b8f5c60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_psiN_rootElt
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relevant_involution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relevant_torus
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_diag_mul_permGL_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hψ₁ : ψ₀ ≠ 1) {w : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (h : ¬ Irrelevant ψ₀ w t) :
    sigma (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
  have key : ∀ i j : Fin n, i < j → w i < w j → ∀ a : F,
      psiN ψ₀ (rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a)) =
        psiN ψ₀ (rootElt i j a) := by
    intro i j hij hw a
    by_contra hne
    exact h ⟨i, j, hij, hw, a, hne⟩
  obtain ⟨b, hb⟩ : ∃ b, ψ₀ b ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hψ₁ (DFunLike.ext ψ₀ 1 fun x => by rw [hall x, AddChar.one_apply])
  have hψ0 : ∀ x, ψ₀ x ≠ 0 := fun x hx => by
    have := AddChar.map_add_eq_mul ψ₀ x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at this
    exact one_ne_zero this
  have hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1 := by
    intro i j hij hwv
    have hw : w i < w j := by rw [Fin.lt_def]; omega
    by_contra hj
    have hc : ((t (w i) : F) / (t (w j) : F)) ≠ 0 := div_ne_zero (Units.ne_zero _) (Units.ne_zero _)
    have := key i j hij hw (b / ((t (w i) : F) / (t (w j) : F)))
    rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
      if_pos hwv, if_neg hj, mul_div_cancel₀ _ hc] at this
    exact hb this
  have ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩) := by
    intro i hi hw
    set j : Fin n := ⟨i.val + 1, hi⟩ with hj
    have hij : i < j := by rw [Fin.lt_def]; simp [j]
    have hjv : j.val = i.val + 1 := rfl
    have hwv : (w j).val = (w i).val + 1 := by
      by_contra hne
      have := key i j hij hw b
      rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
        if_neg hne, if_pos hjv] at this
      exact hb this.symm
    set c : F := (t (w i) : F) / (t (w j) : F) with hc
    have hc1 : c = 1 := by
      by_contra hc1
      have hsub : c - 1 ≠ 0 := sub_ne_zero.2 hc1
      have := key i j hij hw (b / (c - 1))
      rw [psiN_rootElt ψ₀ (w.injective.ne (ne_of_lt hij)), psiN_rootElt ψ₀ (ne_of_lt hij),
        if_pos hwv, if_pos hjv] at this
      apply hb
      have e : b = c * (b / (c - 1)) - b / (c - 1) := by field_simp
      rw [e, AddChar.map_sub_eq_div, this, div_self (hψ0 _)]
    exact Units.ext ((div_eq_one_iff_eq (Units.ne_zero _)).1 hc1)
  exact sigma_diag_mul_permGL_eq t w (relevant_involution hB) (relevant_torus t hB ht)
end GroundTheory.Automorphic.Whittaker
