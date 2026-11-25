-- Prove2me | solution 1 for GlobalTheory.PullBdd.isBddSec_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:42.52745+00:00
-- url     : https://prove2.me/submissions/d28703fb-dd3f-499d-91a8-f7f3a46b5efe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
import Theorems.Thm_GlobalTheory_PullBdd_castFrame_mem_GG
import Theorems.Thm_GlobalTheory_PullBdd_castFrame_mem_Bor
import Theorems.Thm_GlobalTheory_PullBdd_bchar_castFrame
import Theorems.Thm_GlobalTheory_PullBdd_castFrame_rmul
import Theorems.Thm_GlobalTheory_PullBdd_castFrame_lact
import Theorems.Thm_GlobalTheory_PullBdd_lact_rmul
import Theorems.Thm_GlobalTheory_PullBdd_lact_lact
import Theorems.Thm_GlobalTheory_PullBdd_dmin_lact
import Theorems.Thm_GlobalTheory_PullBdd_nfac_cast
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_FrameFibre_lact_mem_GG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PullBdd
theorem _root_.solution (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0)
    (β : GL (Fin r) E)
    (hβ : ∀ u v, herm Y.Gm ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm Y.Gm u v)
    (hΓ : ∀ γ ∈ X.Γ, β * γ * β⁻¹ ∈ Y.Γ) (la : Wt Y.Ψ r)
    (hχX : ∀ γ ∈ X.Γ, X.χ (castWt hΨ la) γ = 1) (hχY : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (Q : Frame Y.Ψ r → ℂ) (hQ : Y.IsBddSec la Q) :
    X.IsBddSec (castWt hΨ la) (fun x => Q (lact β (castFrame hΨ x))) := by
  obtain ⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩ := hQ
  have hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom := by
    intro x hx
    have h1 := castFrame_mem_GG hΨ hx
    rw [hG, hp] at h1
    exact GlobalTheory.FrameFibre.lact_mem_GG hβ h1
  refine ⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩
  · have hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x)) := by
      rw [differentiable_pi]; intro τ; rw [differentiable_pi]; intro a; rw [differentiable_pi]; intro b
      simp only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      fun_prop
    exact hQd.comp hd.differentiableOn hmaps
  · intro x hx b hb
    simp only
    rw [castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]
  · intro γ hγ x hx
    simp only
    rw [hχX γ hγ, one_mul, castFrame_lact, lact_lact,
      show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx),
      hχY _ (hΓ γ hγ), one_mul]
  · refine le_trans (le_of_eq ?_) (hC _ (hmaps x hx))
    unfold Data.pnorm
    congr 1
    simp only [dmin_lact hβ]
    rw [← hG]
    exact (nfac_cast hΨ X.Gm la x).symm
end GlobalTheory.PullBdd
