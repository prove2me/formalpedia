-- Prove2me | solution 1 for GlobalTheory.KS.isCob_of_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:58.336316+00:00
-- url     : https://prove2.me/submissions/5f8958f9-8632-4645-b707-dc55007de980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCoboundaryOfMixedOverlaps
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_eq_of_rsT_eq
import Theorems.Thm_GlobalTheory_KS_exists_rsT_eq
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_rsT_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AbLaw.CechOne.kerEquiv_val
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
noncomputable section
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  intro X J K V U hU z z' b h1 h2 hz'
  obtain ⟨y', hy'⟩ := hz'
  have cov : ∀ O : X.Opens, O ≤ ⨆ k, O ⊓ U k := fun O x hx => by
    have : x ∈ ⨆ k, U k := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  have glue : ∀ i, ∃ t : Γ(X, V i), ∀ k, rsT t (V i ⊓ U k) = rsT (y' k) (V i ⊓ U k) - b i k := by
    intro i
    refine exists_rsT_eq (fun k => V i ⊓ U k) (fun k => inf_le_left) (cov _) _ fun k l => ?_
    have e : (V i ⊓ U k) ⊓ (V i ⊓ U l) ≤ V i ⊓ U k ⊓ U l := fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
    have e₁ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U k := inf_le_left
    have e₂ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U l := fun x hx => ⟨hx.1.1, hx.2⟩
    have e₃ : V i ⊓ U k ⊓ U l ≤ U k ⊓ U l := fun x hx => ⟨hx.1.2, hx.2⟩
    rw [← rsT_rsT e₁ e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => rsT s (V i ⊓ U k ⊓ U l)) (hy' k l)
    simp only [rsT_sub] at k₀
    rw [h2, rsT_rsT inf_le_right e₃, rsT_rsT inf_le_left e₃] at k₀
    simp only [rsT_sub]
    rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
    linear_combination k₀
  choose y hy using glue
  refine ⟨y, fun i i' => ?_⟩
  refine eq_of_rsT_eq (fun k => V i ⊓ V i' ⊓ U k) (fun k => inf_le_left) (cov _) _ _ fun k => ?_
  have e₁ : V i ⊓ V i' ⊓ U k ≤ V i ⊓ U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have e₂ : V i ⊓ V i' ⊓ U k ≤ V i' ⊓ U k := fun x hx => ⟨hx.1.2, hx.2⟩
  show rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) (V i ⊓ V i' ⊓ U k)
  rw [h1, rsT_sub, rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (y i'), ← rsT_rsT inf_le_left e₁ (y i), hy, hy]
  simp only [rsT_sub]
  rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
  ring
end GlobalTheory.KS
