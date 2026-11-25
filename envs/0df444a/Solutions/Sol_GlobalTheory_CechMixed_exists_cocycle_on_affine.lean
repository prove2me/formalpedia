-- Prove2me | solution 1 for GlobalTheory.CechMixed.exists_cocycle_on_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:48.170325+00:00
-- url     : https://prove2.me/submissions/c5713a00-1809-4ac9-86ef-f5c28170ddcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
import Theorems.Thm_GlobalTheory_CechMixed_le_iSup_inf
import Theorems.Thm_GlobalTheory_CechMixed_exists_split
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_le_iSup_inf
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_KS_eq_of_rsT_eq
import Theorems.Thm_GlobalTheory_KS_exists_rsT_eq
import Theorems.Thm_GlobalTheory_KS_rsT_add
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
open GlobalTheory GlobalTheory.CechMixed
open GlobalTheory.KS
namespace GlobalTheory.CechMixed
theorem _root_.solution : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  intro X J K V U hV hU z hz
  choose b hb using fun k => exists_split hV (hU k) hz
  have glue : ∀ k k', ∃ t : Γ(X, U k ⊓ U k'), ∀ i, rsT t (V i ⊓ (U k ⊓ U k')) =
      rsT (b k' i) (V i ⊓ (U k ⊓ U k')) - rsT (b k i) (V i ⊓ (U k ⊓ U k')) := by
    intro k k'
    refine exists_rsT_eq (fun i => V i ⊓ (U k ⊓ U k')) (fun i => inf_le_right)
      (le_iSup_inf hV _) _ fun i j => ?_
    simp only [rsT_sub]
    rw [rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_right,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_right]
    have hi : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V i := inf_le_left.trans inf_le_left
    have hj : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V j := inf_le_right.trans inf_le_left
    have hk : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ U k ⊓ U k' := inf_le_right.trans inf_le_right
    have h1 := hb k i j _ hi hj (hk.trans inf_le_left)
    have h2 := hb k' i j _ hi hj (hk.trans inf_le_right)
    linear_combination h1 - h2
  choose t ht using glue
  have ht' : ∀ k k' i (W : X.Opens), W ≤ V i → W ≤ U k → W ≤ U k' →
      rsT (t k k') W = rsT (b k' i) W - rsT (b k i) W := by
    intro k k' i W hi hk hk'
    have e : W ≤ V i ⊓ (U k ⊓ U k') := le_inf hi (le_inf hk hk')
    have h := congrArg (fun s => rsT s W) (ht k k' i)
    simp only [rsT_sub] at h
    rwa [rsT_rsT inf_le_right e, rsT_rsT (inf_le_inf_left _ inf_le_right) e,
      rsT_rsT (inf_le_inf_left _ inf_le_left) e] at h
  refine ⟨t, fun i k => b k i, fun k k' k'' => ?_, fun i i' k => hb k i i' _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right,
    fun i k k' => ht' k k' i _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right⟩
  refine eq_of_rsT_eq (fun i => V i ⊓ (U k ⊓ U k' ⊓ U k'')) (fun i => inf_le_right)
    (le_iSup_inf hV _) _ _ fun i => ?_
  have e : V i ⊓ (U k ⊓ U k' ⊓ U k'') ≤ U k ⊓ U k' ⊓ U k'' := inf_le_right
  have e1 := (e.trans inf_le_left).trans inf_le_left
  have e2 := (e.trans inf_le_left).trans inf_le_right
  have e3 := e.trans inf_le_right
  simp only [rsT_add]
  rw [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e,
    ht' k k' i _ inf_le_left e1 e2, ht' k' k'' i _ inf_le_left e2 e3, ht' k k'' i _ inf_le_left e1 e3]
  ring
end GlobalTheory.CechMixed
