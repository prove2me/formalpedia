-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.isCoboundary_of_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:57:29.105504+00:00
-- url     : https://prove2.me/submissions/65a9bd29-607c-4101-8830-3a5a1fdc84f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_le_iSup_inf
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_existsUnique_glue
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_ext_of_cover
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_glue
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_ext_of_cover
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {I J : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (P : J → X.Opens) (τ : J → I) (hP : ∀ k, P k ≤ O (τ k))
    (hc : ∀ a, O a ≤ ⨆ k, P k) (ψ' : ∀ k, SecOn M (P k))
    (h : ∀ k l, restrict M (inf_le_inf (hP k) (hP l)) (φ (τ k) (τ l)) =
      restrict M inf_le_left (ψ' k) - restrict M inf_le_right (ψ' l)) :
    IsCoboundary M O φ := by
  have hglue : ∀ a, ∃ ψ : SecOn M (O a), ∀ k, restrict M (inf_le_left : O a ⊓ P k ≤ O a) ψ =
      restrict M (inf_le_inf le_rfl (hP k)) (φ a (τ k)) + restrict M inf_le_right (ψ' k) := by
    intro a
    refine (existsUnique_glue (fun k => O a ⊓ P k) (fun k => inf_le_left) (le_iSup_inf (hc a))
      _ fun k l => ?_).exists
    have hk : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ P k := inf_le_left.trans inf_le_right
    have hl : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ P l := inf_le_right.trans inf_le_right
    have ha : O a ⊓ P k ⊓ (O a ⊓ P l) ≤ O a := inf_le_left.trans inf_le_left
    have h1 := congrArg (restrict M (le_inf hk hl)) (h k l)
    have h2 := hφ a (τ k) (τ l) _ ha (hk.trans (hP k)) (hl.trans (hP l))
    simp only [map_add, map_sub, restrict_restrict] at h1 h2 ⊢
    rw [← h2, h1]
    abel
  choose ψ hψ using hglue
  refine ⟨ψ, fun a b => ext_of_cover (fun k => O a ⊓ O b ⊓ P k) (fun k => inf_le_left)
    (le_iSup_inf (inf_le_left.trans (hc a))) fun k => ?_⟩
  have ha : O a ⊓ O b ⊓ P k ≤ O a := inf_le_left.trans inf_le_left
  have hb : O a ⊓ O b ⊓ P k ≤ O b := inf_le_left.trans inf_le_right
  have hk : O a ⊓ O b ⊓ P k ≤ P k := inf_le_right
  have h1 := congrArg (restrict M (le_inf ha hk)) (hψ a k)
  have h2 := congrArg (restrict M (le_inf hb hk)) (hψ b k)
  have h3 := hφ a b (τ k) _ ha hb (hk.trans (hP k))
  simp only [map_add, map_sub, restrict_restrict] at h1 h2 h3 ⊢
  rw [h1, h2, ← h3]
  abel
end GlobalTheory.AbLaw.CechOne
