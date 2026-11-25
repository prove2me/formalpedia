-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:55.056982+00:00
-- url     : https://prove2.me/submissions/ad17cec4-6656-4f65-9470-8389899fe31b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_le_iSup_inf
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_isCoboundary_of_refine
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
theorem _root_.solution {κ : Type} {D : κ → X.Opens} {V : X.Opens} (hD : ∀ i, D i ≤ V)
    (hc : V ≤ ⨆ i, D i) (h1 : ∀ i, CechHOneVanishesOnOpen M (D i))
    (h2 : ∀ θ : ∀ i j, SecOn M (D i ⊓ D j), IsCocycle M D θ → IsCoboundary M D θ) :
    CechHOneVanishesOnOpen M V := by
  intro I O hO hcO φ hφ
  choose σ hσ using fun i => h1 i I (fun a => D i ⊓ O a) (fun _ => inf_le_left)
    (le_iSup_inf ((hD i).trans hcO))
    (fun a b => restrict M (inf_le_inf inf_le_right inf_le_right) (φ a b)) (by
      intro a b d W ha hb hd
      simp only [restrict_restrict]
      exact hφ a b d W (ha.trans inf_le_right) (hb.trans inf_le_right) (hd.trans inf_le_right))
  have hσ' : ∀ i a b (W : X.Opens) (hi : W ≤ D i) (ha : W ≤ O a) (hb : W ≤ O b),
      restrict M (le_inf ha hb) (φ a b) =
        restrict M (le_inf hi ha) (σ i a) - restrict M (le_inf hi hb) (σ i b) := by
    intro i a b W hi ha hb
    have h := congrArg (restrict M (le_inf (le_inf hi ha) (le_inf hi hb))) (hσ i a b)
    simpa only [map_sub, restrict_restrict] using h
  have hglue : ∀ i j, ∃ θ : SecOn M (D i ⊓ D j), ∀ a,
      restrict M (inf_le_left : D i ⊓ D j ⊓ O a ≤ D i ⊓ D j) θ =
        restrict M (inf_le_inf_right _ inf_le_left) (σ i a) -
          restrict M (inf_le_inf_right _ inf_le_right) (σ j a) := by
    intro i j
    refine (existsUnique_glue (fun a => D i ⊓ D j ⊓ O a) (fun a => inf_le_left)
      (le_iSup_inf ((inf_le_left.trans (hD i)).trans hcO)) _ fun a b => ?_).exists
    have ha : D i ⊓ D j ⊓ O a ⊓ (D i ⊓ D j ⊓ O b) ≤ O a := inf_le_left.trans inf_le_right
    have hb : D i ⊓ D j ⊓ O a ⊓ (D i ⊓ D j ⊓ O b) ≤ O b := inf_le_right.trans inf_le_right
    have e1 := hσ' i a b _ (inf_le_left.trans (inf_le_left.trans inf_le_left)) ha hb
    have e2 := hσ' j a b _ (inf_le_left.trans (inf_le_left.trans inf_le_right)) ha hb
    simp only [map_sub, restrict_restrict]
    rw [sub_eq_sub_iff_sub_eq_sub, ← e1, ← e2]
  choose θ hθ using hglue
  have hθ' : ∀ i j a (W : X.Opens) (hi : W ≤ D i) (hj : W ≤ D j) (ha : W ≤ O a),
      restrict M (le_inf hi hj) (θ i j) =
        restrict M (le_inf hi ha) (σ i a) - restrict M (le_inf hj ha) (σ j a) := by
    intro i j a W hi hj ha
    have h := congrArg (restrict M (le_inf (le_inf hi hj) ha)) (hθ i j a)
    simpa only [map_sub, restrict_restrict] using h
  obtain ⟨ξ, hξ⟩ := h2 θ (by
    intro i j k W hi hj hk
    refine ext_of_cover (fun a => W ⊓ O a) (fun a => inf_le_left)
      (le_iSup_inf ((hi.trans (hD i)).trans hcO)) fun a => ?_
    simp only [map_add, restrict_restrict]
    rw [hθ' i j a _ (inf_le_left.trans hi) (inf_le_left.trans hj) inf_le_right,
      hθ' j k a _ (inf_le_left.trans hj) (inf_le_left.trans hk) inf_le_right,
      hθ' i k a _ (inf_le_left.trans hi) (inf_le_left.trans hk) inf_le_right]
    abel)
  refine isCoboundary_of_refine hφ (fun p : κ × I => D p.1 ⊓ O p.2) Prod.snd (fun _ => inf_le_right)
    (fun a => (le_iSup_inf ((hO a).trans hc)).trans (iSup_le fun i =>
      (le_inf inf_le_right inf_le_left).trans (le_iSup (fun p : κ × I => D p.1 ⊓ O p.2) (i, a))))
    (fun p => σ p.1 p.2 - restrict M inf_le_left (ξ p.1)) fun p q => ?_
  have hi : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ D p.1 := inf_le_left.trans inf_le_left
  have hj : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ D q.1 := inf_le_right.trans inf_le_left
  have ha : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ O p.2 := inf_le_left.trans inf_le_right
  have hb : D p.1 ⊓ O p.2 ⊓ (D q.1 ⊓ O q.2) ≤ O q.2 := inf_le_right.trans inf_le_right
  have e1 := hσ' p.1 p.2 q.2 _ hi ha hb
  have e2 := hθ' p.1 q.1 q.2 _ hi hj hb
  have e3 := congrArg (restrict M (le_inf hi hj)) (hξ p.1 q.1)
  simp only [map_sub, restrict_restrict] at e3 ⊢
  rw [e1, sub_sub_sub_comm, ← e3, e2]
  abel
end GlobalTheory.AbLaw.CechOne
