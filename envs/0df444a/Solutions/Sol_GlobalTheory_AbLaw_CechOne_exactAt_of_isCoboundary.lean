-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.exactAt_of_isCoboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:13:01.622421+00:00
-- url     : https://prove2.me/submissions/8562dd7e-e513-4e3b-8724-29f85fe12a18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_add_eq_of_ordered
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_restrict_d_two
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_IsCocycle_swap
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_cechComplex_exactAt_succ_iff
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
variable {κ : Type} (D : κ → X.Opens)
variable [LinearOrder κ]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
variable {D f M}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution
    (h : ∀ φ : ∀ a b, SecOn M (D a ⊓ D b), IsCocycle M D φ → IsCoboundary M D φ) :
    (cechLB f M D).ExactAt 1 := by
  refine (cechComplex_exactAt_succ_iff (secCube f M D) 0).2 fun x => ⟨fun hx => ?_, ?_⟩
  swap
  · rintro ⟨y, rfl⟩
    exact GlobalTheory.Cube.d_d _ _ y
  have hx' : GlobalTheory.Cube.d _ 2 x = 0 := hx
  let φ : ∀ a b, SecOn M (D a ⊓ D b) := fun a b =>
    if h : a < b then
      restrict M (le_pair D inf_le_left inf_le_right) (comp M D f x {a, b} (Finset.card_pair h.ne))
    else if h : b < a then
      -restrict M (le_pair D inf_le_right inf_le_left) (comp M D f x {b, a} (Finset.card_pair h.ne))
    else 0
  have hlt : ∀ a b (h : a < b), φ a b = restrict M (le_pair D inf_le_left inf_le_right)
      (comp M D f x {a, b} (Finset.card_pair h.ne)) := fun a b h => dif_pos h
  have hgt : ∀ a b (h : b < a), φ a b = -restrict M (le_pair D inf_le_right inf_le_left)
      (comp M D f x {b, a} (Finset.card_pair h.ne)) := fun a b h =>
    (dif_neg h.not_gt).trans (dif_pos h)
  have h0 : ∀ a, φ a a = 0 := fun a => (dif_neg (lt_irrefl a)).trans (dif_neg (lt_irrefl a))
  obtain ⟨ψ, hψ⟩ := h φ (by
    intro a b d W ha hb hd
    refine add_eq_of_ordered (κ := {i // W ≤ D i})
      (fun i j => restrict M (le_inf i.2 j.2) (φ i.1 j.1)) (fun i => ?_) (fun i j => ?_)
      (fun i j k hij hjk => ?_) ⟨a, ha⟩ ⟨b, hb⟩ ⟨d, hd⟩
    · rw [h0, map_zero]
    · rcases lt_trichotomy i j with hij | rfl | hij
      · rw [hlt i j hij, hgt j i hij, map_neg, restrict_restrict, restrict_restrict]
      · rw [h0, map_zero, neg_zero]
      · rw [hlt j i hij, hgt i j hij, map_neg, restrict_restrict, restrict_restrict, neg_neg]
    · have hij' : i.1 < j.1 := hij
      have hjk' : j.1 < k.1 := hjk
      have e := restrict_d_two x hij' hjk' (Finset.card_eq_three.2
        ⟨_, _, _, hij'.ne, (hij'.trans hjk').ne, hjk'.ne, rfl⟩) i.2 j.2 k.2
      rw [hx'] at e
      have e' := (map_zero (restrict M _)).symm.trans e
      rw [hlt i j hij, hlt j k hjk, hlt i k (hij.trans hjk), restrict_restrict, restrict_restrict,
        restrict_restrict, ← sub_eq_zero]
      exact Eq.trans (by abel) e'.symm)
  let y := GlobalTheory.Cube.termOneEquiv (secCube f M D) fun a =>
    SecOnR.of f M _ (-restrict M (le_of_mem D (Finset.mem_singleton_self a)) (ψ a))
  have hy : ∀ a, comp M D f y {a} (Finset.card_singleton a) =
      -restrict M (le_of_mem D (Finset.mem_singleton_self a)) (ψ a) := fun a =>
    GlobalTheory.Cube.termOneEquiv_apply _ _ a
  refine ⟨y, ?_⟩
  funext ⟨t, ht⟩
  obtain ⟨i, j, hij, rfl⟩ := exists_pair ht
  have hi : ⨅ l ∈ ({i, j} : Finset κ), D l ≤ D i := le_of_mem D (by simp)
  have hj : ⨅ l ∈ ({i, j} : Finset κ), D l ≤ D j := le_of_mem D (by simp)
  have e := restrict_d_one y hij hi hj
  have e₂ := congrArg (restrict M (le_inf hi hj)) ((hlt i j hij).symm.trans (hψ i j))
  rw [restrict_self, hy, hy] at e
  simp only [map_neg, map_sub, restrict_restrict, restrict_self] at e e₂
  exact e.trans (Eq.trans (by abel) e₂.symm)
end GlobalTheory.AbLaw.CechOne
