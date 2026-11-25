-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.isCoboundary_of_exactAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:49.955802+00:00
-- url     : https://prove2.me/submissions/9abca867-02c1-4499-b246-590b5c9ede74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_exists_triple
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_restrict_d_two
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_IsCocycle_diag
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
theorem _root_.solution (h : (cechLB f M D).ExactAt 1)
    (φ : ∀ a b, SecOn M (D a ⊓ D b)) (hφ : IsCocycle M D φ) : IsCoboundary M D φ := by
  have hex := (cechComplex_exactAt_succ_iff (secCube f M D) 0).1 h
  obtain ⟨x, hx⟩ : ∃ x : GlobalTheory.Cube.Term (secCube f M D) 2, ∀ i j (h : i < j),
      comp M D f x {i, j} (Finset.card_pair h.ne) =
        restrict M (le_inf (le_of_mem D (by simp)) (le_of_mem D (by simp))) (φ i j) := by
    have hne : ∀ s : {s : Finset κ // s.card = 2}, s.1.Nonempty := fun s =>
      Finset.card_pos.1 (by rw [s.2]; decide)
    have hcongr : ∀ {i j i' j' : κ} (_ : i = i') (_ : j = j') {W : X.Opens} (e : W ≤ D i ⊓ D j)
        (e' : W ≤ D i' ⊓ D j'), restrict M e (φ i j) = restrict M e' (φ i' j') := by
      rintro _ _ _ _ rfl rfl _ _ _; rfl
    refine ⟨fun s => SecOnR.of f M _ (restrict M (le_inf (le_of_mem D (s.1.min'_mem (hne s)))
      (le_of_mem D (s.1.max'_mem (hne s)))) (φ _ _)), fun i j h => ?_⟩
    exact hcongr (by simp [h.le]) (by simp [h.le]) (le_inf (le_of_mem D (Finset.min'_mem _ (by simp)))
      (le_of_mem D (Finset.max'_mem _ (by simp)))) _
  have hd : GlobalTheory.Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := exists_triple ht
    have e := restrict_d_two x hij hjk ht (W := ⨅ l ∈ ({i, j, k} : Finset κ), D l)
      (le_of_mem D (by simp)) (le_of_mem D (by simp)) (le_of_mem D (by simp))
    rw [restrict_self, hx i j hij, hx j k hjk, hx i k (hij.trans hjk), restrict_restrict,
      restrict_restrict, restrict_restrict, ← hφ i j k _ (le_of_mem D (by simp))
        (le_of_mem D (by simp)) (le_of_mem D (by simp))] at e
    exact e.trans (Eq.trans (b := 0) (by abel) rfl)
  obtain ⟨y, hy⟩ := (hex x).1 hd
  let ψ : ∀ a, SecOn M (D a) := fun a =>
    -restrict M (le_single D le_rfl) (comp M D f y {a} (Finset.card_singleton a))
  have hlt : ∀ a b, a < b →
      φ a b = restrict M inf_le_left (ψ a) - restrict M inf_le_right (ψ b) := by
    intro a b hab
    have e := restrict_d_one y hab (W := D a ⊓ D b) inf_le_left inf_le_right
    rw [show GlobalTheory.Cube.d _ 1 y = x from hy, hx a b hab, restrict_restrict, restrict_self] at e
    simp only [ψ, map_neg, restrict_restrict, e]
    abel
  refine ⟨ψ, fun a b => ?_⟩
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact hlt a b hab
  · rw [hφ.diag, sub_self]
  · rw [hφ.swap a b, hlt b a hab, map_sub, restrict_restrict, restrict_restrict, neg_sub]
end GlobalTheory.AbLaw.CechOne
