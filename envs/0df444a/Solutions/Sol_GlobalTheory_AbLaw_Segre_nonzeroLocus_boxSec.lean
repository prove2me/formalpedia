-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.nonzeroLocus_boxSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:19.314227+00:00
-- url     : https://prove2.me/submissions/46687338-7140-4c0f-8afb-5920065e126a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_basicOpen_ap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution (s : LB.Sec H) (t : LB.Sec K) :
    nonzeroLocus (boxSec p q s t) = p ⁻¹ᵁ nonzeroLocus s ⊓ q ⁻¹ᵁ nonzeroLocus t := by
  have key : ∀ a : H.ι × K.ι, P.basicOpen ((boxSec p q s t).f a) =
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ p ⁻¹ᵁ X.basicOpen (s.f a.1)) ⊓
      ((p ⁻¹ᵁ H.U a.1 ⊓ q ⁻¹ᵁ K.U a.2) ⊓ q ⁻¹ᵁ Y.basicOpen (t.f a.2)) := fun a =>
    (P.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (basicOpen_ap p _ _) (basicOpen_ap q _ _))
  ext y
  constructor
  · intro h
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have ha := (key a).le ha
    exact ⟨TopologicalSpace.Opens.mem_iSup.2 ⟨a.1, ha.1.2⟩, TopologicalSpace.Opens.mem_iSup.2 ⟨a.2, ha.2.2⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ k, X.basicOpen (s.f k) from h₁)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ k, Y.basicOpen (t.f k) from h₂)
    have hy : y ∈ p ⁻¹ᵁ H.U i ⊓ q ⁻¹ᵁ K.U j := ⟨X.basicOpen_le _ hi, Y.basicOpen_le _ hj⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (key (i, j)).ge ⟨⟨hy, hi⟩, hy, hj⟩⟩
end GlobalTheory.AbLaw.Segre
