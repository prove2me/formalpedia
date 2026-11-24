-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.pull2_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:00:05.934449+00:00
-- url     : https://prove2.me/submissions/61dfb69d-9d95-4997-8e58-975bf48deb8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_pull_restrict_small_injective
import Theorems.Thm_GlobalTheory_CatCoh_Desc_descent_H2_surjective
import Theorems.Thm_GlobalTheory_CatCoh_Desc_acyclic_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution (H : HasLoc F) (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (cov : ∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → P S) :
    Function.Bijective (CoefMap.restrict F P.ι).pull2 :=
  have h := acyclic_of_cover F H P hP cov
  ⟨pull_restrict_small_injective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) fun T ↦ (h T).2.2.1,
    descent_H2_surjective F P hP (fun T ↦ (h T).1) (fun T ↦ (h T).2.1) (fun T ↦ (h T).2.2.1)
      fun T ↦ (h T).2.2.2⟩
end GlobalTheory.CatCoh.Desc
