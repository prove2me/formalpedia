-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Sep.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:02.541606+00:00
-- url     : https://prove2.me/submissions/b51529c5-5543-4c3b-a91d-a817c433f231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms

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
variable {F} {T : C} {P Q : ∀ S, (T ⟶ S) → Prop} (hPQ : ∀ S u, P S u → Q S u)
  (hQ : ∀ S S' u (ψ : S ⟶ S'), Q S u → Q S' (u ≫ ψ))
  (sep : ∀ S u, Q S u → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (glue : ∀ S u, Q S u → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (van : ∀ S u, Q S u → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
include hPQ
namespace GlobalTheory.CatCoh.Desc
namespace Sep
theorem _root_.solution (h : Sep F P) : Sep F Q := fun x hx ↦ h x fun S u hp ↦ hx S u (hPQ S u hp)
end Sep
end GlobalTheory.CatCoh.Desc
