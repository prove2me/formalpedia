-- Prove2me | solution 1 for GlobalTheory.essFiniteType_stalkMap_SpecMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:03.456246+00:00
-- url     : https://prove2.me/submissions/7df9fe87-7cc3-4781-82a6-b85e1a68a5c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {o : CommRingCat.{u}} [IsDedekindDomain o]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o) [LocallyOfFiniteType g]
namespace GlobalTheory
theorem _root_.solution {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : φ.hom.EssFiniteType) (x : Spec B) : ((Spec.map φ).stalkMap x).hom.EssFiniteType := by
  refine .of_comp ((Spec A).presheaf.germ ⊤ (Spec.map φ x) (Opens.mem_top _)).hom ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, CommRingCat.hom_comp]
  refine .comp ?_ (essFiniteType_germ (isAffineOpen_top _) _ _)
  have h : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  change (Spec.map φ).appTop.hom.EssFiniteType
  rw [h]
  exact .comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).2).essFiniteType (hφ.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2).essFiniteType)
end GlobalTheory
