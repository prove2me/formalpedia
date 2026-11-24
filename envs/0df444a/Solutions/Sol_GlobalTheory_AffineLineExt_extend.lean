-- Prove2me | solution 1 for GlobalTheory.AffineLineExt.extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:31.758648+00:00
-- url     : https://prove2.me/submissions/cdeb5955-e97c-4d49-a1fd-e8692c7e28fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAffineLineMorphismToProperAcrossPoint
import Theorems.Thm_GlobalTheory_AffineLineExt_isPrincipalIdealRing_away
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_TorusConst_exists_extension
import Theorems.Thm_GlobalTheory_TorusConst_valuationRing_stalk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AffineLineExt
open Polynomial
namespace GlobalTheory.AffineLineExt
theorem _root_.solution : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩
end GlobalTheory.AffineLineExt
