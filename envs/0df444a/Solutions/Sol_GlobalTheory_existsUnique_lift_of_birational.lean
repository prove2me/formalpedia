-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:53.180801+00:00
-- url     : https://prove2.me/submissions/a90488c5-1d27-4fb8-8464-58592d3b4539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_isIso_fromNormalization
import Theorems.Thm_GlobalTheory_lift_unique_of_isDominant
import Theorems.Thm_GlobalTheory_isDominant_fromSpecStalk_genericPoint
import Theorems.Thm_GlobalTheory_isIso_stalkMap_fromSpecStalk_genericPoint
import Theorems.Thm_GlobalTheory_apply_genericPoint_of_isDominant
import Theorems.Thm_GlobalTheory_isIso_fromNormalization_of_birational


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {U T Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (j : U ⟶ T) [IsIntegral U] [IsIntegral T]
    [IsNormalScheme T] [IsDominant j] [IsIso (j.stalkMap (genericPoint U))]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t => inferInstance
  let _ : Field (U.presheaf.stalk (genericPoint U)) := inferInstanceAs (Field U.functionField)
  have hsub : ∀ x y : Spec (U.presheaf.stalk (genericPoint U)), x = y := by
    intro x y
    apply PrimeSpectrum.ext
    rw [(Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top,
      (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top]
  have : Subsingleton (Spec (U.presheaf.stalk (genericPoint U))) := ⟨hsub⟩
  set η := U.fromSpecStalk (genericPoint U) with hη
  have := isDominant_fromSpecStalk_genericPoint U
  have := isIso_stalkMap_fromSpecStalk_genericPoint U
  have hgen : η (genericPoint _) = genericPoint U := apply_genericPoint_of_isDominant η
  have : IsIso ((η ≫ j).stalkMap (genericPoint _)) := by
    rw [Scheme.Hom.stalkMap_comp]
    have hj : ∀ y (_ : y = genericPoint U), IsIso (j.stalkMap y) := by
      rintro _ rfl; infer_instance
    exact IsIso.comp_isIso' (hj _ hgen) (isIso_stalkMap_fromSpecStalk_genericPoint U)
  have : QuasiCompact (η ≫ j) := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : QuasiSeparated (η ≫ j) := ⟨⟨fun _ _ _ => (Set.toFinite _).isCompact⟩⟩
  have := isIso_fromNormalization_of_birational (η ≫ j) hT
  obtain ⟨c, ⟨hc₁, hc₂⟩, hcu⟩ :=
    existsUnique_lift_of_isIso_fromNormalization (η ≫ j) p (η ≫ a) b
      (by rw [Category.assoc, h, Category.assoc])
  have hjc : j ≫ c = a :=
    lift_unique_of_isDominant η p (by rw [← Category.assoc, hc₁]) (by rw [Category.assoc, hc₂, h])
  exact ⟨c, ⟨hjc, hc₂⟩, fun c' hc' => hcu c' ⟨by rw [Category.assoc, hc'.1], hc'.2⟩⟩
end GlobalTheory
