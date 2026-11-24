-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_isIso_fromNormalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:02.657794+00:00
-- url     : https://prove2.me/submissions/1b64edd7-23a6-43b5-835e-126bd50b65bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

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
theorem _root_.solution (j : U ⟶ T) [QuasiCompact j]
    [QuasiSeparated j] [IsIso j.fromNormalization] (p : Z ⟶ Y) [IsIntegralHom p]
    (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hfac : j = pullback.lift a j h ≫ pullback.snd p b := (pullback.lift_snd _ _ _).symm
  set d := j.normalizationDesc (pullback.lift a j h) (pullback.snd p b) hfac with hd
  have e1 : j ≫ inv j.fromNormalization = j.toNormalization := by
    rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
  refine ⟨inv j.fromNormalization ≫ d ≫ pullback.fst p b, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, e1, hd, Scheme.Hom.toNormalization_normalizationDesc_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, hd,
      Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]
  · rintro c ⟨hc₁, hc₂⟩
    have hl : c ≫ p = 𝟙 T ≫ b := by rw [hc₂, Category.id_comp]
    have key : j.fromNormalization ≫ pullback.lift c (𝟙 T) hl = d := by
      apply Scheme.Hom.normalization.hom_ext j _ _ (pullback.snd p b)
      · rw [Scheme.Hom.toNormalization_fromNormalization_assoc, hd,
          Scheme.Hom.toNormalization_normalizationDesc]
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hc₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
      · rw [hd, Scheme.Hom.normalizationDesc_comp]
    calc c = pullback.lift c (𝟙 T) hl ≫ pullback.fst p b := (pullback.lift_fst _ _ _).symm
      _ = inv j.fromNormalization ≫ (j.fromNormalization ≫ pullback.lift c (𝟙 T) hl) ≫
            pullback.fst p b := by rw [Category.assoc, IsIso.inv_hom_id_assoc]
      _ = _ := by rw [key]
end GlobalTheory
