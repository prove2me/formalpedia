-- Prove2me | solution 1 for GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:59.857134+00:00
-- url     : https://prove2.me/submissions/864cb8c4-ef49-47aa-b643-aee88ddad63d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Theorems.Thm_GlobalTheory_ThickeningDetermines_secIdeal_le_ker
import Theorems.Thm_GlobalTheory_ThickeningDetermines_eq_zero_of_secIdeal_eq_bot
import Theorems.Thm_GlobalTheory_grpObj_geometricallyIntegral_of_smooth
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThickeningDetermines
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom], (∀ (N : LB H.left), N.IsLB → ∀ s : LB.Sec N, (∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) → ∀ j, s.f j = 0) ∧ (∀ (Y : Over (Spec (CommRingCat.of R))) [IsSeparated Y.hom] (f g : H ⟶ Y), (∀ n : ℕ, (fstG I n H).left ≫ f.left = (fstG I n H).left ≫ g.left) → f = g) := by
  intro R _ _ I hI H _ _ _
  have := grpObj_geometricallyIntegral_of_smooth _ H
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H η[H] (fun p ↦ inferInstance)
  refine ⟨fun N hN s hs ↦ eq_zero_of_secIdeal_eq_bot hN s ?_, fun Y _ f g h ↦ ?_⟩
  · have := key _ (secIdeal hN s).subschemeι fun n ↦ by
      have : IsClosedImmersion (thick R I n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I n H).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
      exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
    exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this
  · have := key _ (equalizer.ι f g).left fun n ↦
      ⟨(equalizer.lift (fstG I n H) (Over.OverMorphism.ext (h n))).left,
        by rw [← Over.comp_left, equalizer.lift_ι]⟩
    refine Over.OverMorphism.ext ?_
    rw [← cancel_epi (equalizer.ι f g).left]
    exact congrArg CommaMorphism.left (equalizer.condition f g)
end GlobalTheory
