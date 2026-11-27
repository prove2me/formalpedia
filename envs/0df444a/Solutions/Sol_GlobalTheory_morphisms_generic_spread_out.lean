-- Prove2me | solution 1 for GlobalTheory.morphisms_generic_spread_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:03.976173+00:00
-- url     : https://prove2.me/submissions/62b1d422-3377-4f2b-bbf2-6472f159506b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MorphismsGenericSpreadOut
import Theorems.Thm_GlobalTheory_GenericSpread_exists_away_of_fg
import Theorems.Thm_GlobalTheory_Spread_eq_bcMap
import Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by
  intro R K _ _ _ _ _ _ B Z pB pZ I _ u hqc hqs hlfp hu
  have := hqc
  have := hqs
  have := hlfp
  obtain ⟨S, ψ, hSfg, -, hψ⟩ :=
    GlobalTheory.Spread.exists_fg_forall_comp_eq pB pZ u hu ⊥ Subalgebra.fg_bot
  obtain ⟨f, hf0, g, l, hgl⟩ := GlobalTheory.GenericSpread.exists_away_of_fg S hSfg
  have hmono : Mono (spMap (algebraMap R (Localization.Away f))) := inferInstance
  refine ⟨f, hf0, fun i => GlobalTheory.Spread.bcMap pB g ≫ ψ i, fun i => ⟨?_, fun j hj => ?_⟩⟩
  · rw [Category.assoc, (hψ i).1, ← Category.assoc, GlobalTheory.Spread.bcMap_fst]
  · have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap l.toRingHom := by
      apply (cancel_mono (spMap (algebraMap R (Localization.Away f)))).mp
      rw [Category.assoc, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp, ← pullback.condition,
        ← pullback.condition, ← Category.assoc, hj]
    have hjb : j = GlobalTheory.Spread.bcMap pB l := GlobalTheory.Spread.eq_bcMap pB l hj hj2
    rw [hjb, ← Category.assoc, GlobalTheory.Spread.bcMap_comp_of_eq pB g l S.val hgl]
    exact (hψ i).2
end GlobalTheory
