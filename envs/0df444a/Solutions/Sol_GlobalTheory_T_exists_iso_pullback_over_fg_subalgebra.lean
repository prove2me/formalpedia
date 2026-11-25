-- Prove2me | solution 1 for GlobalTheory.T.exists_iso_pullback_over_fg_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:30.350942+00:00
-- url     : https://prove2.me/submissions/ead9d7d7-6faa-42fc-ad3e-5941a00682f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebraStatement
import Theorems.Thm_GlobalTheory_smooth_models_iso_over_fg_subalgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  first | exact @GlobalTheory.smooth_models_iso_over_fg_subalgebra | exact GlobalTheory.smooth_models_iso_over_fg_subalgebra | (intros; apply GlobalTheory.smooth_models_iso_over_fg_subalgebra <;> assumption)
end _root_.GlobalTheory.T
