-- Prove2me | solution 1 for GlobalTheory.Spread.eq_isoPullback_hom_comp_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:47:01.656659+00:00
-- url     : https://prove2.me/submissions/397a077a-c36f-4975-97d6-6ed1e8f0e455

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.Spread
variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}
namespace GlobalTheory.Spread
theorem _root_.solution (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (R : Subalgebra k V) (σ : T ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : σ ≫ pullback.fst _ _ = τ) (h₂ : σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom) :
    σ = hτ.isoPullback.hom ≫ bcMap p R.val := by
  apply pullback.hom_ext
  · rw [h₁, Category.assoc, bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [h₂, Category.assoc, bcMap_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]
end GlobalTheory.Spread
