-- Prove2me | solution 1 for GlobalTheory.Spread.comp_eq_id_of_models
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:51.749805+00:00
-- url     : https://prove2.me/submissions/bd68a174-ae1b-40aa-acac-7b98e02c8a1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_eq_isoPullback_hom_comp_bcMap
import Theorems.Thm_GlobalTheory_Spread_hom_ext_bcMap


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
theorem _root_.solution [Flat p] [IsSeparated p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) (R : Subalgebra k V)
    (f : pullback p (spMap (algebraMap k R)) ⟶ pullback q (spMap (algebraMap k R)))
    (g : pullback q (spMap (algebraMap k R)) ⟶ pullback p (spMap (algebraMap k R)))
    (hf : f ≫ pullback.snd _ _ = pullback.snd _ _) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ')
    (hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ) :
    f ≫ g = 𝟙 _ := by

  have hu : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f = hτ'.isoPullback.hom ≫ bcMap q R.val := by
    apply eq_isoPullback_hom_comp_bcMap hτ' R
    · simpa only [Category.assoc] using hf'
    · rw [Category.assoc, Category.assoc, hf, bcMap_snd, ← Category.assoc,
        IsPullback.isoPullback_hom_snd]

  have hfst : bcMap p R.val ≫ f ≫ g ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% hu, IsPullback.isoPullback_hom_fst]
    exact hg'

  refine hom_ext_bcMap p R.val Subtype.val_injective (pullback.snd p (spMap (algebraMap k R)))
    ?_ ?_
  · rw [Category.assoc, hg, hf, Category.id_comp]
  · rw [Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hfst, bcMap_fst]
    · rw [Category.assoc, Category.assoc, hg, hf]
end GlobalTheory.Spread
