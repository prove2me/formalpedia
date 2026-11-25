-- Prove2me | solution 1 for GlobalTheory.LieCombBaseChange.epsScale_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:14.445796+00:00
-- url     : https://prove2.me/submissions/a355d3ed-c0d2-4741-b8ba-94cf825f0cd7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
namespace GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']
private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (k : B →+* C) : spMap k ≫ spMap g = spMap (k.comp g) := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
end GlobalTheory.LieCombBaseChange
namespace GlobalTheory
open LieCombBaseChange
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.LieCombBaseChange
theorem _root_.solution (c : R) : spMap (epsScaleR c) ≫ (epsR R).hom = (epsR R).hom := by
  simp only [epsR, Over.mk_hom]
  rw [spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.LieCombBaseChange
