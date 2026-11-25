-- Prove2me | solution 1 for GlobalTheory.LieCombBaseChange.dualMap_epsScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:45:52.86162+00:00
-- url     : https://prove2.me/submissions/49d76db4-d5ab-4b02-996c-823c97f95b36

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
theorem _root_.solution (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces]
  congr 1
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [epsScaleR, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, mul_comm]
end GlobalTheory.LieCombBaseChange
