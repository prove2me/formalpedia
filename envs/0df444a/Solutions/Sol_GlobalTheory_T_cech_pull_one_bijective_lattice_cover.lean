-- Prove2me | solution 1 for GlobalTheory.T.cech_pull_one_bijective_lattice_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:35.555618+00:00
-- url     : https://prove2.me/submissions/51b1326f-d2b5-4b47-b24b-8b4d8147ec30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCoverStatement
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_restrict_bijective
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_restrict_bijective
import Theorems.Thm_GlobalTheory_CoverO_restrict_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (CoefMap.restrict (OAff s) hU.functor.op).pull1 := by
  first | exact @GlobalTheory.CoverO.restrict_bijective | exact GlobalTheory.CoverO.restrict_bijective | (intros; apply GlobalTheory.CoverO.restrict_bijective <;> assumption)
end _root_.GlobalTheory.T
