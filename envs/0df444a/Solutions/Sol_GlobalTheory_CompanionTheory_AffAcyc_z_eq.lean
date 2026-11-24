-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.z_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:05.157461+00:00
-- url     : https://prove2.me/submissions/a8cdba50-07d0-47b3-9153-0727716b1278

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_chain_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (z : Cn F 0) (c : Fin 1 ⥤ Pᵒᵖ) :
    z c = z ((Functor.const (Fin 1)).obj (c.obj 0)) :=
  eq_of_heq (congr_arg_heq z (chain_eq c))
end GlobalTheory.CompanionTheory.AffAcyc
