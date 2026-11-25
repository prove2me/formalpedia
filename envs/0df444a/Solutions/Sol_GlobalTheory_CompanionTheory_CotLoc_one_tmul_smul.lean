-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.one_tmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:56.739681+00:00
-- url     : https://prove2.me/submissions/0802b252-aea0-4632-b7a7-c36fc7778930

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {R' A P : Type} [CommRing R'] [CommRing A] [Algebra A R'] [AddCommGroup P]
    [Module A P] (a : A) (x : P) :
    (1 : R') ⊗ₜ[A] (a • x) = algebraMap A R' a • ((1 : R') ⊗ₜ[A] x) := by
  rw [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
end GlobalTheory.CompanionTheory.CotLoc
