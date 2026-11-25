-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.wedgeT_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:34.031502+00:00
-- url     : https://prove2.me/submissions/f3aac668-2ce4-4b09-9128-ac150f2d5f73

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCrossStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BijectiveOfSurjectiveSameRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeTSurjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] :
    Function.Surjective (wedgeT (R := R) V) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span (R := R) (n := 2) (M := V),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ v 1, ?_⟩
  rw [wedgeT_tmul]
  congr 1
  funext i; fin_cases i <;> rfl
end GlobalTheory.CompanionTheory.WedgeOf
