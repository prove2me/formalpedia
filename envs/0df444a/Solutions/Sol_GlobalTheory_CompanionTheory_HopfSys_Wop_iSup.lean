-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.Wop_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:30.945039+00:00
-- url     : https://prove2.me/submissions/755f07db-785d-4995-b938-c63f240d2592

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
variable [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (a b : P) : ⨆ c, Wop A S a b c = Vop A S a b := by
  apply le_antisymm (iSup_le fun c ↦ inf_le_left)
  intro x hx
  have h1 : μ[A].left x ∈ ⨆ c, (S.u c).1 := by rw [S.cover]; trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hx, hc⟩
end GlobalTheory.CompanionTheory.HopfSys
