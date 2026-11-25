-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.Wop_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:13.060234+00:00
-- url     : https://prove2.me/submissions/53547227-177b-4177-95d8-ffc2d874ce7b

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
theorem _root_.solution (a b c c' : P) : Wop A S a b (c ⊓ c') = Wop A S a b c ⊓ Wop A S a b c' := by
  apply le_antisymm
  · exact le_inf (Wop_mono A S le_rfl le_rfl inf_le_left) (Wop_mono A S le_rfl le_rfl inf_le_right)
  · intro x hx
    refine ⟨hx.1.1, ?_⟩
    change μ[A].left x ∈ (S.u (c ⊓ c')).1
    rw [S.map_inf]
    exact ⟨hx.1.2, hx.2.2⟩
end GlobalTheory.CompanionTheory.HopfSys
