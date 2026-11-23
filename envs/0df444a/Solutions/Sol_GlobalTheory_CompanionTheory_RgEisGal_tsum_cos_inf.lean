-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.tsum_cos_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:16.0272+00:00
-- url     : https://prove2.me/submissions/a258e6f4-278f-4bde-9b12-c50e63ba9a15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {X : Type} [AddCommMonoid X] [TopologicalSpace X] (Γ S : Subgroup G)
    (f : G → X) : ∑' r : Cos (Γ ⊓ S) Γ, f (rep r) = ∑' q : Cos S Γ, f (rep q) := by
  have e : (Γ ⊓ S).subgroupOf Γ = S.subgroupOf Γ := Subgroup.inf_subgroupOf_left S Γ
  have key : ∀ U V : Subgroup Γ, U = V →
      ∑' r : Quotient (QuotientGroup.rightRel U), f (Quotient.out r).1 =
        ∑' q : Quotient (QuotientGroup.rightRel V), f (Quotient.out q).1 := by
    rintro U _ rfl
    rfl
  exact key _ _ e
end GlobalTheory.CompanionTheory.RgEisGal
