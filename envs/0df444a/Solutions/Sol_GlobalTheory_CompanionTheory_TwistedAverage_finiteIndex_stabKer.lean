-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.finiteIndex_stabKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:55.887915+00:00
-- url     : https://prove2.me/submissions/5a990c3f-5b4f-4763-9487-acdca3552349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_isOpen_stabKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (x : V) :
    (stabKer ρ L θ x).FiniteIndex := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ stabKer ρ L θ x) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_stabKer hρ L θ hθ x)
  exact Subgroup.finiteIndex_of_finite_quotient
end GlobalTheory.CompanionTheory.TwistedAverage
