-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums.le_lamMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:25.594137+00:00
-- url     : https://prove2.me/submissions/feeba8cc-2d03-4d99-b271-8d2a2a02485a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_InfinitePlaceDepthSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
theorem _root_.solution (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) (c : ℝ)
    (h : ∀ p, Df.Qp Bs.μ0 p ≠ ⊥ → c ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) : c ≤ lamMin hW S v := by
  classical
  refine Finset.le_inf' _ _ fun p hp => h p ?_
  simpa [occurring] using hp
end GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
