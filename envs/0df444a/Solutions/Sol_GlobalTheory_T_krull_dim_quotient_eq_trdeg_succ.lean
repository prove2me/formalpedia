-- Prove2me | solution 1 for GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:11.525316+00:00
-- url     : https://prove2.me/submissions/32ec2fc6-3aba-4e43-b605-c3cb2322be3b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSuccStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_DimChart_ringKrullDim_quotient_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B), CharZero (Y.residueField (j q)) → ringKrullDim (B ⧸ q.asIdeal) = (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | exact GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq | (intros; apply GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq <;> assumption)
end _root_.GlobalTheory.T
