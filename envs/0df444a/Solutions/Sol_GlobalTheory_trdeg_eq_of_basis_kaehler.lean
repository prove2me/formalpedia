-- Prove2me | solution 1 for GlobalTheory.trdeg_eq_of_basis_kaehler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:19.298712+00:00
-- url     : https://prove2.me/submissions/bcefce61-07fd-450b-bcc0-2f0cb1fac8f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_rank_kaehler_eq_trdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]
omit [IsDomain V] [IsDiscreteValuationRing V] [Algebra.FormallySmooth K V]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (b : Basis (Fin n) V Ω[V⁄K]) :
    Algebra.trdeg K F = n := by
  have : Algebra.EssFiniteType V F := .of_isLocalization F V⁰
  have : Algebra.EssFiniteType K F := .comp K V F
  rw [← rank_kaehler_eq_trdeg, rank_eq_card_basis (fracKaehlerBasis F b), Fintype.card_fin]
end GlobalTheory
