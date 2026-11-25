-- Prove2me | solution 1 for GlobalTheory.MatchTerm.tx_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:03.933963+00:00
-- url     : https://prove2.me/submissions/5fe996d9-fc9d-4e9d-9de7-9d7a74f7194c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
import Theorems.Thm_GlobalTheory_T_degenerationSeriesTerms_nest
import Theorems.Thm_GlobalTheory_T_thetaConstantTerm_representative_dependence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
namespace GlobalTheory.MatchTerm
theorem _root_.solution {C : Type} [NormedField C] {N : NumD C} {M m : ℕ} (hM : Odd M) (hm : Odd m)
    (p : N.QT (m ^ 2)) (P : N.QT ((M * m) ^ 2)) (hp : p.1.1 = 1) (hP : P.1.1 = 1) (h : p.1.2 = P.1.2 ^ M)
    (s : Multiplicative N.X →* Cˣ) (hs : s ^ (M * m) ^ 2 = 1) :
    N.tx (M * m) (P * N.qTor s hs) = ∑' β, N.txT m p β * ((s ^ (M * m)) (Multiplicative.ofAdd β) : C) := by
  refine tsum_congr fun β => ?_
  rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (M * m) (hM.mul hm) P (P * N.qTor s hs) β).2 s (mul_one _) rfl,
    GlobalTheory.T.degenerationSeriesTerms_nest C N M m hM hm P p (by rw [hP, hp, one_pow]) h, hP, map_one, one_pow, one_mul, toAdd_one, zero_add,
    ofAdd_nsmul, map_pow, mul_comm]
  rfl
end GlobalTheory.MatchTerm
