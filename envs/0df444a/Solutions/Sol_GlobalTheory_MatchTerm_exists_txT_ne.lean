-- Prove2me | solution 1 for GlobalTheory.MatchTerm.exists_txT_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:36.025025+00:00
-- url     : https://prove2.me/submissions/4ba57b98-92bb-4c58-9f79-fded23929ef7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_tor
import Theorems.Thm_GlobalTheory_MatchTerm_exists_char_pow
import Theorems.Thm_GlobalTheory_T_degenerationData_torsion_structure_algClosed
import Theorems.Thm_GlobalTheory_T_norm_rep_generators_and_thetaSeriesTerm


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
theorem _root_.solution {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by
  obtain ⟨t, ht, hx⟩ := hT.good (N.c x)
  obtain ⟨b, rfl⟩ := hT.div t
  obtain ⟨γ, rfl⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT 0).1 b
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ ^ (n ^ 1) ^ 2)).2 (by rw [NumD.Gt.pow_b, pow_one, sq, pow_mul, ht])
  obtain ⟨s, rfl⟩ := exists_char_pow (k := (n ^ 1) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')) s
  refine ⟨⟨(1, γ * (N.tor s)⁻¹), ?_⟩, rfl, ?_⟩
  · rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
    exact N.io_zero.symm
  · rw [← norm_ne_zero_iff, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 _ hn.pow]
    refine mul_ne_zero (Real.exp_pos _).ne' ?_
    simp [hx]
end GlobalTheory.MatchTerm
