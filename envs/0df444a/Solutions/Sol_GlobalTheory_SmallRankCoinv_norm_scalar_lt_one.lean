-- Prove2me | solution 1 for GlobalTheory.SmallRankCoinv.norm_scalar_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:09.664503+00:00
-- url     : https://prove2.me/submissions/51886591-0447-4e33-828b-b2672e799dfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFullRankSubMem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_GLDoubling_nabs_unif
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e



set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.SmallRankCoinv
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel GlobalTheory.RankChart GlobalTheory.RankStrata
namespace GlobalTheory.SmallRankCoinv
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {z : ℂ} (hz : ‖z‖ = 1) {t r d c : ℕ} (ht : 0 < t) (hrd : 2 * r < d)
    (hc : c ≤ GlobalTheory.SplitWeil.resCard k ^ (t * r)) : ‖z ^ t * apow (ϖ ^ t) ((d : ℂ) / 2) * (c : ℂ)‖ < 1 := by
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])
  have hn : GlobalTheory.SplitWeil.nabs k (ϖ ^ t) = ((GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹) ^ t := by
    rw [← GlobalTheory.GLDoubling.nabs_unif hϖ]
    simp [GlobalTheory.SplitWeil.nabs]
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqd
  have hq0 : 0 < q := by linarith
  have e : ‖apow (ϖ ^ t) ((d : ℂ) / 2)‖ = q ^ (-((t : ℝ) * (d / 2))) := by
    rw [apow, Complex.norm_cpow_eq_rpow_re_of_pos (GlobalTheory.SplitWeil.Model.nabs_pos _), hn, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le]
    simp
  rw [norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, e, Complex.norm_natCast]
  have hc' : (c : ℝ) ≤ q ^ ((t : ℝ) * r) := by
    rw [← Nat.cast_mul, Real.rpow_natCast, hqd]; exact_mod_cast hc
  calc _ ≤ q ^ (-((t : ℝ) * (d / 2))) * q ^ ((t : ℝ) * r) := by gcongr
    _ = q ^ (-((t : ℝ) * (d / 2)) + t * r) := (Real.rpow_add hq0 _ _).symm
    _ < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg hq
      have h1 : (2 * r : ℝ) < d := by exact_mod_cast hrd
      have h2 : (0 : ℝ) < t := by exact_mod_cast ht
      nlinarith
end GlobalTheory.SmallRankCoinv
