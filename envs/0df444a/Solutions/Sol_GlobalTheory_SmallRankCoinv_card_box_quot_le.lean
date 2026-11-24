-- Prove2me | solution 1 for GlobalTheory.SmallRankCoinv.card_box_quot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:51:35.45671+00:00
-- url     : https://prove2.me/submissions/48ac0949-a8d3-4ed3-8df8-9c78eda862b2

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
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
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
    (T R : Type) [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R] {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : kˣ) :
    Nat.card (box T R (ϖ⁻¹ * a) ⧸ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a))) ≤
      GlobalTheory.SplitWeil.resCard k ^ (Fintype.card T * Fintype.card R) := by
  have hb : 0 < valuation k ((ϖ⁻¹ * a : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have ha0 : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hint : ∀ (x : box T R (ϖ⁻¹ * a)) r q, x.1 r q / ((ϖ⁻¹ * a : kˣ) : k) ∈ 𝒪[k] := fun x r q => by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ hb]
    exact x.2 r q
  let φ : box T R (ϖ⁻¹ * a) →+ (T → R → 𝓀[k]) :=
    { toFun := fun x r q => IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩
      map_zero' := by
        funext r q
        rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (IsLocalRing.residue 𝒪[k])]
        congr 1
        exact Subtype.ext (by simp)
      map_add' := fun x y => by
        funext r q
        rw [Pi.add_apply, Pi.add_apply, ← map_add]
        congr 1
        exact Subtype.ext (by simp [add_div]) }
  have hker : φ.ker ≤ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a)) := by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf]
    intro r q
    have h1 : IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩ = 0 := congrFun (congrFun hx r) q
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at h1
    have h2 : valuation k (x.1 r q / ((ϖ⁻¹ * a : kˣ) : k)) ≤ valuation k (ϖ : k) := by
      rw [hϖ, le_uniformizer_iff]; exact h1
    rw [map_div₀, div_le_iff₀ hb, ← map_mul, ← Units.val_mul, mul_inv_cancel_left] at h2
    exact h2
  have h1 : Nat.card (box T R (ϖ⁻¹ * a) ⧸ φ.ker) ≤ Nat.card (T → R → 𝓀[k]) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective φ)
  haveI : Finite (box T R (ϖ⁻¹ * a) ⧸ φ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective φ)
  have h2 := Nat.le_of_dvd Nat.card_pos (AddSubgroup.index_dvd_of_le hker)
  refine h2.trans (h1.trans_eq ?_)
  simp only [Nat.card_fun, Nat.card_eq_fintype_card, GlobalTheory.SplitWeil.resCard, ← pow_mul, mul_comm]
end GlobalTheory.SmallRankCoinv
