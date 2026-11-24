-- Prove2me | solution 1 for GlobalTheory.Ex.ArcForm.hasSum_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:44:40.423404+00:00
-- url     : https://prove2.me/submissions/8345bfbe-d41e-44b9-9291-932b9aad0e46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.ArcForm
namespace GlobalTheory.Ex.ArcForm
theorem _root_.solution {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by
  have h1 := h.tsum_fiberwise fun χ => (e χ).toNat
  refine h1.congr_fun fun n => ?_
  have hs : (fun χ => (e χ).toNat) ⁻¹' {n} = ((hf n).toFinset : Set X) := by
    ext χ
    have := h0 χ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    omega
  rw [hs, Finset.tsum_subtype' (hf n).toFinset fun χ => u ^ e χ * a χ]
  have h2 : (∑ᶠ (χ : X) (_ : e χ = n), a χ) = ∑ χ ∈ (hf n).toFinset, a χ :=
    finsum_mem_eq_finite_toFinset_sum a (hf n)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : e χ = n := by simpa using hχ
  rw [this, zpow_natCast, mul_comm]
end GlobalTheory.Ex.ArcForm
