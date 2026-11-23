-- Prove2me | solution 1 for GlobalTheory.SplitWeil.nabs_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:28.182805+00:00
-- url     : https://prove2.me/submissions/a171ccce-2cb1-47b1-8dfa-680fb7fca6e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_isUnitVol
import Theorems.Thm_GlobalTheory_SplitWeil_measure_cball
import Theorems.Thm_GlobalTheory_SplitWeil_mem_cball_uniformiser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.SplitWeil
theorem _root_.solution {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {x : kˣ} (hx : (x : k) = ϖ) :
    nabs k x = (resCard k : ℝ)⁻¹ := by
  borelize k
  obtain ⟨ν, hν, h1⟩ := exists_isUnitVol k
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let S : 𝓀[k] → Set k := fun r => (fun z => -(l r : k) + z) ⁻¹' cball x
  have hS : ∀ (r : 𝓀[k]) (y : 𝒪[k]), (y : k) ∈ S r ↔ IsLocalRing.residue _ y = r := by
    intro r y
    have := mem_cball_uniformiser hϖ hx (-(l r) + y)
    rw [← IsLocalRing.residue_eq_zero_iff, map_add, map_neg, hl, neg_add_eq_zero, eq_comm] at this
    simpa [S] using this
  have hsub : ∀ r, S r ⊆ (𝒪[k] : Set k) := by
    intro r z hz
    have h2 : -(l r : k) + z ∈ 𝒪[k] := by
      have : valuation k (-(l r : k) + z) ≤ valuation k (x : k) := hz
      rw [hx] at this
      exact this.trans ((Valuation.mem_integer_iff _ _).mp ϖ.2)
    simpa using add_mem (l r).2 h2
  have hU : (𝒪[k] : Set k) = ⋃ r, S r := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion_subset hsub)
    exact Set.mem_iUnion.mpr ⟨_, (hS _ ⟨z, hz⟩).mpr rfl⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro r r' hr
    refine Set.disjoint_left.mpr fun z hz hz' => hr ?_
    exact ((hS r ⟨z, hsub r hz⟩).mp hz).symm.trans ((hS r' ⟨z, hsub r hz⟩).mp hz')
  have hm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_cball x).preimage (by fun_prop)).measurableSet
  have h2 : ν (𝒪[k] : Set k) = ∑' r, ν (S r) := by rw [hU, measure_iUnion hd hm]
  have h3 : ∀ r, ν (S r) = distribHaarChar k x := by
    intro r
    simp only [S]
    rw [measure_preimage_add, measure_cball, h1, mul_one]
  haveI := Fintype.ofFinite 𝓀[k]
  simp only [h3, h1, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h4 := congrArg ENNReal.toReal h2
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] at h4
  rw [resCard, Nat.card_eq_fintype_card, nabs]
  exact eq_inv_of_mul_eq_one_right h4.symm
end GlobalTheory.SplitWeil
