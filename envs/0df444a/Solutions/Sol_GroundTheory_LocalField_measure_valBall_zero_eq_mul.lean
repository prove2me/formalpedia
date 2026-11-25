-- Prove2me | solution 1 for GroundTheory.LocalField.measure_valBall_zero_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:26:00.556799+00:00
-- url     : https://prove2.me/submissions/906ce356-22f3-4203-bd1c-5deb264f05d3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_residue_eq_residue_iff
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (μ : Measure K) [μ.IsAddLeftInvariant] :
    μ (valBall K 0) = residueCard K * μ (valBall K 1) := by
  classical
  have : Fintype 𝓀[K] := Fintype.ofFinite _
  choose s hs using
    (IsLocalRing.residue_surjective : Function.Surjective (IsLocalRing.residue 𝒪[K]))
  let T : 𝓀[K] → Set K := fun r => (fun x => -((s r : 𝒪[K]) : K) + x) ⁻¹' (valBall K 1 : Set K)
  have hmem : ∀ r x, x ∈ T r ↔ ∃ h : x ∈ 𝒪[K], IsLocalRing.residue 𝒪[K] ⟨x, h⟩ = r := by
    intro r x
    constructor
    · intro hx
      have hx' : x - (s r : K) ∈ valBall K 1 := by
        have : -((s r : 𝒪[K]) : K) + x ∈ valBall K 1 := hx
        rwa [neg_add_eq_sub] at this
      have h1 := add_mem (valBall_antitone (show (0 : ℤ) ≤ 1 by norm_num) hx')
        (mem_valBall_zero_iff.mpr (s r).2)
      rw [sub_add_cancel] at h1
      refine ⟨mem_valBall_zero_iff.mp h1, ?_⟩
      rw [← hs r, residue_eq_residue_iff]
      exact hx'
    · rintro ⟨h, hr⟩
      rw [← hs r, residue_eq_residue_iff] at hr
      show -((s r : 𝒪[K]) : K) + x ∈ valBall K 1
      rw [neg_add_eq_sub]
      exact hr
  have hunion : (valBall K 0 : Set K) = ⋃ r, T r := by
    ext x
    simp only [Set.mem_iUnion, hmem, SetLike.mem_coe, mem_valBall_zero_iff]
    constructor
    · intro hx
      exact ⟨_, hx, rfl⟩
    · rintro ⟨r, h, -⟩
      exact h
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro r r' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    obtain ⟨h, rfl⟩ := (hmem r x).mp hx
    obtain ⟨h', rfl⟩ := (hmem r' x).mp hx'
    rfl
  have hmeas : ∀ r, MeasurableSet (T r) := fun r =>
    (measurableSet_valBall 1).preimage (measurable_const_add _)
  have hμ : ∀ r, μ (T r) = μ (valBall K 1) := fun r => measure_preimage_add μ _ _
  rw [hunion, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, residueCard,
    Nat.card_eq_fintype_card]
end GroundTheory.LocalField
