-- Prove2me | solution 1 for MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9e583f49-0bcc-521c-859e-cabb4c4bd7b1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise ENNReal

namespace RS11C1

variable {G X ι : Type*} [Group G] [MulAction G X]

theorem subgroup_smul_set (Γ : Subgroup G) (γ : Γ) (s : Set X) : γ • s = (γ : G) • s := rfl

theorem smul_iUnion_inv_smul (Γ : Subgroup G) (R : ι → Γ) (g : G) (s : Set X) :
    g • (⋃ i, ((R i : G)⁻¹) • s) = ⋃ i, (g * (R i : G)⁻¹) • s := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i => ?_
  rw [smul_smul]

end RS11C1

theorem solution
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    IsFundamentalDomain Γ₂ (⋃ i, ((R i : G)⁻¹) • 𝓕) μ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    refine NullMeasurableSet.iUnion fun i => ?_
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [RS11C1.subgroup_smul_set, Subgroup.coe_inv] at h
  ·
    filter_upwards [h𝓕.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨i, hi, -⟩ := hR γ
    refine ⟨⟨(R i : G)⁻¹ * γ, hi⟩, ?_⟩
    rw [Subgroup.smul_def]
    show ((R i : G)⁻¹ * (γ : G)) • x ∈ ⋃ i, ((R i : G)⁻¹) • 𝓕
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [mul_smul]
    exact Set.smul_mem_smul_set (by rw [← Subgroup.smul_def]; exact hγ)
  ·
    intro γ γ' hne
    change AEDisjoint μ (γ • ⋃ i, ((R i : G)⁻¹) • 𝓕) (γ' • ⋃ i, ((R i : G)⁻¹) • 𝓕)
    rw [RS11C1.subgroup_smul_set, RS11C1.subgroup_smul_set, RS11C1.smul_iUnion_inv_smul Γ₁ R,
      RS11C1.smul_iUnion_inv_smul Γ₁ R, AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j

    have hγ₁ : ((γ : G) * (R i : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ.2) (inv_mem (R i).2)
    have hγ₁' : ((γ' : G) * (R j : G)⁻¹) ∈ Γ₁ := mul_mem (hle γ'.2) (inv_mem (R j).2)
    have hne' : (⟨(γ : G) * (R i : G)⁻¹, hγ₁⟩ : Γ₁) ≠ ⟨(γ' : G) * (R j : G)⁻¹, hγ₁'⟩ := by
      intro heq
      have heq' : (γ : G) * (R i : G)⁻¹ = (γ' : G) * (R j : G)⁻¹ := congrArg Subtype.val heq

      have hmem : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by
        have : ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * (γ : G) := by
          calc ((R j : G)⁻¹ * (R i : G)) = (γ' : G)⁻¹ * ((γ' : G) * (R j : G)⁻¹) * (R i : G) := by group
            _ = (γ' : G)⁻¹ * ((γ : G) * (R i : G)⁻¹) * (R i : G) := by rw [heq']
            _ = (γ' : G)⁻¹ * (γ : G) := by group
        rw [Subgroup.coe_inv, this]
        exact mul_mem (inv_mem γ'.2) γ.2
      have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
      obtain ⟨k, -, hk⟩ := hR (R i)
      have hij : i = j := (hk i hii).trans (hk j hmem).symm
      subst hij
      apply hne
      apply Subtype.ext
      exact mul_right_cancel heq'
    have h := h𝓕.aedisjoint hne'
    simpa only [Function.onFun, RS11C1.subgroup_smul_set] using h

end S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
end P2MW
export P2MW.S_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives (solution)
