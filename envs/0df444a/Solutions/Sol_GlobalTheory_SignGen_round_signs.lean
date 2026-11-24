-- Prove2me | solution 1 for GlobalTheory.SignGen.round_signs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:13.631231+00:00
-- url     : https://prove2.me/submissions/4462c8c9-cc40-46ca-832f-ad2107d1c827

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImaginaryGeneratorCmType
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.SignGen
namespace GlobalTheory.SignGen
theorem _root_.solution (I : Type) [Fintype I] (G : AddSubgroup (I → ℝ))
    (hG : Submodule.span ℝ (G : Set (I → ℝ)) = ⊤) (c : I → ℝ) :
    ∃ g ∈ G, ∀ i, |c i| ≤ c i * g i := by
  classical
  let s : I → ℝ := fun i => if 0 ≤ c i then 1 else -1
  have hs : ∀ i, c i * s i = |c i| := by
    intro i
    by_cases h : 0 ≤ c i
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (lt_of_not_ge h)]
  have hsmem : s ∈ Submodule.span ℝ (G : Set (I → ℝ)) := hG ▸ Submodule.mem_top
  obtain ⟨n, t, g, hsum⟩ := Submodule.mem_span_set'.1 hsmem
  let B : ℝ := ∑ k, ∑ i, |(g k : I → ℝ) i|
  let R : ℝ := B + 1
  let a : I → ℝ := ∑ k, (⌊R * t k⌋) • (g k : I → ℝ)
  have haG : a ∈ G := AddSubgroup.sum_mem _ (fun k _ => AddSubgroup.zsmul_mem _ (g k).2 _)
  refine ⟨a, haG, fun i => ?_⟩
  have hai : a i = ∑ k, (⌊R * t k⌋ : ℝ) * (g k : I → ℝ) i := by
    simp [a, Finset.sum_apply, zsmul_eq_mul]
  have hsi : s i = ∑ k, t k * (g k : I → ℝ) i := by
    rw [← hsum]; simp [Finset.sum_apply, smul_eq_mul]
  set e := a i - R * s i with he
  have he' : e = ∑ k, ((⌊R * t k⌋ : ℝ) - R * t k) * (g k : I → ℝ) i := by
    rw [he, hai, hsi, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have heB : |e| ≤ B := by
    rw [he']
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [abs_mul]
    have h1 : |(⌊R * t k⌋ : ℝ) - R * t k| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := Int.lt_floor_add_one (R * t k); linarith
      · have := Int.floor_le (R * t k); linarith
    have h2 : |(g k : I → ℝ) i| ≤ ∑ j, |(g k : I → ℝ) j| :=
      Finset.single_le_sum (f := fun j => |(g k : I → ℝ) j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    calc |(⌊R * t k⌋ : ℝ) - R * t k| * |(g k : I → ℝ) i| ≤ 1 * |(g k : I → ℝ) i| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ ∑ j, |(g k : I → ℝ) j| := by rw [one_mul]; exact h2
  have hai' : a i = R * s i + e := by rw [he]; ring
  have hce : -(|c i| * B) ≤ c i * e := by
    have h1 : |c i * e| ≤ |c i| * B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left heB (abs_nonneg _)
    have h2 := neg_abs_le (c i * e)
    linarith
  rw [hai']
  have : c i * (R * s i + e) = R * |c i| + c i * e := by rw [← hs i]; ring
  rw [this]
  have hR : R = B + 1 := rfl
  rw [hR]
  nlinarith [abs_nonneg (c i)]
end GlobalTheory.SignGen
