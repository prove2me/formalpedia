-- Prove2me | solution 1 for OAI.ShortEgyptian.residue_double_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:44:16.737045+00:00
-- url     : https://prove2.me/submissions/a3b12751-6ab8-4169-a0fa-4bc177cc62a6

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DoubleCount.lean:L14-L80
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.residue_double_count. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

theorem predecessor_dvd {v u z h : ℕ} (heq : v + h = u * z) : u ∣ v + h := by
  rw [heq]
  exact Nat.dvd_mul_right _ _

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DoubleCount ----
namespace OAI

universe uI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma residue_double_count {I : Type uI} [Fintype I] [Nonempty I]
    (H K B : Finset ℕ) (N : I → ℕ) (hN : ∀ i, 0 < N i) (X Y ρ : ℝ) (hρ : 0 < ρ)
    (hH : ∀ u ∈ H, 0 < u ∧ (u:ℝ) ≤ X)
    (hsmall : ∀ u ∈ H, (u:ℝ) ≤ Y → u ∈ K)
    (hlift : ∀ u ∈ H, ∀ i, (residue (N i) u (quotient (N i) u):ℝ) ≤ Y →
      residue (N i) u (quotient (N i) u) ∈ K)
    (hgood : ∀ u ∈ H, u ∉ B → Y < (u:ℝ) →
      ρ*(Fintype.card I:ℝ)/2 ≤ ((univ.filter fun i =>
        (residue (N i) u (quotient (N i) u):ℝ) ≤ Y).card:ℝ)) :
    (H.card:ℝ) ≤ B.card+K.card+2/(ρ*Fintype.card I)*
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
  let W := H.filter (fun u => u ∉ B ∧ Y < (u:ℝ))
  have hsub : H ⊆ B ∪ K ∪ W := by
    intro u hu
    by_cases hb : u ∈ B
    · exact mem_union_left _ (mem_union_left _ hb)
    by_cases hy : (u:ℝ) ≤ Y
    · exact mem_union_left _ (mem_union_right _ (hsmall u hu hy))
    · exact mem_union_right _ (mem_filter.mpr ⟨hu,hb,lt_of_not_ge hy⟩)
  have hc : H.card ≤ B.card+K.card+W.card := (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  let rem (i : I) (u : ℕ) := residue (N i) u (quotient (N i) u)
  have hswap : ∑ u ∈ W, (univ.filter fun i => rem i u ∈ K).card =
      ∑ i, (W.filter fun u => rem i u ∈ K).card := by
    simp only [card_eq_sum_ones,sum_filter]
    exact sum_comm
  have hfiber (i : I) : (W.filter fun u => rem i u ∈ K).card ≤
      ∑ v ∈ K, truncatedDivisorCount X (N i+v) := by
    rw [←sum_card_fiberwise_eq_card_filter W K (rem i)]
    apply sum_le_sum
    intro v _hv
    apply card_le_card
    intro u hu
    obtain ⟨hu,hrem⟩ := mem_filter.mp hu
    have huu := (mem_filter.mp hu).1
    have hupos := (hH u huu).1
    have heq := (residue_spec (hN i) hupos).2
    change N i+rem i u=u*quotient (N i) u at heq
    rw [hrem] at heq
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨predecessor_dvd heq,by have hh := hN i; omega⟩,(hH u huu).2⟩
  have hcount : ∑ u ∈ W, (univ.filter fun i => rem i u ∈ K).card ≤
      ∑ i, ∑ v ∈ K, truncatedDivisorCount X (N i+v) := by
    rw [hswap]
    exact sum_le_sum (fun i _ => hfiber i)
  have hlow (u : ℕ) (hu : u ∈ W) : ρ*(Fintype.card I:ℝ)/2 ≤
      ((univ.filter fun i => rem i u ∈ K).card:ℝ) := by
    obtain ⟨hu,hb,hy⟩ := mem_filter.mp hu
    apply (hgood u hu hb hy).trans
    apply Nat.cast_le.mpr
    apply card_le_card
    intro i hi
    exact mem_filter.mpr ⟨mem_univ i,hlift u hu i (mem_filter.mp hi).2⟩
  have hlo : (W.card:ℝ)*(ρ*Fintype.card I/2) ≤
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
    calc
      _ = ∑ u ∈ W, ρ*(Fintype.card I:ℝ)/2 := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ ∑ u ∈ W, ((univ.filter fun i => rem i u ∈ K).card:ℝ) := sum_le_sum hlow
      _ ≤ _ := by exact_mod_cast hcount
  have hI : 0 < (Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  have hW : (W.card:ℝ) ≤ 2/(ρ*Fintype.card I)*
      ∑ i, ∑ v ∈ K, (truncatedDivisorCount X (N i+v):ℝ) := by
    have hd := (le_div_iff₀ (div_pos (mul_pos hρ hI) (by norm_num : (0:ℝ)<2))).mpr hlo
    apply hd.trans_eq
    simp only [div_div_eq_mul_div]
    ring
  have hcR : (H.card:ℝ) ≤ B.card+K.card+W.card := by exact_mod_cast hc
  linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution.{uI} : type_of% @_root_.OAI.ShortEgyptian.residue_double_count.{uI} := @_root_.OAI.ShortEgyptian.residue_double_count.{uI}
