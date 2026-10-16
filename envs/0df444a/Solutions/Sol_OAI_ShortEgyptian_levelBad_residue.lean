-- Prove2me | solution 1 for OAI.ShortEgyptian.levelBad_residue
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:47:45.572753+00:00
-- url     : https://prove2.me/submissions/0034ed9f-4478-428c-819a-dcdf7c88fcc8

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DescentSets.lean:L104-L120
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.levelBad_residue. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Theorems.Thm_OAI_ShortEgyptian_residue_lift

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma level_pos (S : ℝ) (j : ℕ) : 0 < level S j := Real.exp_pos _
lemma scaleRho_le_one (S : ℝ) : scaleRho S ≤ 1 :=
  Real.exp_le_one_iff.mpr (by have hh : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _; nlinarith)

lemma level_succ (S : ℝ) (j : ℕ) : level S (j+1) = level S j*scaleRho S := by
  unfold level scaleRho
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring

lemma level_antitone (S : ℝ) : Antitone (level S) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [level_succ]
  exact mul_le_of_le_one_right (level_pos S j).le (scaleRho_le_one S)

lemma levelMultiplier_pos (S : ℝ) (C j : ℕ) (hC : 0 < C) : 0 < levelMultiplier S C j := by
  unfold levelMultiplier
  split <;> omega

lemma levelMultiplier_dvd (S : ℝ) (C j : ℕ) :
    levelMultiplier S C (j+1) ∣ levelMultiplier S C j := by
  unfold levelMultiplier
  split_ifs with h₁ h₂ h₂
  · exact dvd_refl _
  · exact False.elim (h₂ (h₁.trans_le (level_antitone S (by omega))))
  · exact one_dvd _
  · exact dvd_refl _

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DescentSets ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma HasUnitSum.mono {M Q u k l : ℕ} (h : HasUnitSum M Q u k) (hkl : k ≤ l) : HasUnitSum M Q u l := by
  obtain ⟨ns,hs,hl⟩ := h
  exact ⟨ns,hs,hl.trans hkl⟩

lemma hasUnitSum_zero (M Q k : ℕ) : HasUnitSum M Q 0 k := by
  exact ⟨[],⟨by simp,by simp⟩,by simp⟩

lemma mem_levelBad (S : ℝ) (M C K j u : ℕ) :
    u ∈ levelBad S M C K j ↔ 0 < u ∧ (u:ℝ) ≤ level S j ∧
      ¬HasUnitSum M (levelMultiplier S C j) u (K+(depth S-j)) := by
  constructor
  · intro hu
    obtain ⟨hu,hn⟩ := mem_filter.mp hu
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
    exact ⟨by omega,(Nat.cast_le.mpr hhi).trans (Nat.floor_le (level_pos S j).le),hn⟩
  · rintro ⟨hu0,hu,hn⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hu0,Nat.le_floor hu⟩,hn⟩

lemma levelBad_residue (S : ℝ) (C M K j u t : ℕ) (hM : 0 < M) (hC : 0 < C)
    (hj : j < depth S) (huM : u < M*levelMultiplier S C j)
    (hu : u ∈ levelBad S M C K j) (ht : 0 < t) (htM : t ∣ M)
    (hy : (residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u):ℝ) ≤ level S (j+1)) :
    residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u) ∈ levelBad S M C K (j+1) := by
  let v := residue (levelMultiplier S C j*t) u (quotient (levelMultiplier S C j*t) u)
  obtain ⟨hu0,_,hn⟩ := (mem_levelBad S M C K j u).mp hu
  have hlift (hv : HasUnitSum M (levelMultiplier S C (j+1)) v (K+(depth S-(j+1)))) : False := by
    have hh := residue_lift hM (levelMultiplier_pos S C j hC) (levelMultiplier_pos S C (j+1) hC)
      (levelMultiplier_dvd S C j) hu0 huM ht htM hv
    apply hn
    exact HasUnitSum.mono hh (by omega)
  apply (mem_levelBad S M C K (j+1) v).mpr
  refine ⟨?_,hy,hlift⟩
  by_contra hv
  have hv0 : v = 0 := by omega
  exact hlift (hv0 ▸ hasUnitSum_zero M (levelMultiplier S C (j+1)) _)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.levelBad_residue := @_root_.OAI.ShortEgyptian.levelBad_residue
