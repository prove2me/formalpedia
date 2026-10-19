-- Prove2me | solution 2 for OAI.CriticalZ3.Box.separated_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:22:39.512246+00:00
-- url     : https://prove2.me/submissions/8d4f1625-9f4a-4913-a4a4-4d15a10279d3

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/BoxGeometry.lean:L196-L247
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Box.separated_subset. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

/-- The exact number of candidates excluded in one greedy selection. -/
theorem card_cube (c : Vertex) (m : ℕ) : (cube c m).vertices.card = (2*m+1)^3 := by
  rw [vertices,Pi.card_Icc]
  have he (i : Fin 3) : (Finset.Icc ((cube c m).lower i) ((cube c m).upper i)).card = 2*m+1 := by
    rw [Int.card_Icc]
    dsimp [cube]
    omega
  simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem separated_subset (s : Finset Vertex) (m K : ℕ)
    (hcard : K*(8*m+5)^3 ≤ s.card) :
    ∃ t ⊆ s, t.card = K ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
  induction K generalizing s with
  | zero => exact ⟨∅,Finset.empty_subset s,rfl,by simp⟩
  | succ K ih =>
    have hcpos : 0 < (8*m+5)^3 := by positivity
    have hspos : 0 < s.card := by nlinarith
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hspos
    let U := (cube a (4*m+2)).vertices
    have hU : U.card = (8*m+5)^3 := by
      rw [card_cube]
      congr 1
      omega
    have hc : (s ∩ U).card ≤ (8*m+5)^3 := by
      rw [←hU]
      exact Finset.card_le_card Finset.inter_subset_right
    have hdiff : K*(8*m+5)^3 ≤ (s \ U).card := by
      have he := Finset.card_sdiff_add_card_inter s U
      rw [Nat.succ_mul] at hcard
      omega
    obtain ⟨t,ht,htc,hts⟩ := ih (s \ U) hdiff
    have hat : a ∉ t := by
      intro hat
      have haa := (Finset.mem_sdiff.mp (ht hat)).2
      apply haa
      apply (mem_vertices _ _).mpr
      rw [contains_cube]
      intro i
      simp only [sub_self,abs_zero]
      positivity
    have has (b : Vertex) (hb : b ∈ t) : ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
      have hn := (Finset.mem_sdiff.mp (ht hb)).2
      have hn' : ¬ ∀ i, |b i-a i| ≤ (4*m+2 : ℤ) := by
        simpa [U,contains_cube] using hn
      push Not at hn'
      simpa only [abs_sub_comm] using hn'
    refine ⟨insert a t,?_,by simp [hat,htc],?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact (Finset.mem_sdiff.mp (ht hb)).1
    · intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact (hbc rfl).elim
        · exact has c hc
      · rcases Finset.mem_insert.mp hc with hca | hc
        · subst c
          simpa only [abs_sub_comm] using has b hb
        · exact hts b hb c hc hbc

end Box
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Box.separated_subset := @_root_.OAI.CriticalZ3.Box.separated_subset
