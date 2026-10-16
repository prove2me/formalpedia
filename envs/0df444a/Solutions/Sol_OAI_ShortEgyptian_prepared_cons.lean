-- Prove2me | solution 1 for OAI.ShortEgyptian.prepared_cons
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:02:42.84658+00:00
-- url     : https://prove2.me/submissions/1918a05c-6af4-48e5-a259-78ee9ac72034

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/GreedyPreparation.lean:L69-L83
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prepared_cons. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_GreedyPreparation
import Theorems.Thm_OAI_ShortEgyptian_greedy_step

-- ---- from OAI.NumberTheory.ShortEgyptian.GreedyPreparation ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

lemma prepared_cons (A C : ℕ) (hA : 0<A) (hAC : A<C) (T : ℝ) (k : ℕ)
    (h : Prepared (residue C A (quotient C A)) (C*quotient C A) T k) :
    Prepared A C T (k+1) := by
  obtain ⟨xs,B,D,hxs,hlen,hB,hBD,heq,hstop⟩ := h
  have hs := greedy_step A C hA hAC
  dsimp at hs
  refine ⟨quotient C A :: xs,B,D,?_,by simpa only [List.length_cons] using Nat.succ_le_succ hlen,
    hB.trans hs.2.2.1.le,hBD,?_,hstop⟩
  · intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hs.1
    · exact hxs n hn
  · rw [unitSum_cons]
    rw [Nat.cast_mul] at heq
    linarith [hs.2.2.2.1]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prepared_cons := @_root_.OAI.ShortEgyptian.prepared_cons
