-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.concaveOn_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:28:12.147039+00:00
-- url     : https://prove2.me/submissions/530246be-8b47-49dd-a1e4-b2caf33a4567

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropyScalars.lean:L95-L107
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.concaveOn_entropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem concaveOn_entropy : ConcaveOn ℝ (Icc (-1) 1) entropy := by
  refine ⟨convex_Icc (-1) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 + y) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [entropy_eq_binEntropy, entropy_eq_binEntropy, entropy_eq_binEntropy]
  convert h using 1
  congr 1
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_entropy := @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_entropy
