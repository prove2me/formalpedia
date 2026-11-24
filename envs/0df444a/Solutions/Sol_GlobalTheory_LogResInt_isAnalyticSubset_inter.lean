-- Prove2me | solution 1 for GlobalTheory.LogResInt.isAnalyticSubset_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:52:00.658374+00:00
-- url     : https://prove2.me/submissions/2dbc142c-d60b-487e-a41d-5e2054dc4c8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Theorems.Thm_GlobalTheory_LogResInt_HasHoloImm_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.LogResInt
theorem _root_.solution {A : FinHolAtlas d X} {S T : Set X} (hS : A.IsAnalyticSubset S)
    (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∩ T) := by
  intro x
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hxW', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW'⟩, r + r', Fin.append f f', fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact fun j => (hf i j).mono fun z hz => ⟨hz.1, hz.2.1⟩
    | right i =>
      simp only [Fin.append_right]
      exact fun j => (hf' i j).mono fun z hz => ⟨hz.1, hz.2.2⟩
  · ext y
    constructor
    · rintro ⟨⟨hyS, hyT⟩, hyW, hyW'⟩
      refine ⟨⟨hyW, hyW'⟩, fun i => ?_⟩
      induction i using Fin.addCases with
      | left i => simpa using (hSW.le ⟨hyS, hyW⟩).2 i
      | right i => simpa using (hTW.le ⟨hyT, hyW'⟩).2 i
    · rintro ⟨⟨hyW, hyW'⟩, h⟩
      exact ⟨⟨(hSW.ge ⟨hyW, fun i => by simpa using h (Fin.castAdd r' i)⟩).1,
        (hTW.ge ⟨hyW', fun i => by simpa using h (Fin.natAdd r i)⟩).1⟩, hyW, hyW'⟩
end GlobalTheory.LogResInt
