-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.vacuum_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:19.031844+00:00
-- url     : https://prove2.me/submissions/5164700d-1838-4028-91b1-6e8ef4664d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
import Theorems.Thm_GlobalTheory_FunObj_UnfModel_elt_one
import Theorems.Thm_GlobalTheory_FunObj_UnfModel_moved_one
import Theorems.Thm_GlobalTheory_FunObj_flatTensor_vacuum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
namespace GlobalTheory.FunObj.UnfModel
theorem _root_.solution (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1 ∧
    (fun _ => DoubleCoset.mk _ _ 1) ∈ unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S := by
  have h : (unfTerm ψ ν keep (Reps.through hs J fun _ => 1) S fun _ => DoubleCoset.mk _ _ 1).datum 0 0 = 1 := by
    simp only [unfTerm, elt_one, moved_one]
    exact (flatTensor_vacuum hs ψ ν hψ hν S h1 h0).2
  refine ⟨h, fun H => ?_⟩
  rw [H] at h
  exact zero_ne_one h
end GlobalTheory.FunObj.UnfModel
