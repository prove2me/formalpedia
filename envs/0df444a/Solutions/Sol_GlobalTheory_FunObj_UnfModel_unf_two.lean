-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.unf_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:12.014076+00:00
-- url     : https://prove2.me/submissions/67faa37c-a3ea-4601-994c-84d4715c72ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
import Theorems.Thm_GlobalTheory_FunObj_UnfModel_vacuum_term

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
theorem _root_.solution (hm : G.m = 2) (hψ : ∀ a ∈ 𝒪[k], ψ a = 1) (hν : IsUnitVol ν) (S : G.Args → ℂ)
    (h1 : ∀ z, (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 1)
    (h0 : ∀ z, ¬ (∀ b ∈ oppositePath G.m, ∀ i j, z b i j ∈ 𝒪[k]) → S z = 0) (J : G.Level) (keep : Bool) :
    ∃ (hfin : (unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S).Finite) (t : UnfTerm G),
      unf ψ ν keep _ S hfin = {t} ∧ t.coef = 1 ∧ t.datum 0 0 = 1 := by
  have : IsEmpty (Fin (G.m - 2)) := by rw [hm]; exact Fin.isEmpty'
  obtain ⟨a, b⟩ := vacuum_term hs ψ ν hψ hν S h1 h0 J keep
  have hS : unfSupport ψ ν keep (Reps.through hs J fun _ => 1) S = {fun _ => DoubleCoset.mk _ _ 1} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨b, fun β _ => funext fun i => isEmptyElim i⟩
  refine ⟨hS ▸ Set.finite_singleton _, _, ?_, ?_, a⟩
  · simp [unf, hS]
  · simp [unfTerm]
end GlobalTheory.FunObj.UnfModel
