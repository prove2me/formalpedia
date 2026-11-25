-- Prove2me | solution 1 for GlobalTheory.algTens_wtNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:37.747735+00:00
-- url     : https://prove2.me/submissions/3e06a597-eee6-484a-8891-a9f704c02a57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AlgTensWtNear
import Theorems.Thm_GlobalTheory_l1_shift_single_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  intro M _ _ n ε E N _ _ F io pr Λ t hT
  refine ⟨fun w hw s c => ?_, fun s y hy d => ?_⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0,
        l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩
      rw [← hT.pr_comm, ← map_smul]
      congr 1
      funext i
      simp only [dualTens, Pi.smul_apply]
      by_cases hi : i = c
      · subst hi
        by_cases ha : a = i
        · subst ha
          simp [hx a, add_smul, sub_eq_add_neg]
        · have : ¬ i = a := fun h => ha h.symm
          simp [hx a, ha, this]
      · by_cases ha : i = a
        · subst ha
          simp [hi]
        · simp [hi, ha]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0,
        l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩
      have h := congrFun (hT.io_comm s a a x) d
      rw [hx a, map_smul] at h
      simp only [dualTens, Pi.smul_apply] at h
      rw [eq_sub_iff_add_eq] at h
      rw [← h]
      by_cases ha : a = d
      · subst ha
        simp [add_smul]
      · have : ¬ d = a := fun h => ha h.symm
        simp [ha, this]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, Pi.smul_apply]; exact Submodule.smul_mem _ _ hx
end GlobalTheory
