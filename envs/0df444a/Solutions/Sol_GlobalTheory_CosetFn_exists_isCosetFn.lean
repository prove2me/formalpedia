-- Prove2me | solution 1 for GlobalTheory.CosetFn.exists_isCosetFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:51.162521+00:00
-- url     : https://prove2.me/submissions/9e22a1ab-c9e1-4695-aa08-0f88ac11e127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsParabolicDoubleCosetFunctionEqOne
import Theorems.Thm_GlobalTheory_CosetFn_deltaR_mul
import Theorems.Thm_GlobalTheory_CosetFn_deltaR_one
import Theorems.Thm_GlobalTheory_CosetFn_mul_embX_mem_R
import Theorems.Thm_GlobalTheory_CosetFn_deltaR_eq
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.CosetFn
namespace GlobalTheory.CosetFn
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) : ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  classical
  let P : GL (n ⊕ Fin c) k → GL n k → Prop := fun x g =>
    ∃ u ∈ N k n c 1, ∃ j ∈ J, x = u * embX c g * h * j
  let f : GL (n ⊕ Fin c) k → ℂ := fun x =>
    if hx : ∃ g, P x g then (deltaR c hx.choose : ℂ) else 0
  have fpos : ∀ x g, P x g → f x = (deltaR c g : ℂ) := by
    intro x g hg
    have hx : ∃ g, P x g := ⟨g, hg⟩
    obtain ⟨u, hu, j, hj, e⟩ := hx.choose_spec
    obtain ⟨u', hu', j', hj', e'⟩ := hg
    simp only [f, dif_pos hx]
    rw [deltaR_eq H hu hu' hj hj' (e.symm.trans e')]
  have fneg : ∀ x, (¬ ∃ g, P x g) → f x = 0 := fun x hx => by simp only [f, dif_neg hx]
  have left : ∀ u ∈ N k n c 1, ∀ (g g' : GL n k) x, P x g' → P (u * embX c g * x) (g * g') := by
    rintro u hu g g' x ⟨u', hu', j, hj, rfl⟩
    refine ⟨u * (embX c g * u' * (embX c g)⁻¹), mul_mem hu (Radical.conj_mem _ hu'), j, hj, ?_⟩
    simp only [map_mul]; group
  have right : ∀ j ∈ J, ∀ g x, P x g → P (x * j) g := by
    rintro j hj g x ⟨u', hu', j', hj', rfl⟩
    exact ⟨u', hu', j' * j, mul_mem hj' hj, by group⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu g x
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (left u hu g g' x hg'), fpos _ _ hg', deltaR_mul]
      push_cast; rfl
    · rw [fneg x hx, mul_zero]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := left _ (Radical.conj_mem g⁻¹ (inv_mem hu)) g⁻¹ g' _ hg'
      have e : embX c g⁻¹ * u⁻¹ * (embX c g⁻¹)⁻¹ * embX c g⁻¹ * (u * embX c g * x) = x := by
        simp only [map_inv]; group
      rw [e] at this
      exact ⟨_, this⟩
  · intro x j hj
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (right j hj g' x hg'), fpos _ _ hg']
    · rw [fneg x hx]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := right _ (inv_mem hj) g' _ hg'
      rw [mul_inv_cancel_right] at this
      exact ⟨_, this⟩
  · intro x hx
    apply fneg
    rintro ⟨g, u, hu, j, hj, e⟩
    apply hx
    symm
    rw [DoubleCoset.eq]
    exact ⟨_, mul_embX_mem_R hu g, j, hj, e⟩
  · rw [fpos h 1 ⟨1, one_mem _, 1, one_mem _, by simp⟩, deltaR_one]
    simp
end GlobalTheory.CosetFn
