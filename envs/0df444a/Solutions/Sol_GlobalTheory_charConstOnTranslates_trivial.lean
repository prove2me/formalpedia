-- Prove2me | solution 1 for GlobalTheory.charConstOnTranslates_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:31.723358+00:00
-- url     : https://prove2.me/submissions/b6e6df97-c87e-4e9f-9a9b-f595a1325000

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
import Theorems.Thm_GlobalTheory_ArchChar_real_trivial
import Theorems.Thm_GlobalTheory_ArchChar_const_eq_one
import Theorems.Thm_GlobalTheory_ArchChar_exists_near
import Theorems.Thm_GlobalTheory_ArchChar_char_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (ψ : (ι → ℂˣ) →* ℂˣ) (θ : ι → ℂ) (T : Set (ι → ℝ)) (C : ℝ) (c : ℂˣ), Continuous ψ →
    (∀ i, (θ i).im ≠ 0) → (∀ y : ι → ℝ, ∃ a ∈ T, ‖a - y‖ ≤ C) →
    (∀ a ∈ T, ∀ z : ι → ℂˣ, (∀ i, (z i : ℂ) = a i + θ i) → ψ z = c) → ψ = 1 := by
  intro ι _ _ ψ θ T C c hψ hθ hT hc
  have hc' : ∀ a ∈ T, ψ (GlobalTheory.ArchChar.shift θ hθ a) = c :=
    fun a ha => hc a ha _ (fun i => rfl)
  have h1 := GlobalTheory.ArchChar.const_eq_one ψ hψ θ hθ T C c hT hc'
  subst h1
  have hcomp : ∀ i, ψ.comp (MonoidHom.mulSingle (fun _ : ι => ℂˣ) i) = 1 := by
    intro i
    refine GlobalTheory.ArchChar.char_trivial _ (by exact hψ.comp (continuous_mulSingle (A := fun _ : ι => ℂˣ) i)) (θ i) (hθ i) C ?_ ?_
    · intro ρ hρ
      have hr : ∀ j, 0 < Function.update (fun _ : ι => (1 : ℝ)) i ρ j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa using hρ
        · simp [Function.update_of_ne hj]
      have h := GlobalTheory.ArchChar.real_trivial ψ hψ θ hθ T C 1 hT hc' _ hr
      have hu : GlobalTheory.ArchChar.realUnits _ hr = Pi.mulSingle i (Units.mk0 _ (GlobalTheory.ArchChar.ofReal_ne hρ)) := by
        funext j
        by_cases hj : j = i
        · subst hj; ext; simp [GlobalTheory.ArchChar.realUnits]
        · ext; simp [GlobalTheory.ArchChar.realUnits, hj]
      rw [hu] at h
      simpa using h
    · intro R
      obtain ⟨t, ht, h⟩ := GlobalTheory.ArchChar.exists_near ψ hψ θ hθ T C hT hc' i R
      exact ⟨t, ht, by simpa using h⟩
  refine MonoidHom.ext fun z => ?_
  conv_lhs => rw [← Finset.univ_prod_mulSingle z]
  rw [map_prod, MonoidHom.one_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  have := DFunLike.congr_fun (hcomp i) (z i)
  simpa using this
end GlobalTheory
