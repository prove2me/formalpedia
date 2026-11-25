-- Prove2me | solution 1 for GlobalTheory.BasicFlow.basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:54.451855+00:00
-- url     : https://prove2.me/submissions/ce69fc22-79fe-4121-97c8-80f680b40023

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
import Theorems.Thm_GlobalTheory_BasicFlow_pivot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card ≤ Fintype.card κ := by
  induction' h : (s.filter fun i => x i ≠ 0).card using Nat.strong_induction_on
    with n ih generalizing x
  by_cases hc : (s.filter fun i => x i ≠ 0).card ≤ Fintype.card κ
  · exact ⟨x, hx, rfl, le_rfl, fun _ h => h, hc⟩
  · obtain ⟨y, h1, h2, h3, h4, h5⟩ := pivot s T φ hT x hx hs (not_le.1 hc)
    obtain ⟨z, g1, g2, g3, g4, g5⟩ :=
      ih _ (h ▸ h5) y h1 (fun i hi => h4 i (hs i hi)) rfl
    exact ⟨z, g1, g2.trans h2, h3.trans g3, fun i hi => g4 i (h4 i hi), g5⟩
end GlobalTheory.BasicFlow
