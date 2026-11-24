-- Prove2me | solution 1 for GlobalTheory.RealAlgebraCharacters.span_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:55:13.612371+00:00
-- url     : https://prove2.me/submissions/18ba67a4-fd15-412f-ac8b-3cad69349973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)
omit [AddCommGroup B]
namespace GlobalTheory.RealAlgebraCharacters
theorem _root_.solution (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    {f : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ)) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    exact ⟨1, fun x => (hn a x).le⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add u w _ _ hu hw =>
    obtain ⟨M1, h1⟩ := hu
    obtain ⟨M2, h2⟩ := hw
    refine ⟨M1 + M2, fun x => ?_⟩
    show ‖u x + w x‖ ≤ M1 + M2
    exact (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))
  | smul c u _ hu =>
    obtain ⟨M, h⟩ := hu
    refine ⟨‖c‖ * M, fun x => ?_⟩
    show ‖c • u x‖ ≤ ‖c‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)
end GlobalTheory.RealAlgebraCharacters
