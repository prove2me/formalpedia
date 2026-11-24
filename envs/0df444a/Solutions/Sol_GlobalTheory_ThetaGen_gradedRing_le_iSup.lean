-- Prove2me | solution 1 for GlobalTheory.ThetaGen.gradedRing_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:05.415874+00:00
-- url     : https://prove2.me/submissions/a62ab522-4925-4265-bd83-67c51f3adef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow
import Theorems.Thm_GlobalTheory_ThetaGen_homog_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {X : Type}
variable (R : ℕ → Submodule ℂ (X → ℂ))
namespace GlobalTheory.ThetaGen
theorem _root_.solution (h1 : (1 : X → ℂ) ∈ R 0)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) {F : ℂ × X → ℂ} (hF : F ∈ gradedRing R) :
    F ∈ Submodule.span ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f} := by
  have : Subalgebra.toSubmodule (gradedRing R) =
      Submodule.span ℂ {F | ∃ d, ∃ f ∈ R d, F = homog d f} := by
    unfold gradedRing
    rw [Algebra.adjoin_eq_span]
    apply le_antisymm
    · apply Submodule.span_mono
      intro G hG
      induction hG using Submonoid.closure_induction with
      | mem x hx => exact hx
      | one => exact ⟨0, 1, h1, by funext p; simp [homog]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, f, hf, rfl⟩ := hx
        obtain ⟨b, h, hh, rfl⟩ := hy
        exact ⟨a + b, f * h, hmul a b (Submodule.mul_mem_mul hf hh), homog_mul _ _ _ _⟩
    · exact Submodule.span_mono Submonoid.subset_closure
  rw [← this]; exact hF
end GlobalTheory.ThetaGen
