-- Prove2me | solution 1 for GlobalTheory.StableLatCount.exists_smul_mem_finset_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:10:34.655187+00:00
-- url     : https://prove2.me/submissions/59cb1be0-d81a-4edc-a11e-8a9b6efe6178

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTop
import Theorems.Thm_GlobalTheory_StableLatCount_exists_smul_mem_of_span_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.StableLatCount
namespace GlobalTheory.StableLatCount
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E]
    [Algebra O E] [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A]
    [IsScalarTower O E A] (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (t : Finset A) :
    ∃ d ∈ nonZeroDivisors O, ∀ a ∈ t, d • a ∈ M := by
  classical
  refine Finset.induction_on t ⟨1, one_mem _, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨d₁, hd₁, h₁⟩ := ih
  obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_span_eq_top O E M hM a
  refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mul_smul]; exact M.smul_mem _ h₂
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ (h₁ b hb)
end GlobalTheory.StableLatCount
