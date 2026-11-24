-- Prove2me | solution 1 for GlobalTheory.existsUnique_realLinear_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:29.355427+00:00
-- url     : https://prove2.me/submissions/a84bb5fd-ce12-4116-af4f-c5e5c7ae1eda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_existsUnique_realLinear_lift_of_germ
import Theorems.Thm_GlobalTheory_exists_local_section_of_isDiscrete_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution [TopologicalSpace A] {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) (hopen : 𝓝 (0 : A) ≤ map ex' (𝓝 0))
    (hc : ContinuousAt ex 0) : ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by
  obtain ⟨s, -, hs, hs', -⟩ := exists_local_section_of_isDiscrete_ker hker hopen
  have ht : Tendsto ex (𝓝 0) (𝓝 0) := by simpa using hc.tendsto
  exact existsUnique_realLinear_lift_of_germ hker (g := s ∘ ex)
    (ContinuousAt.comp (by simpa using hs) hc) (ht.eventually hs')
end GlobalTheory
