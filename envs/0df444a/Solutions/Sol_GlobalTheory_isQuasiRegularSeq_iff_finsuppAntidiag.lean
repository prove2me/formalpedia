-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_iff_finsuppAntidiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:44.582652+00:00
-- url     : https://prove2.me/submissions/ca0632e1-ddf4-47a9-9d75-d0d194d64bbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_MonoDeg_sum_eq_sum_finsuppAntidiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (a : ℕ) (c : (ι →₀ ℕ) → M),
      ∑ α ∈ Finset.finsuppAntidiag Finset.univ a, monoVal f α • c α ∈
        (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
      ∀ α, α.degree = a → c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by
  constructor
  · intro h a c hc α hα
    rw [← MonoDeg.sum_eq_sum_finsuppAntidiag a fun α => monoVal f α • c α] at hc
    exact h a (fun α => c α.1) hc ⟨α, hα⟩
  · intro h a c hc α
    have := h a (fun β => if hβ : β.degree = a then c ⟨β, hβ⟩ else 0) (by
      rw [← MonoDeg.sum_eq_sum_finsuppAntidiag a
        fun β => monoVal f β • if hβ : β.degree = a then c ⟨β, hβ⟩ else 0]
      convert hc using 3 with β
      rw [dif_pos β.2]) α.1 α.2
    rwa [dif_pos α.2] at this
end GlobalTheory
