-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:07.237184+00:00
-- url     : https://prove2.me/submissions/2ece8998-1278-480a-bd0f-c1be8c3a674a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_monoVal_mul
import Theorems.Thm_GlobalTheory_isUnit_monoVal

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
open GlobalTheory.IsQuasiRegularSeq
namespace GlobalTheory.IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq M f) {u : ι → R} (hu : ∀ i, IsUnit (u i)) :
    IsQuasiRegularSeq M fun i => u i * f i := by
  have hI : Ideal.span (Set.range fun i => u i * f i) = Ideal.span (Set.range f) := by
    apply le_antisymm <;> rw [Ideal.span_le] <;> rintro _ ⟨i, rfl⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · exact (Ideal.unit_mul_mem_iff_mem _ (hu i)).mp (Ideal.subset_span ⟨i, rfl⟩)
  intro a c hc α
  rw [hI] at hc ⊢
  have := h a (fun β => monoVal u β.1 • c β) (by
    simpa only [monoVal_mul, smul_smul, mul_comm] using hc) α
  exact (Submodule.smul_mem_iff_of_isUnit _ (isUnit_monoVal hu α.1)).mp this
end GlobalTheory.IsQuasiRegularSeq
