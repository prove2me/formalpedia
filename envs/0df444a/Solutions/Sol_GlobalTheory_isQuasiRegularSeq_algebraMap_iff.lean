-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:13.967765+00:00
-- url     : https://prove2.me/submissions/a5aeee54-e0be-4092-b176-f89d51c92676

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Theorems.Thm_GlobalTheory_map_monoVal

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
theorem _root_.solution (S : Type*) [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (f : ι → R) :
    IsQuasiRegularSeq M (fun i => algebraMap R S (f i)) ↔ IsQuasiRegularSeq M f := by
  have hI : Ideal.span (Set.range fun i => algebraMap R S (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap R S) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hm : ∀ (J : Ideal R) (x : M),
      x ∈ (J.map (algebraMap R S) • ⊤ : Submodule S M) ↔ x ∈ (J • ⊤ : Submodule R M) := by
    intro J x
    rw [← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  simp only [IsQuasiRegularSeq, hI, ← Ideal.map_pow, hm, ← map_monoVal, algebraMap_smul]
end GlobalTheory
