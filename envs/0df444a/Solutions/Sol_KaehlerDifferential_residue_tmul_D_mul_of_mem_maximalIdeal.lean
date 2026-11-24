-- Prove2me | solution 1 for KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:56.289806+00:00
-- url     : https://prove2.me/submissions/2fe5e068-cdd1-4902-8658-023f6da04c72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential
namespace KaehlerDifferential
theorem _root_.solution (k : Type*) [CommRing k] (A : Type*)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  have hsm : ∀ a : A, a • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A a := by
    intro a
    rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
  have hx0 : IsLocalRing.residue A x = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hstep : IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x)
      = (IsLocalRing.residue A c * 1) ⊗ₜ[A] KaehlerDifferential.D k A x := rfl
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, hsm, hsm, hx0, TensorProduct.zero_tmul, zero_add, hstep,
    mul_one]
end KaehlerDifferential
