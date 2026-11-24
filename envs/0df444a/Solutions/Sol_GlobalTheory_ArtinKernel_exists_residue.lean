-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:08.417544+00:00
-- url     : https://prove2.me/submissions/bc5d125a-7de9-4f11-97b0-c4eb1c14db8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
namespace GlobalTheory.ArtinKernel
theorem _root_.solution : ∃ ρ : R →ₐ[ℂ] ℂ, ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R := by
  have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := R ⧸ IsLocalRing.maximalIdeal R))
  let e : ℂ ≃ₐ[ℂ] R ⧸ IsLocalRing.maximalIdeal R := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hsurj
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : e.symm (Ideal.Quotient.mk _ r) = 0 := hr
  have h2 := congrArg e h1
  rwa [AlgEquiv.apply_symm_apply, map_zero] at h2
end GlobalTheory.ArtinKernel
