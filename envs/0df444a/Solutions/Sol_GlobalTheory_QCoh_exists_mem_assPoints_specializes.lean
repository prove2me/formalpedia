-- Prove2me | solution 1 for GlobalTheory.QCoh.exists_mem_assPoints_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:51.544282+00:00
-- url     : https://prove2.me/submissions/50569f13-56d7-477d-bb6b-86c4ec92e9aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_mem_support_iff
import Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_mem_assPoints_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] {x : X} (hx : x ∈ support F) :
    ∃ y ∈ assPoints F, y ⤳ x := by
  obtain ⟨U, hU, hxU⟩ := exists_affine_mem x
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = x := ⟨⟨x, hxU⟩, rfl⟩
  have := mem_support_iff.1 hx
  have := hU.isLocalization_stalk x
  obtain ⟨Q, hQ⟩ :=
    associatedPrimes.nonempty (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :)
  have hQ' := (mem_associatedPrimes_stalk_iff F hU x Q).1 hQ
  let P : PrimeSpectrum Γ(X, U) := ⟨_, hQ'.isPrime⟩
  refine ⟨pointOfPrime hU P, (pointOfPrime_mem_assPoints_iff hU P).2 hQ', ?_⟩
  have hle : P ≤ hU.primeIdealOf x := by
    change P.asIdeal ≤ (hU.primeIdealOf x).asIdeal
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (x : X))
      (hU.primeIdealOf x).asIdeal]
    exact Ideal.comap_mono (le_maximalIdeal hQ.isPrime.ne_top)
  have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf] at this
end GlobalTheory.QCoh
