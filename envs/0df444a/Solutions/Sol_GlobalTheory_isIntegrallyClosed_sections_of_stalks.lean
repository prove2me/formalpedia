-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_sections_of_stalks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:25.117823+00:00
-- url     : https://prove2.me/submissions/396f3b7c-0df5-4adc-b785-e12b00d18b0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) {U : Y.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(Y, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ => ?_
  let q : PrimeSpectrum Γ(Y, U) := ⟨p, inferInstance⟩
  have hq : hU.fromSpec q ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨hU.fromSpec q, hq⟩
  haveI : IsLocalization p.primeCompl (Y.presheaf.stalk (hU.fromSpec q)) :=
    hU.isLocalization_stalk' q hq
  haveI := hY (hU.fromSpec q)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (hU.fromSpec q))
      (Localization.AtPrime p)).toRingEquiv
end _root_.GlobalTheory
end GlobalTheory
