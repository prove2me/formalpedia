-- Prove2me | solution 1 for GlobalTheory.mem_primeIdealOf_iff_evaluation_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:24.957978+00:00
-- url     : https://prove2.me/submissions/735f4a6f-1961-4971-9053-2bc007bf0add

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{0}} {V : Z.Opens}
    (hV : IsAffineOpen V) {z : Z} (hz : z ∈ V) (a : Γ(Z, V)) :
    a ∈ (hV.primeIdealOf ⟨z, hz⟩).asIdeal ↔ Z.evaluation V z hz a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ← not_iff_not, not_not,
    ← PrimeSpectrum.mem_basicOpen, ← hV.fromSpec_preimage_basicOpen]
  change hV.fromSpec (hV.primeIdealOf ⟨z, hz⟩) ∈ Z.basicOpen a ↔ _
  rw [hV.fromSpec_primeIdealOf]
end GlobalTheory
