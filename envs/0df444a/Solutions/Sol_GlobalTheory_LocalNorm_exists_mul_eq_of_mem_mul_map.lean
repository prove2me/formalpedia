-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_mul_eq_of_mem_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:05.151481+00:00
-- url     : https://prove2.me/submissions/6cc8f634-94bd-471e-ad48-4485dab7da03

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {B : Type*} [CommRing B] (σ : B →+* B) {I : Ideal B}
    {i r m : B} (h : Ideal.span {r} * I ≤ Ideal.span {i}) (hm : m ∈ I * I.map σ) :
    ∃ c, c * (i * σ i) = r * σ r * m := by
  have h' := Ideal.map_mono (f := σ) h
  rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton] at h'
  have h2 := Ideal.mul_mono h h'
  rw [Ideal.span_singleton_mul_span_singleton, mul_mul_mul_comm,
    Ideal.span_singleton_mul_span_singleton] at h2
  exact Ideal.mem_span_singleton'.1
    (h2 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm))
end GlobalTheory.LocalNorm
