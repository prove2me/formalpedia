-- Prove2me | solution 1 for GlobalTheory.NoetherPrimitive.exists_C_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:30.304457+00:00
-- url     : https://prove2.me/submissions/7c72411a-45f9-41ac-adfc-aa9d10a63f39

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple
import Theorems.Thm_GlobalTheory_NoetherPrimitive_exists_map_eq_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherPrimitive
open Polynomial
open scoped nonZeroDivisors
namespace GlobalTheory.NoetherPrimitive
theorem _root_.solution {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X]) (hp : (p.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ C q ∈ Ideal.span {p, p.derivative} := by
  obtain ⟨u, v, huv⟩ := hp
  obtain ⟨s, hs, U, hU⟩ := exists_map_eq_C_mul (R := R) u
  obtain ⟨t, ht, V, hV⟩ := exists_map_eq_C_mul (R := R) v
  refine ⟨s * t, mul_ne_zero hs ht, Ideal.mem_span_pair.2 ⟨C t * U, C s * V, ?_⟩⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [derivative_map] at huv
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hU, hV, map_mul]
  linear_combination (C (algebraMap R K s) * C (algebraMap R K t)) * huv
end GlobalTheory.NoetherPrimitive
