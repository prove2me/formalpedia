-- Prove2me | solution 1 for GlobalTheory.PrimeSection.eq_zero_of_component_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:10.342803+00:00
-- url     : https://prove2.me/submissions/ab89467e-2ffc-4943-93fe-d9362ecaeccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_res_inf_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} [IsIntegral X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution {ι : Type v} {U : ι → X.Opens}
    (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (h : s a = 0) (b : ι) : s b = 0 := by
  have hgen : genericPoint X ∈ U a := genericPoint_mem hx
  apply res_inf_injective hgen (U b)
  rw [hs b a, h, map_zero, mul_zero, map_zero]
end GlobalTheory.PrimeSection
