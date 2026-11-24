-- Prove2me | solution 1 for GlobalTheory.PrimeSection.res_inf_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:48:36.024802+00:00
-- url     : https://prove2.me/submissions/680f9653-d675-4d58-b1c3-0b6c9136ecb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_eq_of_germ_eq

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
theorem _root_.solution {D : X.Opens} (hD : genericPoint X ∈ D) (W : X.Opens) :
    Function.Injective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op) := by
  intro s s' hss
  refine eq_of_germ_eq fun hW => ?_
  have hWD : genericPoint X ∈ W ⊓ D := ⟨hW, hD⟩
  rw [← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s, ← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s', hss]
end GlobalTheory.PrimeSection
