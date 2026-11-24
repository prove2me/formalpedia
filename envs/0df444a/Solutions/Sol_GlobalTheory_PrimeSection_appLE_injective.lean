-- Prove2me | solution 1 for GlobalTheory.PrimeSection.appLE_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:10:11.255563+00:00
-- url     : https://prove2.me/submissions/5567005d-2f8f-4a55-b7aa-81140f461b6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_res
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_bijective
import Theorems.Thm_GlobalTheory_PrimeSection_eq_preimage_inf
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X) [IsOpenImmersion j]
    [Nonempty Y] {U : X.Opens} {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U W h.le) := by
  intro s s' H
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine res_inf_injective (D := j.opensRange) (genericPoint_mem ⟨y, rfl⟩) U
    ((appLE_bijective j inf_le_right (eq_preimage_inf rfl h)).1 ?_)
  rw [appLE_res, appLE_res]
  exact H
end GlobalTheory.PrimeSection
