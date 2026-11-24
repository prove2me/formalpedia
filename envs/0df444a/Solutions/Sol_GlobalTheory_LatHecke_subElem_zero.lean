-- Prove2me | solution 1 for GlobalTheory.LatHecke.subElem_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:32.043175+00:00
-- url     : https://prove2.me/submissions/20ea8e35-ea7a-42aa-88d5-132a34ba0c62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Theorems.Thm_GlobalTheory_LatHecke_subIdx_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
variable [IsFractionRing O K] (r : ℕ)
variable {O K r}
variable [Finite (IsLocalRing.ResidueField O)]
namespace GlobalTheory.LatHecke
theorem _root_.solution (L : Lat O K r) : subElem 0 L = {L} := by
  ext M
  simp only [subElem, subIdx_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, Submodule.smul_le_right⟩
end GlobalTheory.LatHecke
