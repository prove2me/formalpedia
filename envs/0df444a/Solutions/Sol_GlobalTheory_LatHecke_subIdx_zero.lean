-- Prove2me | solution 1 for GlobalTheory.LatHecke.subIdx_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:34.960666+00:00
-- url     : https://prove2.me/submissions/b13cc11a-1e3d-4773-8960-f9b932d670ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt

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
theorem _root_.solution (L : Lat O K r) : subIdx 0 L = {L} := by
  ext M
  simp only [subIdx, pow_zero, Set.mem_setOf_eq, Set.mem_singleton_iff,
    AddSubgroup.relIndex_eq_one, Submodule.toAddSubgroup_le]
  constructor
  · rintro ⟨h1, h2⟩; exact Subtype.ext (le_antisymm h1 h2)
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩
end GlobalTheory.LatHecke
