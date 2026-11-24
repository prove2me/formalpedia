-- Prove2me | solution 1 for GlobalTheory.LatHecke.smul_mem_subIdx_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:28.865579+00:00
-- url     : https://prove2.me/submissions/9dbd8cf6-06e7-4d3e-842f-fc2756e1943e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Theorems.Thm_GlobalTheory_LatHecke_glMap_le_glMap_iff
import Theorems.Thm_GlobalTheory_LatHecke_relIndex_glMap
import Theorems.Thm_GlobalTheory_LatHecke_smul_def

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
theorem _root_.solution (g : GL (Fin r) K) (n : ℕ) (M L : Lat O K r) :
    g • M ∈ subIdx n (g • L) ↔ M ∈ subIdx n L := by
  simp only [subIdx, Set.mem_setOf_eq, smul_def, glLat_val, glMap_le_glMap_iff, relIndex_glMap]
end GlobalTheory.LatHecke
