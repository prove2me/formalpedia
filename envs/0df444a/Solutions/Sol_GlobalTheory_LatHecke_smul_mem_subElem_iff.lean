-- Prove2me | solution 1 for GlobalTheory.LatHecke.smul_mem_subElem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:59.299931+00:00
-- url     : https://prove2.me/submissions/a7e76a5e-cbc3-4895-8051-30bed6a17887

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Theorems.Thm_GlobalTheory_LatHecke_glMap_le_glMap_iff
import Theorems.Thm_GlobalTheory_LatHecke_glMap_smul
import Theorems.Thm_GlobalTheory_LatHecke_smul_def
import Theorems.Thm_GlobalTheory_LatHecke_smul_mem_subIdx_iff

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
theorem _root_.solution (g : GL (Fin r) K) (k : ℕ) (M L : Lat O K r) :
    g • M ∈ subElem k (g • L) ↔ M ∈ subElem k L := by
  have h := smul_mem_subIdx_iff g k M L
  simp only [subElem, Set.mem_setOf_eq, h]
  simp only [smul_def, glLat_val, ← glMap_smul, glMap_le_glMap_iff]
end GlobalTheory.LatHecke
