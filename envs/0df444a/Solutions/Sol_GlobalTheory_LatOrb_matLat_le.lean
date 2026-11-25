-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:41.913007+00:00
-- url     : https://prove2.me/submissions/936907e4-8dd9-4800-beb0-3bcfe2c6672a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
variable {K : Type} [Field K] {n : ℕ}
namespace GlobalTheory.LatOrb
theorem _root_.solution {O : Type} [CommRing O] [Algebra O K] (M : Submodule O (Fin n → K))
    (u : Matrix (Fin n) (Fin n) K) (hu : ∀ v ∈ M, u *ᵥ v ∈ M) : matLat O u M ≤ M := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := (mem_matLat u M v).mp hv
  exact hu w hw
end GlobalTheory.LatOrb
