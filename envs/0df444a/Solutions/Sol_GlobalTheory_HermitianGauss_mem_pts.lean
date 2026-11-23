-- Prove2me | solution 1 for GlobalTheory.HermitianGauss.mem_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:46.317706+00:00
-- url     : https://prove2.me/submissions/b8253265-86b6-4c8f-a3e0-a8fc7f8e8eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]
namespace GlobalTheory.HermitianGauss
theorem _root_.solution {B : Submodule R M} {x : M} : x ∈ pts B ↔ x ∈ B := by simp [pts]
end GlobalTheory.HermitianGauss
