-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.map_perSub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:24.785522+00:00
-- url     : https://prove2.me/submissions/98032b24-05fe-4a81-b481-fd0748b3970e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
import Theorems.Thm_GlobalTheory_SW_LinChange_mem_perSub_iff
import Theorems.Thm_GlobalTheory_SW_LinChange_map_nat_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) :
    (perSub K κ ι (R * M)).map T.toAddEquiv.toAddMonoidHom ≤ perSub K κ ι R := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := (mem_perSub_iff _ _).1 hx
  refine (mem_perSub_iff _ _).2 ⟨_, hT y hy, ?_⟩
  rw [smul_smul, ← Nat.cast_mul]
  exact map_nat_smul T.toLinearMap _ _
end GlobalTheory.SW.LinChange
