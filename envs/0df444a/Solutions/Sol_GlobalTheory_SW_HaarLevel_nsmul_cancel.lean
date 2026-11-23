-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.nsmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:54.571459+00:00
-- url     : https://prove2.me/submissions/9acf6dc5-ce8d-46f9-866e-3b94f2a56589

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
omit [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution {R : ℕ} (hR : 0 < R) {x y : Matrix κ ι K} : R • x = R • y ↔ x = y := by
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]
  exact (smul_right_injective _ (by exact_mod_cast hR.ne')).eq_iff
end GlobalTheory.SW.HaarLevel
