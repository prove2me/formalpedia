-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.inclT_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:22.66626+00:00
-- url     : https://prove2.me/submissions/b8d4f619-21c2-4f9d-a8f3-e6f8ec4519c0

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}
namespace GlobalTheory.SatakeWeyl.InclusionMultiplication
theorem _root_.solution {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, he.eq_iff, Matrix.one_apply, eq_comm]
end GlobalTheory.SatakeWeyl.InclusionMultiplication
