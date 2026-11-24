-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.incl_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:24.919433+00:00
-- url     : https://prove2.me/submissions/8072e080-b7a3-461c-8b1a-763bcc11d1e3

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
theorem _root_.solution {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]
end GlobalTheory.SatakeWeyl.InclusionMultiplication
