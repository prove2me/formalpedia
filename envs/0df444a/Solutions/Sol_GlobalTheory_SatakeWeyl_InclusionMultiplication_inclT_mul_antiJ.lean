-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.InclusionMultiplication.inclT_mul_antiJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:47.887423+00:00
-- url     : https://prove2.me/submissions/f72a0b01-0e79-4a4e-b5c0-ce8fa10e9011

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_antiJ_transpose
import Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_antiJ_mul_incl
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}
namespace GlobalTheory.SatakeWeyl.InclusionMultiplication
theorem _root_.solution {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this
end GlobalTheory.SatakeWeyl.InclusionMultiplication
