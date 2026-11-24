-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.levi_mul_rad_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:14.912131+00:00
-- url     : https://prove2.me/submissions/3a85d4e2-b2e4-4afc-b16b-c6cec97ab0ff

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
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
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {L : Type} [Field L] {σ : L →+* L} {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n}
    (hm : ∀ i j, β i ≠ β j → mat m i j = 0)
    (hu : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j) {i l : Fin n} (h : β l ≤ β i) :
    mat (m * u) i l = mat m i l := by
  rw [mat_mul, Matrix.mul_apply]
  have key : ∀ k, mat m i k * mat u k l = mat m i k * (1 : Matrix (Fin n) (Fin n) L) k l := by
    intro k
    by_cases hk : β i = β k
    · rw [hu k l (by rw [← hk]; exact h)]
    · rw [hm i k hk, zero_mul, zero_mul]
  simp_rw [key]
  rw [← Matrix.mul_apply, Matrix.mul_one]
end GlobalTheory.SatakeWeyl
