-- Prove2me | solution 1 for GlobalTheory.InertZeta.HeisCoord.mul_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:44.547828+00:00
-- url     : https://prove2.me/submissions/9ca54741-0266-4da1-bc24-b6da719972c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_shape_of_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta.HeisCoord
theorem _root_.solution {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := shape_of_mem hu
  obtain ⟨h00', h0m', h0l', hm0', hmm', hml', hl0', hlm', hll'⟩ := shape_of_mem hu'
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simp only [rowOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [h00, h0m, h0l, hmm', hl0', hlm', h0m']
    ring
  · simp only [colOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [hm0, hmm, hml, hml', hll', h0l']
    ring
  · simp only [cornerOf, mat_mul, Matrix.mul_apply, sum_idx, dotProduct]
    simp [h00, h0m, h0l, hml', hll', h0l']
    ring
end GlobalTheory.InertZeta.HeisCoord
