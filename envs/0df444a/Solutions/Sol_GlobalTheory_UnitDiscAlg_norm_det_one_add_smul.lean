-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.norm_det_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:56.768558+00:00
-- url     : https://prove2.me/submissions/67a73f01-7019-4a03-bf4d-7bb43f5d304a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
    (x : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ‖(1 + ϖ • x).det‖ = 1 := by
  set O := unitBallSubring E
  let y : Matrix (Fin n) (Fin n) O := fun i j => ⟨x i j, hx i j⟩
  let w : O := ⟨ϖ, hϖ.le⟩
  have hmap : O.subtype.mapMatrix (1 + w • y) = 1 + ϖ • x := by
    rw [map_add, map_one]
    congr 1
  have hdet : (1 + ϖ • x).det = ((1 + w • y).det : E) := by
    rw [← hmap, ← RingHom.map_det]; rfl
  have hq : (Ideal.Quotient.mk (Ideal.span {w})) (1 + w • y).det = 1 := by
    rw [RingHom.map_det, map_add, map_one]
    have : (Ideal.Quotient.mk (Ideal.span {w})).mapMatrix (w • y) = 0 := by
      ext i j
      simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rw [this, add_zero, Matrix.det_one]
  have hmem : (1 + w • y).det - 1 ∈ Ideal.span {w} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hq, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hc' : ((1 + w • y).det : E) - 1 = (c : E) * ϖ := by
    have := congrArg Subtype.val hc
    simpa [w] using this.symm
  have hlt : ‖(1 + ϖ • x).det - 1‖ < 1 := by
    rw [hdet, hc', norm_mul]
    calc ‖(c : E)‖ * ‖ϖ‖ ≤ 1 * ‖ϖ‖ := mul_le_mul_of_nonneg_right c.2 (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hϖ
  have key : (1 + ϖ • x).det = 1 + ((1 + ϖ • x).det - 1) := by ring
  rw [key, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne')]
  simp [hlt.le]
end GlobalTheory.UnitDiscAlg
