-- Prove2me | solution 1 for GlobalTheory.SplitLift.exists_lift_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:08.234391+00:00
-- url     : https://prove2.me/submissions/add14ba0-16cf-4a26-9883-5903c3481f16

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
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
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.SplitLift
theorem _root_.solution {S k : Type} [CommRing S] [Field k] (r : S →+* k) (ε : S)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (M : GL (Fin n) k) :
    ∃ N N' : Matrix (Fin n) (Fin n) S, N.map r = (M : Matrix (Fin n) (Fin n) k) ∧
      N * N' = ε • (1 : Matrix (Fin n) (Fin n) S) ∧ N' * N = ε • (1 : Matrix (Fin n) (Fin n) S) := by
  choose f hf using hr
  let N : Matrix (Fin n) (Fin n) S := (M : Matrix (Fin n) (Fin n) k).map f
  have hN : N.map r = (M : Matrix (Fin n) (Fin n) k) := by
    ext i j; simp [N, hf]
  have hd : r N.det ≠ 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN]
    exact (Matrix.isUnits_det_units M).ne_zero
  obtain ⟨t, ht⟩ := hloc _ hd
  refine ⟨N, (t * ε) • N.adjugate, hN, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1; linear_combination ht
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    congr 1; linear_combination ht
end GlobalTheory.SplitLift
