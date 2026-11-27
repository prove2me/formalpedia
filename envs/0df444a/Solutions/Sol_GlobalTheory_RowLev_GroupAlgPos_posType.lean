-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.posType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:47.40881+00:00
-- url     : https://prove2.me/submissions/7bc60fb6-db00-433b-b415-9867c102936a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_coeff_inv_mul
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
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
namespace GlobalTheory.RowLev.GroupAlgPos
theorem _root_.solution [Finite Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (m : ℕ) (x : Fin m → Q)
    (c : Fin m → ℂ) : 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) := by
  haveI := Fintype.ofFinite Q
  have e : ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) =
      ∑ q : Q, star (∑ j, c j * a.coeff (q⁻¹ * x j)) * ∑ j, c j * a.coeff (q⁻¹ * x j) := by
    simp only [coeff_inv_mul a h hs (x _), star_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul']
    ring
  rw [e]
  exact Finset.sum_nonneg fun q _ => star_mul_self_nonneg _
end GlobalTheory.RowLev.GroupAlgPos
