-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.selfAdjoint_idempotent_posType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:45:45.440912+00:00
-- url     : https://prove2.me/submissions/d91553a6-9057-416a-8591-68888362e82c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_adj_mul
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_isSA_iff
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_coeff_mul_adj_one
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_eq_zero_of_coeff_mul_adj
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_isSA_central
import Theorems.Thm_GlobalTheory_RowLev_GroupAlgPos_posType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
namespace GlobalTheory.RowLev.GroupAlgPos
theorem _root_.solution : ∀ (Q : Type) [Group Q] [Finite Q],
    (∀ a : MonoidAlgebra ℂ Q, a * a = a → IsSA a →
      (∀ (m : ℕ) (x : Fin m → Q) (c : Fin m → ℂ), 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j)) ∧
        0 ≤ a.coeff 1 ∧ (a.coeff 1 = 0 → a = 0)) ∧
    (∀ z : MonoidAlgebra ℂ Q, z * z = z → (∀ a, z * a = a * z) → IsSA z) ∧
    ∀ a b : MonoidAlgebra ℂ Q, IsSA a → IsSA b → a * b = b * a → IsSA (a * b) := by
  intro Q _ _
  haveI := Fintype.ofFinite Q
  refine ⟨fun a h hs => ?_, isSA_central, fun a b ha hb hab => ?_⟩
  · have e : a * adj a = a := by rw [(isSA_iff a).1 hs, h]
    refine ⟨posType a h hs, ?_, fun h0 => eq_zero_of_coeff_mul_adj a (by rw [e, h0])⟩
    rw [← e, coeff_mul_adj_one]
    exact Finset.sum_nonneg fun q _ => mul_star_self_nonneg _
  · rw [isSA_iff] at ha hb ⊢
    rw [adj_mul, ha, hb, hab]
end GlobalTheory.RowLev.GroupAlgPos
