-- Prove2me | solution 1 for GlobalTheory.CharIdem.sum_fiber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:50.968382+00:00
-- url     : https://prove2.me/submissions/f7241986-bc0e-4086-8dda-7647e0e2049b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CharFnLocallyConstant
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
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.CharIdem
variable {G : Type} [Group G]
variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)
namespace GlobalTheory.CharIdem
theorem _root_.solution {ι Q : Type} [Fintype ι] [DecidableEq Q] (q : ι → Q) (a : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) := by
  have h : ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) =
      ∑ t ∈ Finset.univ.image q, star (∑ i, if q i = t then a i else 0) *
        (∑ j, if q j = t then a j else 0) := by
    simp only [star_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j i => if q i = q j then star (a i) * a j else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (q i)]
    · by_cases hij : q i = q j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_image_of_mem q (Finset.mem_univ i)) hb
  rw [h]
  exact Finset.sum_nonneg fun t _ => star_mul_self_nonneg _
end GlobalTheory.CharIdem
