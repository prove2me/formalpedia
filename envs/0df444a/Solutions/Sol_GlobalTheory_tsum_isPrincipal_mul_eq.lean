-- Prove2me | solution 1 for GlobalTheory.tsum_isPrincipal_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:36.73898+00:00
-- url     : https://prove2.me/submissions/09c4b547-fb94-49b4-adb8-29dff51d03a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (hB : B ≠ ⊥) (F : Ideal (𝓞 K) → ℂ) :
    ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal}, F (I * B) =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, F J := by
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * B).IsPrincipal} →
      {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} :=
    fun I => ⟨I.1 * B, mul_ne_zero I.2.1 hB, I.2.2, Ideal.mul_le_inf.trans inf_le_right⟩
  have he : Function.Bijective e := by
    constructor
    · intro I I' h
      have h' : I.1 * B = I'.1 * B := congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel₀ hB h')
    · intro J
      obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 J.2.2.2
      have hI0 : I ≠ ⊥ := by
        rintro rfl
        exact J.2.1 (by rw [hI, Ideal.mul_bot])
      refine ⟨⟨I, hI0, ?_⟩, Subtype.ext ?_⟩
      · rw [mul_comm, ← hI]; exact J.2.2.1
      · show I * B = J.1
        rw [hI, mul_comm]
  exact (Equiv.ofBijective e he).tsum_eq (fun J => F J.1)
end _root_.GlobalTheory
end GlobalTheory
