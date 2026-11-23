-- Prove2me | solution 1 for GlobalTheory.existsUnique_isPrincipal_mul_classRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:06.721847+00:00
-- url     : https://prove2.me/submissions/a7a66f86-8239-451a-be99-5a9abe8711e0

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
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! c, (I * (b c : Ideal (𝓞 K))).IsPrincipal := by
  have hI0 : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have key : ∀ c, (I * (b c : Ideal (𝓞 K))).IsPrincipal ↔
      ClassGroup.mk0 (b c) = (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹ := by
    intro c
    rw [eq_inv_iff_mul_eq_one, mul_comm, ← map_mul]
    rw [ClassGroup.mk0_eq_one_iff]
    rfl
  obtain ⟨c, hc⟩ := hb.2 (ClassGroup.mk0 ⟨I, hI0⟩)⁻¹
  refine ⟨c, (key c).2 hc, fun c' hc' => hb.1 ?_⟩
  simp only
  rw [(key c').1 hc']
  exact hc.symm
end _root_.GlobalTheory
end GlobalTheory
