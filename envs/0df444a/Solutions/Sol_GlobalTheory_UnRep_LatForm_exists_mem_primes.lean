-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.exists_mem_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:48.488681+00:00
-- url     : https://prove2.me/submissions/fd8c9f72-474a-443c-b085-40455d8a99db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ s ∈ I, s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → I ≤ P := by
  classical
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨s, hs⟩ := h2
  have hs' : I ^ h = Ideal.span {s} := hs
  refine ⟨s, Ideal.pow_le_self hpos (hs' ▸ Ideal.mem_span_singleton_self s), ?_, fun P hP hsP => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hs']; simp)
  · exact (Ideal.IsPrime.pow_le_iff hpos).1 (by rw [hs']; exact (Ideal.span_singleton_le_iff_mem _).2 hsP)
end GlobalTheory.UnRep.LatForm
