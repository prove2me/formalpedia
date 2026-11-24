-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_mem_only
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:48.50023+00:00
-- url     : https://prove2.me/submissions/a4323a39-0e08-4064-8777-abe2431f909e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
    mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 F)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ h, pow_mem hv h⟩ = 1 := by
    have : (⟨v.asIdeal ^ h, pow_mem hv h⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
        ⟨v.asIdeal, hv⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff _).1 h1
  have ha' : v.asIdeal ^ h = Ideal.span {a} := ha
  refine ⟨a, ?_, ?_, ?_⟩
  · rintro rfl
    have : v.asIdeal ^ h = ⊥ := by rw [ha']; simp
    exact pow_ne_zero h v.ne_bot this
  · exact Ideal.pow_le_self hpos (ha' ▸ Ideal.mem_span_singleton_self a)
  · intro w hw haw
    have hle : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [ha']; exact (Ideal.span_singleton_le_iff_mem _).2 haw
    have := w.isPrime
    have h2 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hle
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2).symm)
end GlobalTheory.QNorm
