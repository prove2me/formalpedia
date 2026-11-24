-- Prove2me | solution 1 for GlobalTheory.PrimTransc.exists_separable_specialization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:27.171657+00:00
-- url     : https://prove2.me/submissions/1987ba87-e034-482c-9f72-bf2431a94571

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecialization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open GlobalTheory GlobalTheory.PrimTransc
namespace GlobalTheory.PrimTransc
theorem _root_.solution {D : ℕ} (P : (MvPolynomial (Fin D) ℚ)[X])
    (h : (P.map (algebraMap (MvPolynomial (Fin D) ℚ) (FractionRing (MvPolynomial (Fin D) ℚ)))).Separable) :
    ∃ c : Fin D → ℚ, (P.map (MvPolynomial.eval c)).Separable := by
  set R := MvPolynomial (Fin D) ℚ
  set F := FractionRing R
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨da, hda, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨db, hdb, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors R) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors R) b
  have key : (C db * A) * P + (C da * B) * derivative P = C (da * db) := by
    apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
    have hA' : A.map (algebraMap R F) = C (algebraMap R F da) * a := by
      rw [hA, ← algebraMap_smul F da a, smul_eq_C_mul]
    have hB' : B.map (algebraMap R F) = C (algebraMap R F db) * b := by
      rw [hB, ← algebraMap_smul F db b, smul_eq_C_mul]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hA', hB',
      ← derivative_map, map_mul]
    linear_combination (C (algebraMap R F da) * C (algebraMap R F db)) * hab
  have hδ : da * db ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hda) (nonZeroDivisors.ne_zero hdb)
  obtain ⟨c, hc⟩ : ∃ c : Fin D → ℚ, MvPolynomial.eval c (da * db) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hδ (MvPolynomial.funext fun c => by simpa using hno c)
  refine ⟨c, ?_⟩
  have key' := congrArg (Polynomial.map (MvPolynomial.eval c)) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map] at key'
  have hinv : C (MvPolynomial.eval c (da * db))⁻¹ * C (MvPolynomial.eval c (da * db)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  refine ⟨C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c db) * A.map (MvPolynomial.eval c)),
    C (MvPolynomial.eval c (da * db))⁻¹ * (C (MvPolynomial.eval c da) * B.map (MvPolynomial.eval c)), ?_⟩
  linear_combination C (MvPolynomial.eval c (da * db))⁻¹ * key' + hinv
end GlobalTheory.PrimTransc
