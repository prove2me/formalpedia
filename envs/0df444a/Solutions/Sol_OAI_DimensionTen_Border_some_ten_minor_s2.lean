-- Prove2me | solution 1 for OAI.DimensionTen.Border.some_ten_minor_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:58:23.76029+00:00
-- url     : https://prove2.me/submissions/799bf628-b549-41a7-af04-7d19c9bb78d7

import Mathlib
import Definitions.Def_OAIQ057D011

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_NormalizedMatrices
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma cast_mulVec (B : Matrix (Fin 20) (Fin 20) ℤ) (v : Fin 20 → ℤ) :
    (fun j => ((B *ᵥ v) j : ℚ)) = B.map (Int.castRingHom ℚ) *ᵥ (fun j => (v j : ℚ)) := by
  ext j
  exact (Int.castRingHom ℚ).map_mulVec B v j

lemma cast_single (i : Fin 20) :
    (fun j => ((Pi.single i 1 : Fin 20 → ℤ) j : ℚ)) = eQ i := by
  ext j
  simp [eQ, Pi.single_apply]

lemma normalize_shift (B : Matrix (Fin 20) (Fin 20) ℤ) (i j : Fin 20)
    (h : B *ᵥ Pi.single i 1 = d • Pi.single j 1) :
    ((d : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)) *ᵥ eQ i = eQ j := by
  have hh := congrArg (fun v : Fin 20 → ℤ => fun k => (v k : ℚ)) h
  rw [cast_mulVec, cast_single] at hh
  have hcast : (fun k => ((d • (Pi.single j 1 : Fin 20 → ℤ)) k : ℚ)) = (d : ℚ) • eQ j := by
    ext k
    simp [eQ, Pi.single_apply, smul_eq_mul]
  rw [hcast] at hh
  rw [Matrix.smul_mulVec, hh, smul_smul, inv_mul_cancel₀ dQ_ne_zero, one_smul]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_BorderField
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma E_one : E 1 = eQ 0 := by change rho 1 *ᵥ eQ 0 = _; simp
lemma E_mul (a b : L) : E (a * b) = rho a *ᵥ E b := by
  change rho (a * b) *ᵥ eQ 0 = rho a *ᵥ (rho b *ᵥ eQ 0)
  rw [map_mul, Matrix.mulVec_mulVec]

lemma rho_alpha (i : Fin 3) : rho (alpha i) = NB i := by
  fin_cases i
  · change rho ((d : ℚ)⁻¹ • AdjoinRoot.root fQ) = _
    rw [map_smul, rho_root]
    rfl
  · exact (NB_in_image 1).choose_spec
  · exact (NB_in_image 2).choose_spec

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_LowBasis
attribute [-instance] _root_.OAI.DimensionTen.Border.instIsGaloisRatK _root_.OAI.DimensionTen.Border.instIsSplittingFieldRatKFQ _root_.OAI.DimensionTen.Border.instNumberFieldK _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma low_zero {R : Type*} [CommRing R] (t : Fin 3 → R) : low t 0 = 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma low_shift_1 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 1 = t 2 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_1 : NB 2 *ᵥ eQ 0 = eQ 1 := by
  exact normalize_shift B2 0 1 shift_1

lemma low_shift_2 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 2 = t 1 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_2 : NB 1 *ᵥ eQ 0 = eQ 2 := by
  exact normalize_shift B1 0 2 shift_2

lemma low_shift_3 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 3 = t 0 * low t 0 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_3 : NB 0 *ᵥ eQ 0 = eQ 3 := by
  exact normalize_shift B0 0 3 shift_3

lemma low_shift_4 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 4 = t 2 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_4 : NB 2 *ᵥ eQ 1 = eQ 4 := by
  exact normalize_shift B2 1 4 shift_4

lemma low_shift_5 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 5 = t 1 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_5 : NB 1 *ᵥ eQ 1 = eQ 5 := by
  exact normalize_shift B1 1 5 shift_5

lemma low_shift_6 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 6 = t 1 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_6 : NB 1 *ᵥ eQ 2 = eQ 6 := by
  exact normalize_shift B1 2 6 shift_6

lemma low_shift_7 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 7 = t 0 * low t 1 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_7 : NB 0 *ᵥ eQ 1 = eQ 7 := by
  exact normalize_shift B0 1 7 shift_7

lemma low_shift_8 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 8 = t 0 * low t 2 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_8 : NB 0 *ᵥ eQ 2 = eQ 8 := by
  exact normalize_shift B0 2 8 shift_8

lemma low_shift_9 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 9 = t 0 * low t 3 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_9 : NB 0 *ᵥ eQ 3 = eQ 9 := by
  exact normalize_shift B0 3 9 shift_9

lemma low_shift_10 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 10 = t 2 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_10 : NB 2 *ᵥ eQ 4 = eQ 10 := by
  exact normalize_shift B2 4 10 shift_10

lemma low_shift_11 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 11 = t 1 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_11 : NB 1 *ᵥ eQ 4 = eQ 11 := by
  exact normalize_shift B1 4 11 shift_11

lemma low_shift_12 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 12 = t 1 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_12 : NB 1 *ᵥ eQ 5 = eQ 12 := by
  exact normalize_shift B1 5 12 shift_12

lemma low_shift_13 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 13 = t 1 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_13 : NB 1 *ᵥ eQ 6 = eQ 13 := by
  exact normalize_shift B1 6 13 shift_13

lemma low_shift_14 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 14 = t 0 * low t 4 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_14 : NB 0 *ᵥ eQ 4 = eQ 14 := by
  exact normalize_shift B0 4 14 shift_14

lemma low_shift_15 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 15 = t 0 * low t 5 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_15 : NB 0 *ᵥ eQ 5 = eQ 15 := by
  exact normalize_shift B0 5 15 shift_15

lemma low_shift_16 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 16 = t 0 * low t 6 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]

lemma NB_shift_16 : NB 0 *ᵥ eQ 6 = eQ 16 := by
  exact normalize_shift B0 6 16 shift_16

lemma low_shift_17 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 17 = t 0 * low t 7 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_17 : NB 0 *ᵥ eQ 7 = eQ 17 := by
  exact normalize_shift B0 7 17 shift_17

lemma low_shift_18 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 18 = t 0 * low t 8 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_18 : NB 0 *ᵥ eQ 8 = eQ 18 := by
  exact normalize_shift B0 8 18 shift_18

lemma low_shift_19 {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t 19 = t 0 * low t 9 := by
  simp [low, mon, monExps, Fin.prod_univ_succ]
  ring

lemma NB_shift_19 : NB 0 *ᵥ eQ 9 = eQ 19 := by
  exact normalize_shift B0 9 19 shift_19

lemma E_low_0 : E (low alpha 0) = eQ 0 := by rw [low_zero, E_one]

lemma E_low_1 : E (low alpha 1) = eQ 1 := by
  rw [low_shift_1, E_mul, rho_alpha, E_low_0, NB_shift_1]

lemma E_low_2 : E (low alpha 2) = eQ 2 := by
  rw [low_shift_2, E_mul, rho_alpha, E_low_0, NB_shift_2]

lemma E_low_3 : E (low alpha 3) = eQ 3 := by
  rw [low_shift_3, E_mul, rho_alpha, E_low_0, NB_shift_3]

lemma E_low_4 : E (low alpha 4) = eQ 4 := by
  rw [low_shift_4, E_mul, rho_alpha, E_low_1, NB_shift_4]

lemma E_low_5 : E (low alpha 5) = eQ 5 := by
  rw [low_shift_5, E_mul, rho_alpha, E_low_1, NB_shift_5]

lemma E_low_6 : E (low alpha 6) = eQ 6 := by
  rw [low_shift_6, E_mul, rho_alpha, E_low_2, NB_shift_6]

lemma E_low_7 : E (low alpha 7) = eQ 7 := by
  rw [low_shift_7, E_mul, rho_alpha, E_low_1, NB_shift_7]

lemma E_low_8 : E (low alpha 8) = eQ 8 := by
  rw [low_shift_8, E_mul, rho_alpha, E_low_2, NB_shift_8]

lemma E_low_9 : E (low alpha 9) = eQ 9 := by
  rw [low_shift_9, E_mul, rho_alpha, E_low_3, NB_shift_9]

lemma E_low_10 : E (low alpha 10) = eQ 10 := by
  rw [low_shift_10, E_mul, rho_alpha, E_low_4, NB_shift_10]

lemma E_low_11 : E (low alpha 11) = eQ 11 := by
  rw [low_shift_11, E_mul, rho_alpha, E_low_4, NB_shift_11]

lemma E_low_12 : E (low alpha 12) = eQ 12 := by
  rw [low_shift_12, E_mul, rho_alpha, E_low_5, NB_shift_12]

lemma E_low_13 : E (low alpha 13) = eQ 13 := by
  rw [low_shift_13, E_mul, rho_alpha, E_low_6, NB_shift_13]

lemma E_low_14 : E (low alpha 14) = eQ 14 := by
  rw [low_shift_14, E_mul, rho_alpha, E_low_4, NB_shift_14]

lemma E_low_15 : E (low alpha 15) = eQ 15 := by
  rw [low_shift_15, E_mul, rho_alpha, E_low_5, NB_shift_15]

lemma E_low_16 : E (low alpha 16) = eQ 16 := by
  rw [low_shift_16, E_mul, rho_alpha, E_low_6, NB_shift_16]

lemma E_low_17 : E (low alpha 17) = eQ 17 := by
  rw [low_shift_17, E_mul, rho_alpha, E_low_7, NB_shift_17]

lemma E_low_18 : E (low alpha 18) = eQ 18 := by
  rw [low_shift_18, E_mul, rho_alpha, E_low_8, NB_shift_18]

lemma E_low_19 : E (low alpha 19) = eQ 19 := by
  rw [low_shift_19, E_mul, rho_alpha, E_low_9, NB_shift_19]

lemma E_low (i : Fin 20) : E (low alpha i) = eQ i := by
  fin_cases i
  · exact E_low_0
  · exact E_low_1
  · exact E_low_2
  · exact E_low_3
  · exact E_low_4
  · exact E_low_5
  · exact E_low_6
  · exact E_low_7
  · exact E_low_8
  · exact E_low_9
  · exact E_low_10
  · exact E_low_11
  · exact E_low_12
  · exact E_low_13
  · exact E_low_14
  · exact E_low_15
  · exact E_low_16
  · exact E_low_17
  · exact E_low_18
  · exact E_low_19


lemma basis_eq (i : Fin 20) : basis i = low alpha i := by
  apply E_injective
  simp only [basis, Module.Basis.map_apply, Pi.basisFun_apply, E_low, eQ]
  exact (LinearEquiv.ofBijective E ⟨E_injective, E_surjective⟩).apply_symm_apply _

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_IndependentMinor
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Arithmetic

lemma independent_minor {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Function.Surjective A.mulVec) :
    ∃ a : Fin m → Fin n, Function.Injective a ∧ (A.submatrix id a).det ≠ 0 := by
  classical
  have hsp : Submodule.span K (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr hA
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' K A.col
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ K (Fin m → K) := Module.Basis.mk hl (by rw [hs, hsp])
  have hc : Fintype.card κ = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hh : LinearIndependent K (A.submatrix id (a ∘ e)).col := hl.comp e e.injective
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hh))

lemma restrict_rows_surjective {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0)
    (r : Fin m → Fin n) (hr : Function.Injective r) :
    Function.Surjective (A.submatrix r id).mulVec := by
  classical
  intro v
  let w : Fin n → K := Function.extend r v 0
  have hw : w ∘ r = v := Function.extend_comp hr _ _
  obtain ⟨u, hu⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))) w
  refine ⟨u, ?_⟩
  ext i
  exact (congrFun hu (r i)).trans (congrFun hw i)

end DimensionTen.Arithmetic

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_EvaluationMinors
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma evaluationMatrix_map : evaluationMatrix.map complexEmbedding =
    Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC := by
  ext i j
  change complexEmbedding (embeddingsK j (low alpha i)) = embeddingsC j (basis i)
  rw [basis_eq]
  rfl

lemma evaluationMatrix_det_ne : evaluationMatrix.det ≠ 0 := by
  intro hz
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ basis embeddingsC
  have hc : (Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC).det = 0 := by
    rw [← evaluationMatrix_map]
    erw [← complexEmbedding.map_det, hz, map_zero]
  rw [hc, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hd
  exact Algebra.discr_not_zero_of_basis ℚ basis ((algebraMap ℚ ℂ).injective (hd.trans (map_zero _).symm))

lemma some_ten_minor_s2_oai : ∃ a : Fin 10 → Fin 20, Function.Injective a ∧
    (evaluationMatrix.submatrix firstTen a).det ≠ 0 := by
  obtain ⟨a, ha, hd⟩ := Arithmetic.independent_minor
    (evaluationMatrix.submatrix firstTen id)
    (Arithmetic.restrict_rows_surjective evaluationMatrix evaluationMatrix_det_ne
      firstTen (Fin.castLE_injective _))
  exact ⟨a, ha, hd⟩

end DimensionTen.Border

end
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.Border.some_ten_minor_s2_oai := @OAI.DimensionTen.Border.some_ten_minor_s2_oai
