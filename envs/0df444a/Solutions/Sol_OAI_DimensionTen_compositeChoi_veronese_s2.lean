-- Prove2me | solution 1 for OAI.DimensionTen.compositeChoi_veronese_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:53:40.220411+00:00
-- url     : https://prove2.me/submissions/43406ddc-d17b-48e5-982b-baabd3ce4421

import Mathlib
import Definitions.Def_OAIQ057D013

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PureMatrices
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pure_conjugate {a b : Type*} [Fintype a] (V : Matrix b a ℂ) (x : a → ℂ) :
    V * pure x * Vᴴ = pure (V *ᵥ x) := by
  simp only [pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

lemma pure_kronecker {a b : ℕ} (x : Fin a → ℂ) (y : Fin b → ℂ) :
    pure (productVector x y) = pure x ⊗ₖ pure y := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [pure, productVector, Matrix.vecMulVec_apply]
  ring

lemma trace_pure_mul {n : Type*} [Fintype n] (x : n → ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (pure x * A) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [pure, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

lemma linear_comp {a b c : ℕ} (F : Mat a → Mat b) (G : Mat b → Mat c)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) :
    IsComplexLinear (G ∘ F) := by
  constructor
  · intro A B; simp only [Function.comp_apply, hF.1, hG.1]
  · intro c A; simp only [Function.comp_apply, hF.2, hG.2]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ChoiPairing
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma matrix_expansion {a : ℕ} (A : Mat a) :
    A = ∑ i : Fin a, ∑ j : Fin a, A i j • Matrix.single i j 1 := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma linear_expansion {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) (A : Mat a) :
    F A = ∑ i : Fin a, ∑ j : Fin a, A i j • F (Matrix.single i j 1) := by
  calc
    F A = F (∑ i, ∑ j, A i j • Matrix.single i j 1) := congrArg F (matrix_expansion A)
    _ = _ := by
      change asLinearMap F hF _ = _
      simp only [map_sum, map_smul, asLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma choi_trace_pairing {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (A : Mat a) (B : Mat b) :
    Matrix.trace ((A ⊗ₖ B) * choi F) = Matrix.trace (B * F Aᵀ) := by
  rw [linear_expansion F hF Aᵀ]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, choi, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.transpose_apply, Finset.mul_sum]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [sum_four_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma choi_product_dot {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F)
    (u : Fin a → ℂ) (v : Fin b → ℂ) :
    star (productVector u v) ⬝ᵥ (choi F *ᵥ productVector u v) =
      Matrix.trace (pure v * F (pure u)ᵀ) := by
  rw [← trace_pure_mul, pure_kronecker, choi_trace_pairing F hF]

lemma kraus_trace_adjoint {r a b : Type*} [Fintype r] [Fintype a] [Fintype b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (B : Matrix b b ℂ) :
    Matrix.trace (A * krausMap (fun k => (Q k)ᴴ) B) =
      Matrix.trace (krausMap Q A * B) := by
  simp only [krausMap, Matrix.conjTranspose_conjTranspose, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    Matrix.trace (A * ((Q k)ᴴ * B * Q k)) =
      Matrix.trace ((A * (Q k)ᴴ * B) * Q k) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q k * (A * (Q k)ᴴ * B)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_MinorData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

 lemma det_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
     M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2 - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1 + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1 - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2 + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0 - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0 + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1 - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0 + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0 - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1 + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0 - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Veronese
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma sqrtTwo_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

lemma sqrtTwo_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))

lemma symmetric_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry *ᵥ veronese x = productVector x x := by
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, symmetricIsometry,
      symmetricPairs, veronese, productVector] <;>
      field_simp [sqrtTwo_ne]

lemma symmetric_pure_veronese (x : Fin 4 → ℂ) :
    symmetricIsometry * pure (veronese x) * symmetricIsometryᴴ =
      pure x ⊗ₖ pure x := by
  rw [pure_conjugate, symmetric_veronese, pure_kronecker]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_CompoundTrace
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma exterior_left_entry {r : Type*} (X : Matrix (Fin 4 × Fin 4) r ℂ)
    (i : Fin 6) (j : r) :
    (exteriorIsometryᴴ * X) i j =
      (X (exteriorPairs i) j - X ((exteriorPairs i).2, (exteriorPairs i).1) j) /
        (Real.sqrt 2 : ℂ) := by
  rw [exteriorIsometry_real]
  simp [Matrix.mul_apply, Matrix.transpose_apply, exteriorIsometry,
    div_eq_mul_inv, mul_sub, Finset.sum_sub_distrib,
    mul_ite, Prod.mk.eta, mul_comm]

lemma exterior_right_entry {r : Type*} (X : Matrix r (Fin 4 × Fin 4) ℂ)
    (i : r) (j : Fin 6) :
    (X * exteriorIsometry) i j =
      (X i (exteriorPairs j) - X i ((exteriorPairs j).2, (exteriorPairs j).1)) /
        (Real.sqrt 2 : ℂ) := by
  simp [Matrix.mul_apply, exteriorIsometry, div_eq_mul_inv, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ite_mul, mul_ite, Prod.mk.eta]

lemma exterior_compression_entry (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (i j : Fin 6) :
    (exteriorIsometryᴴ * X * exteriorIsometry) i j =
      (X (exteriorPairs i) (exteriorPairs j) -
       X ((exteriorPairs i).2, (exteriorPairs i).1) (exteriorPairs j) -
       X (exteriorPairs i) ((exteriorPairs j).2, (exteriorPairs j).1) +
       X ((exteriorPairs i).2, (exteriorPairs i).1)
         ((exteriorPairs j).2, (exteriorPairs j).1)) / 2 := by
  rw [exterior_right_entry, exterior_left_entry, exterior_left_entry]
  field_simp [sqrtTwo_ne]
  ring_nf
  rw [sqrtTwo_sq]

lemma exterior_compound (B : Mat 4) :
    exteriorIsometryᴴ * (B ⊗ₖ B) * exteriorIsometry = compound B := by
  ext i j
  rw [exterior_compression_entry]
  simp only [Matrix.kroneckerMap_apply, compound]
  ring

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma hodgeComplement_adjoint : hodgeComplementᴴ = hodgeComplement := by
  ext i j
  change star (hodgeComplement j i) = hodgeComplement i j
  fin_cases i <;> fin_cases j <;> norm_num [hodgeComplement]

lemma hodge_mul_entry (A : Mat 6) (i j : Fin 6) :
    (hodgeComplement * A) i j = complementarySign i * A (complementaryIndex i) j := by
  change (∑ k : Fin 6, hodgeComplement i k * A k j) = _
  fin_cases i <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma mul_hodge_entry (A : Mat 6) (i j : Fin 6) :
    (A * hodgeComplement) i j = complementarySign j * A i (complementaryIndex j) := by
  change (∑ k : Fin 6, A i k * hodgeComplement k j) = _
  fin_cases j <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma compound_trace (B : Mat 4) :
    Matrix.trace (hodgeComplement * (compound B)ᵀ * hodgeComplementᴴ * compound B) =
      6 * B.det := by
  rw [hodgeComplement_adjoint, Border.det_four]
  change (∑ i : Fin 6, ∑ j : Fin 6,
    (hodgeComplement * (compound B)ᵀ * hodgeComplement) i j * compound B j i) = _
  simp only [mul_hodge_entry, hodge_mul_entry, Matrix.transpose_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [compound, exteriorPairs, TensorCriterion.altPair, complementaryIndex, complementarySign]
  ring

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma pencilMap_linear : IsComplexLinear pencilMap := by
  rw [pencilMap_kraus]
  exact krausMap_linear _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

lemma phiOne_ppt : PPT phiOne := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiOne_kraus]; exact krausMap_linear _
  · rw [phiOne_kraus]; exact krausMap_cp _
  · simp only [phiOne_output_transpose]
    rw [phiOne_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorEvaluation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma tensorMap_kronecker {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : IsComplexLinear F) (hG : IsComplexLinear G) (A : Mat a) (B : Mat c) :
    tensorMap F G (A ⊗ₖ B) = F A ⊗ₖ G B := by
  have hblock (i j : Fin c) : (fun u v => A u v * B i j) = B i j • A := by
    ext u v
    simp [Matrix.smul_apply, mul_comm]
  rw [linear_expansion G hG B]
  ext ⟨u,i⟩ ⟨v,j⟩
  simp only [tensorMap, Matrix.kronecker, Matrix.sum_apply, hblock, hF.2,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma exteriorMap_veronese (x : Fin 4 → ℂ) :
    exteriorMap (pure (veronese x)) = compound (pencilMap (pure x)) := by
  unfold exteriorMap
  rw [symmetric_pure_veronese, tensorMap_kronecker _ _ pencilMap_linear pencilMap_linear]
  exact exterior_compound _

lemma firstSix_isometry : firstSixᴴ * firstSix = (1 : Mat 6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, firstSix, Matrix.conjTranspose_apply,
      Matrix.one_apply]

lemma firstSix_compression (B : Mat 6) :
    firstSixᴴ * (firstSix * B * firstSixᴴ) * firstSix = B := by
  calc
    _ = (firstSixᴴ * firstSix) * B * (firstSixᴴ * firstSix) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [firstSix_isometry]; simp

lemma phiTwo_phiOne (A : Mat 10) :
    phiTwo (phiOne A) = hsAdjoint complementaryMap (exteriorMap Aᵀ) := by
  unfold phiTwo phiOne
  rw [firstSix_compression]

lemma compositeChoi_pairing (u v : Fin 10 → ℂ) :
    star (productVector u v) ⬝ᵥ (compositeChoi *ᵥ productVector u v) =
      Matrix.trace (complementaryMap (pure v) * exteriorMap (pure u)) := by
  rw [compositeChoi, choi_product_dot _ (linear_comp _ _ phiOne_ppt.1 phiTwo_ppt.1)]
  simp only [Function.comp_apply, phiTwo_phiOne, Matrix.transpose_transpose]
  rw [complementaryMap_kraus, krausMap_adjoint, kraus_trace_adjoint]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Main
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma compositeChoi_veronese_s2_oai (x : Fin 4 → ℂ) :
    star (productVector (veronese x) (veronese x)) ⬝ᵥ
      (compositeChoi *ᵥ productVector (veronese x) (veronese x)) =
      6 * (pencilMap (pure x)).det := by
  rw [compositeChoi_pairing]
  unfold complementaryMap
  rw [exteriorMap_veronese, compound_trace]

end DimensionTen

end
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.compositeChoi_veronese_s2_oai := @OAI.DimensionTen.compositeChoi_veronese_s2_oai
