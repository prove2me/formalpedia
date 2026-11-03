-- Prove2me | solution 1 for OAI.Laughlin.Fock.source_physical_four_body_certificates_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:58:14.774962+00:00
-- url     : https://prove2.me/submissions/2fdc6265-cbbd-41c2-945f-176dba016e8e

import Mathlib
import Definitions.Def_OAIQ050L010
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Certificate_four_body_certificates_s50
import Theorems.Thm_OAI_Laughlin_Fock_physicalLimitGram_eq_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_fourBody_error_matrix_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_MatrixCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem compressed_congruence_identity {n : ℕ}
    (D Z Y K : Matrix (Fin n) (Fin n) ℝ) :
    (D*Z*D) * (K-D*Y*D) * (D*Z*D) =
      D * (Z * (D*K*D-(D*D)*Y*(D*D)) * Z) * D := by
  noncomm_ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Scaled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem cast_rat_diagonal {n : ℕ} (v : Fin n → ℚ) :
    (Matrix.diagonal v).map (Rat.castHom ℝ) = Matrix.diagonal (fun i => (v i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply,h]

theorem cast_rat_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A-B).map (Rat.castHom ℝ) = A.map (Rat.castHom ℝ)-B.map (Rat.castHom ℝ) := by
  ext i j
  simp [Matrix.map_apply,Matrix.sub_apply]

theorem copyWeight_nonneg (D : ℕ) (i : Fin ((D+1)/2)) : 0 ≤ (copyWeight D i : ℝ) := by
  unfold copyWeight
  positivity

theorem weightSqrtDiagonal_sq (D : ℕ) :
    weightSqrtDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (copyWeight D)).map (Rat.castHom ℝ) := by
  rw [weightSqrtDiagonal,Matrix.diagonal_mul_diagonal,cast_rat_diagonal]
  congr 1
  funext i
  simpa [pow_two] using Real.sq_sqrt (copyWeight_nonneg D i)

theorem weightSqrtDiagonal_middle_diagonal (D : ℕ) :
    weightSqrtDiagonal D * certificateDiagonal D * weightSqrtDiagonal D =
      (Matrix.diagonal (fun i => ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ))*copyWeight D i)).map
        (Rat.castHom ℝ) := by
  simp only [weightSqrtDiagonal,certificateDiagonal,cast_rat_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change Real.sqrt (copyWeight D i : ℝ) *
    (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) * Real.sqrt (copyWeight D i : ℝ) = _
  rw [Rat.cast_mul]
  calc
    _ = (((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ) : ℚ) : ℝ) *
        (Real.sqrt (copyWeight D i : ℝ))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (copyWeight_nonneg D i)]

theorem scaled_compression_identity (D : ℕ) :
    scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D =
      weightSqrtDiagonal D * (compressedRational D).map (Rat.castHom ℝ) * weightSqrtDiagonal D := by
  rw [scaledGram,scaledError,compressed_congruence_identity,
    weightSqrtDiagonal_middle_diagonal,weightSqrtDiagonal_sq]
  simp only [compressedRational,middleRational,Matrix.map_mul,cast_rat_sub]

theorem scaled_compression_positive (D : ℕ)
    (hM : ((compressedRational D).map (Rat.castHom ℝ)).PosSemidef) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef := by
  rw [scaled_compression_identity]
  have hd : (weightSqrtDiagonal D).IsHermitian := by
    simp [weightSqrtDiagonal,Matrix.IsHermitian]
  simpa only [hd.eq] using hM.mul_mul_conjTranspose_same (weightSqrtDiagonal D)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ScaledAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem scaled_four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef :=
  scaled_compression_positive D (four_body_certificates_s50 D hD₁ hD₂)

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix

theorem physicalLimitError_eq (D : ℕ) : physicalLimitError D = Certificate.scaledError D := by
  ext i j
  exact Spin.source_fourBody_error_matrix_s50 D i j

theorem source_physical_four_body_certificates_s50_oai (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalLimitGram Q D * (Certificate.certificateDiagonal D-physicalLimitError D) *
      physicalLimitGram Q D).PosSemidef := by
  rw [physicalLimitGram_eq_s50 Q D hQ,physicalLimitError_eq]
  exact Certificate.scaled_four_body_certificates D hD₁ hD₂

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.source_physical_four_body_certificates_s50_oai := @OAI.Laughlin.Fock.source_physical_four_body_certificates_s50_oai
