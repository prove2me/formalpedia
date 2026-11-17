-- Prove2me | solution 1 for N25.unitRelationNumeratorPolynomial25_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:14.132211+00:00
-- url     : https://prove2.me/submissions/88416730-45f4-458b-8c95-2036a6d1aa21

import Mathlib
import Theorems.Thm_Polynomial_coeff_eq_zero_of_coprime_evals_dvd
import Theorems.Thm_N25_unitRelationNumeratorPolynomial25_coeff_bound
import Definitions.Def_N25_UnitRelationCertificate
import Theorems.Thm_N25_unitRelationNumeratorResidue25_sound
import Definitions.Def_Polynomial_BinomialResidue
import Theorems.Thm_N25_unitRelationNumeratorResidue25_first
import Theorems.Thm_N25_unitRelationNumeratorResidue25_second
import Theorems.Thm_N25_unitRelationNumeratorResidue25_third
import Theorems.Thm_N25_unitRelationNumeratorResidue25_fourth
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace N25

/-- The four independently checked evaluations determine all required
coefficients because their coprime bases exceed the proven coefficient bound. -/
theorem _root_.solution :
    ∀ n : ℕ, n < 4951 → (unitRelationNumeratorPolynomial25 199).coeff n = 0 := by
  let b₀ : ℤ := unitRelationCertificateBase25 0
  let b₁ : ℤ := unitRelationCertificateBase25 1
  let b₂ : ℤ := unitRelationCertificateBase25 2
  let b₃ : ℤ := unitRelationCertificateBase25 3
  have h₀ : 0 < b₀ := by norm_num [b₀, unitRelationCertificateBase25]
  have h₁ : 0 < b₁ := by norm_num [b₁, unitRelationCertificateBase25]
  have h₂ : 0 < b₂ := by norm_num [b₂, unitRelationCertificateBase25]
  have h₃ : 0 < b₃ := by norm_num [b₃, unitRelationCertificateBase25]
  have hc₀₁ : IsCoprime b₀ b₁ := by
    refine ⟨-1237940039285380274899124222, 1237940039285380274899124223, ?_⟩
    norm_num [b₀, b₁, unitRelationCertificateBase25]
  have hc₂ : IsCoprime (b₀*b₁) b₂ := by
    refine ⟨-928455029464035206174343166,
      2298743311298833287537520536702158647750622789853249537, ?_⟩
    norm_num [b₀, b₁, b₂, unitRelationCertificateBase25]
  have hc₃ : IsCoprime (b₀*b₁*b₂) b₃ := by
    refine ⟨1186359204315156096778327378,
      -7272360761912722758975850210824473497162813741768820232455605759998107016920825849, ?_⟩
    norm_num [b₀, b₁, b₂, b₃, unitRelationCertificateBase25]
  apply Polynomial.coeff_eq_zero_of_coprime_evals_dvd _ 4951
    b₀ b₁ b₂ b₃ h₀ h₁ h₂ h₃ hc₀₁ hc₂ hc₃
  · intro n hn
    exact (unitRelationNumeratorPolynomial25_coeff_bound n hn).trans
      (by
        rw [show 360 = 180*2 from rfl, pow_mul]
        norm_num [b₀, b₁, b₂, b₃, unitRelationCertificateBase25])
  · exact unitRelationNumeratorResidue25_sound _ _
      (by norm_num [unitRelationCertificateBase25]) unitRelationNumeratorResidue25_first
  · exact unitRelationNumeratorResidue25_sound _ _
      (by norm_num [unitRelationCertificateBase25]) unitRelationNumeratorResidue25_second
  · exact unitRelationNumeratorResidue25_sound _ _
      (by norm_num [unitRelationCertificateBase25]) unitRelationNumeratorResidue25_third
  · exact unitRelationNumeratorResidue25_sound _ _
      (by norm_num [unitRelationCertificateBase25]) unitRelationNumeratorResidue25_fourth

end N25
