-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.phiQ_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:50:51.444385+00:00
-- url     : https://prove2.me/submissions/e4e2cd0a-91ab-4c5b-92b1-74f256edc1c8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_unramifiedCharExt_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_Jset_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Eigen_step
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_parJ_compact_open
import Theorems.Thm_GlobalTheory_T_parahoric_character_modulus_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
    LF O ϖ nrm q → ∀ δ : Fˣ →* ℂˣ, Del nrm δ → ∀ r d c : ℕ, ∀ k ∈ parJ O ϖ r c,
    ∀ x : Matrix (Fin (r + d)) (Fin (r + c)) F,
    ((δ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
        phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) =
      lamJ δ k * phiQ O ϖ δ r d c x := by
  intro F _ _ _ _ O ϖ nrm q hLF δ hδ r d c k hk x
  by_cases hx : Supp O ϖ x
  · obtain ⟨hs, hc⟩ := step hLF δ hδ hk hx
    have hp1 : phiQ O ϖ δ r d c x = (chi0 δ (bAA x).det)⁻¹ := by
      unfold phiQ; exact if_pos hx
    have hp2 : phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) =
        (chi0 δ (bAA (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F))).det)⁻¹ := by
      unfold phiQ; exact if_pos hs
    have hdet := ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.2.2.1
    have hAd := ((Jset_iff hLF _).1 hx.1).2
    have hadet := ((GlobalTheory.T.parahoric_character_modulus_properties hLF δ hδ r c).2.1 k hk).2.1
    have hAne : (bAA x).det ≠ 0 := fun h => by
      rw [h, map_zero] at hAd; exact zero_ne_one hAd
    have hane : (bAA (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h => by
      rw [h, map_zero] at hadet; exact zero_ne_one hadet
    have h1 := unramifiedCharExt_ne_zero δ hAne
    have h2 := unramifiedCharExt_ne_zero δ hane
    rw [hp1, hp2, hc, hdet]
    field_simp
  · have hinv : k⁻¹ ∈ parJ O ϖ r c := by
      obtain ⟨J, hJ, -⟩ := Par.parJ_compact_open hLF r c
      rw [← hJ] at hk ⊢
      exact J.inv_mem hk
    have hs : ¬ Supp O ϖ (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) := fun h => hx (by
      have := (step hLF δ hδ hinv h).1
      rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this)
    have hp1 : phiQ O ϖ δ r d c x = 0 := by
      unfold phiQ; exact if_neg hx
    have hp2 : phiQ O ϖ δ r d c (x * (k : Matrix (Fin (r + c)) (Fin (r + c)) F)) = 0 := by
      unfold phiQ; exact if_neg hs
    rw [hp1, hp2, mul_zero, mul_zero]
end GlobalTheory.CompanionTheory.QL.Eigen
