-- Prove2me | solution 1 for Hermite1DimdLEAN.blockLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:33.395709+00:00
-- url     : https://prove2.me/submissions/e2031409-0cce-4d7c-a4e1-d4b445d5967e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Theorems.Thm_Hermite1DimdLEAN_productBasisLocalization
public import Theorems.Thm_Hermite1DimdLEAN_annulusParseval
public import Theorems.Thm_Hermite1DimdLEAN_finiteParseval
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (κ : MultiIndex d) :
    ∃ C c B : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ j ℓ : MultiIndex d, ∀ G : FiniteHermiteSum d,
        annulusMass j (evalHermiteSum κ (blockPart ℓ G)) ≤
          C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) *
            hermiteNormSq κ (blockPart ℓ G) := by
  classical
  obtain ⟨C, c, B, hCpos, hcpos, hBnonneg, hloc⟩ := productBasisLocalization (κ := κ)
  refine ⟨C, c, B, hCpos, hcpos, hBnonneg, ?_⟩
  intro j ℓ G
  rw [annulusParseval]
  have hC_nonneg : 0 ≤ C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2) := by
    positivity
  calc
    Finset.sum (blockPart ℓ G).support
        (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α))
      ≤ Finset.sum (blockPart ℓ G).support
          (fun α =>
            ‖(blockPart ℓ G).coeff α‖ ^ 2 *
              (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2))) := by
                refine Finset.sum_le_sum ?_
                intro α hα
                have hblock : α ∈ squareBlock ℓ := by
                  have hsuppnz : (blockPart ℓ G).coeff α ≠ 0 := by
                    simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hα
                  rw [blockPart, Finsupp.onFinset_apply] at hsuppnz
                  simp_all
                exact mul_le_mul_of_nonneg_left (hloc α j ℓ hblock) (by positivity)
    _ =
        (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
          Finset.sum (blockPart ℓ G).support (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2) := by
            calc
              Finset.sum (blockPart ℓ G).support
                  (fun α =>
                    ‖(blockPart ℓ G).coeff α‖ ^ 2 *
                      (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)))
                =
                  Finset.sum (blockPart ℓ G).support
                    (fun α =>
                      (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
                        ‖(blockPart ℓ G).coeff α‖ ^ 2) := by
                          refine Finset.sum_congr rfl ?_
                          intro α hα
                          ring
              _ =
                  (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
                    Finset.sum (blockPart ℓ G).support (fun α => ‖(blockPart ℓ G).coeff α‖ ^ 2) :=
                        by
                      rw [Finset.mul_sum]
    _ =
        (C * Real.exp (-(c) * max (((blockDistance j ℓ : ℕ) : ℝ) - B) 0 ^ 2)) *
          hermiteNormSq κ (blockPart ℓ G) := by rw [← finiteParseval]
end Hermite1DimdLEAN
