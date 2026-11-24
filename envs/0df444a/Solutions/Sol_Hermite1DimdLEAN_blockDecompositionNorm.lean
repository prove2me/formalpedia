-- Prove2me | solution 1 for Hermite1DimdLEAN.blockDecompositionNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:51.155193+00:00
-- url     : https://prove2.me/submissions/a47163c9-5ed6-45bd-84b1-771ac9f97171

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Theorems.Thm_Hermite1DimdLEAN_finiteParseval
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma mem_squareBlock_iff_blockIndexMulti_eq
    {d : ℕ} (α ℓ : MultiIndex d) :
    α ∈ squareBlock ℓ ↔ blockIndexMulti α = ℓ := by
  constructor
  · intro h
    funext q
    have hq : α q ∈ HermiteLEAN.squareBlock (ℓ q) := h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico] at hq
    exact ((Nat.eq_sqrt).2 (by simpa [Nat.pow_two] using hq)).symm
  · intro h q
    rw [HermiteLEAN.squareBlock, Finset.mem_Ico]
    have hq : Nat.sqrt (α q) = ℓ q := by
      simpa [blockIndexMulti, HermiteLEAN.blockIndex] using congrArg (fun f => f q) h
    exact by simpa [Nat.pow_two] using (Nat.eq_sqrt).1 hq.symm
private lemma blockPart_support_eq_filter
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ : MultiIndex d) :
    (blockPart ℓ G).support = G.support.filter (fun α => blockIndexMulti α = ℓ) := by
  ext α
  simp [FiniteHermiteSum.support, blockPart, Finsupp.mem_support_iff,
    mem_squareBlock_iff_blockIndexMulti_eq, and_comm]
private lemma blockwise_regroup
    {d : ℕ} (G : FiniteHermiteSum d) (w : MultiIndex d → ℝ) :
    ∑ ℓ ∈ G.support.image blockIndexMulti,
        ∑ α ∈ (blockPart ℓ G).support, ‖(blockPart ℓ G).coeff α‖ ^ 2 * w α =
      ∑ α ∈ G.support, ‖G.coeff α‖ ^ 2 * w α := by
  classical
  have hterm :
      ∀ ℓ ∈ G.support.image blockIndexMulti,
        ∑ α ∈ (blockPart ℓ G).support, ‖(blockPart ℓ G).coeff α‖ ^ 2 * w α =
          ∑ α ∈ G.support.filter (fun α => blockIndexMulti α = ℓ), ‖G.coeff α‖ ^ 2 * w α := by
    intro ℓ _
    rw [blockPart_support_eq_filter]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hblock : blockIndexMulti α = ℓ := (Finset.mem_filter.mp hα).2
    have hsq : α ∈ squareBlock ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mpr hblock
    simp [blockPart, Finsupp.onFinset_apply, hsq]
  rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_true_of_mem fun α hα => ?_
  exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
private lemma blockPart_coeff_eq_zero_of_not_mem_support_image
    {d : ℕ} (G : FiniteHermiteSum d) (ℓ α : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    (blockPart ℓ G).coeff α = 0 := by
  by_cases hb : α ∈ squareBlock ℓ
  · have hidx : blockIndexMulti α = ℓ := (mem_squareBlock_iff_blockIndexMulti_eq α ℓ).mp hb
    by_cases hsupp : α ∈ G.support
    · exact absurd (Finset.mem_image.mpr ⟨α, hsupp, hidx⟩) hℓ
    · have hcoeff : G.coeff α = 0 := by
        simpa [FiniteHermiteSum.support, Finsupp.mem_support_iff] using hsupp
      simp [blockPart, Finsupp.onFinset_apply, hb, hcoeff]
  · simp [blockPart, Finsupp.onFinset_apply, hb]
private lemma hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) (ℓ : MultiIndex d)
    (hℓ : ℓ ∉ G.support.image blockIndexMulti) :
    hermiteNormSq κ (blockPart ℓ G) = 0 := by
  rw [finiteParseval]
  refine Finset.sum_eq_zero fun α _ => ?_
  simp [blockPart_coeff_eq_zero_of_not_mem_support_image G ℓ α hℓ]
private lemma tsum_hermiteNormSq_blockPart_eq_sum_support_image
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) =
      Finset.sum (G.support.image blockIndexMulti) (fun ℓ => hermiteNormSq κ (blockPart ℓ G)) :=
  tsum_eq_sum
    (fun ℓ hℓ => hermiteNormSq_blockPart_eq_zero_of_not_mem_support_image κ G ℓ hℓ)
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = ∑' ℓ : MultiIndex d, hermiteNormSq κ (blockPart ℓ G) := by
  /-
  Scaffolding guidance:
  the block decomposition is the quantitative backbone for both local windows
  and leakage. Keep it exported in norm-squared form.
  -/
  classical
  rw [tsum_hermiteNormSq_blockPart_eq_sum_support_image (κ := κ), finiteParseval]
  simp_rw [finiteParseval]
  have hkey := blockwise_regroup G (fun _ => 1)
  simp_all
end Hermite1DimdLEAN
