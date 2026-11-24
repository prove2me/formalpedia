-- Prove2me | solution 1 for GlobalTheory.RankStrata.rowRenum_SB_Nsp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:01.316874+00:00
-- url     : https://prove2.me/submissions/1dfe6d24-baac-4cba-b0b8-3dee8df8bbca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Theorems.Thm_GlobalTheory_RankStrata_comp_rowRenum_mem_SB
import Theorems.Thm_GlobalTheory_RankStrata_omB_comp_rowRenum
import Theorems.Thm_GlobalTheory_RankStrata_sub_mem_Nsp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankStrata
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.RankStrata
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (ν : kˣ →* ℂˣ) (e : A ≃ A'),
    (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧
    (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν,
      (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ ν e
  refine ⟨fun f hf => comp_rowRenum_mem_SB e hf, ?_⟩
  let L : (Matrix A' D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun Y : Matrix A D k => Y.submatrix e.symm id)
  have hle : Nsp k A' D ν ≤ (Nsp k A D ν).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    show L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ') ∈ Nsp k A D ν
    rw [map_sub]
    have h1 : L (GlobalTheory.SplitFlip.omB ν ν g 1 Ψ') =
        GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ' (Y.submatrix e.symm id)) :=
      omB_comp_rowRenum ν e g Ψ'
    rw [h1]
    exact sub_mem_Nsp ν (glRenum e g) (comp_rowRenum_mem_SB e hΨ')
  intro f hf
  exact hle hf
end GlobalTheory.RankStrata
