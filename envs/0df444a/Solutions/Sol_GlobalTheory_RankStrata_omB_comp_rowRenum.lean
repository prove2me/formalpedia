-- Prove2me | solution 1 for GlobalTheory.RankStrata.omB_comp_rowRenum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:33.653695+00:00
-- url     : https://prove2.me/submissions/5b3991a6-6f50-4347-bcb5-1b16b21d0899

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRows
import Theorems.Thm_GlobalTheory_RankStrata_glRenum_val
import Theorems.Thm_GlobalTheory_RankStrata_gdet_glRenum

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
theorem _root_.solution (ν : kˣ →* ℂˣ) (e : A ≃ A') (g : GL A' k) (Ψ : Matrix A' D k → ℂ) :
    (fun Y : Matrix A D k => GlobalTheory.SplitFlip.omB ν ν g 1 Ψ (Y.submatrix e.symm id)) =
      GlobalTheory.SplitFlip.omB ν ν (glRenum e g) 1 (fun Y : Matrix A D k => Ψ (Y.submatrix e.symm id)) := by
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, gdet_glRenum, Units.val_one, Matrix.mul_one]
  congr 1
  · simp
  · congr 1
    rw [glRenum_val]
    have hY : Y = (Y.submatrix e.symm id).submatrix e id := by ext; simp
    conv_rhs => rw [hY]
    rw [show (g.val.submatrix e e)ᵀ = (g.valᵀ).submatrix e e from rfl, Matrix.submatrix_mul_equiv]
    ext; simp
end GlobalTheory.RankStrata
