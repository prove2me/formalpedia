-- Prove2me | solution 1 for GlobalTheory.Inertia.exists_congr_diagonal_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:18:49.609811+00:00
-- url     : https://prove2.me/submissions/f054b072-0081-439f-8e78-86063ca5a949

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    ∃ (P : Matrix n n ℂ) (d : n → ℝ), P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal (fun k => (d k : ℂ)) ∧ (G.det ≠ 0 → ∀ k, d k ≠ 0) := by
  obtain ⟨P, d, hP, hd, hre, hne⟩ := HermDiag.exists_congr_diagonal (c := starRingEnd ℂ)
    two_ne_zero Complex.conj_conj (G := G) (fun a b => hG.apply b a)
  have h : ∀ k, (((d k).re : ℝ) : ℂ) = d k := fun k => Complex.conj_eq_iff_re.1 (hre k)
  refine ⟨P, fun k => (d k).re, hP, by simpa only [h] using hd, fun hG0 k hk => hne hG0 k ?_⟩
  rw [← h k, show (d k).re = 0 from hk, Complex.ofReal_zero]
end GlobalTheory.Inertia
