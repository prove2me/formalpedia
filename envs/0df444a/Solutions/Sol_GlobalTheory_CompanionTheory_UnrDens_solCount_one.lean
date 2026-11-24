-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.solCount_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:22.4618+00:00
-- url     : https://prove2.me/submissions/bc8594ab-7524-4a38-9ceb-d3814c73eb8c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardUnimodularHermitianRepsLevelOne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_cT_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_isUnit_det_red_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_image_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_resAlg_of_isUnrQuad
import Theorems.Thm_GlobalTheory_T_card_hermitian_representations_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hS' : cT σ S = S ∧ IsUnit S.det := hS
  have hT' : cT σ T = T ∧ IsUnit T.det := hT
  have h1 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 S) = red ϖ 1 S := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hS'.1]
  have h2 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 T) = red ϖ 1 T := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hT'.1]
  unfold solCount
  rw [red_image_one σ ϖ hR.fix_ϖ S T]
  exact GlobalTheory.T.card_hermitian_representations_residue (R ⧸ lev ϖ 1) (barσ σ ϖ hR.fix_ϖ 1) q ε
    (resAlg_of_isUnrQuad R σ ϖ q ε hR) m n hnm (red ϖ 1 S) (red ϖ 1 T) h1
    (isUnit_det_red_one ϖ S hS'.2) h2 (isUnit_det_red_one ϖ T hT'.2)
end GlobalTheory.CompanionTheory.UnrDens
