-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:55.02665+00:00
-- url     : https://prove2.me/submissions/f49ad940-8174-4ddb-bca9-90f231f98769

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_card_eq_card_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_card_one_eq_orthonormal
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_prod_pow_div
import Theorems.Thm_GlobalTheory_T_card_orthonormal_frames_hermitian_space
import Theorems.Thm_GlobalTheory_T_exists_hermitian_congr_to_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Emb
variable {E : Type} [CommRing E] {τ : E →+* E}
namespace GlobalTheory.CompanionTheory.UnrDens.Emb
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ),
    ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E)
    (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det →
    (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) =
      (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro E _ τ q ε hR m n hnm S T hS hSd hT hTd
  obtain ⟨g, hg, hgT⟩ := GlobalTheory.T.exists_hermitian_congr_to_one E τ q ε hR n T hT hTd
  have hcard : Nat.card (Fin m → E) = q ^ (2 * m) := by
    rw [Nat.card_fun, hR.card, Nat.card_eq_fintype_card, Fintype.card_fin, pow_mul]
  have hq : (q : ℝ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  rw [card_eq_card_one S T g hg hgT, card_one_eq_orthonormal hR.inv S hS hSd,
    GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n m hnm (Fin m → E) (HermSp.ofMatrix hR.inv S hS hSd) hcard,
    Finset.prod_mul_distrib, prod_pow_div _ hq n m hnm]
end GlobalTheory.CompanionTheory.UnrDens.Emb
