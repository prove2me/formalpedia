-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.lift_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:25.086451+00:00
-- url     : https://prove2.me/submissions/163aaa81-4c2e-42ec-af63-a91b5f5e6cc8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_smul_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_gram_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
variable {R : Type} [CommRing R] {a b c : ℕ}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hf : σ ϖ = ϖ) (hr : IsSMulRegular R ϖ) {k : ℕ} (hk : 1 ≤ k)
    (S : Matrix (Fin a) (Fin a) R) (T H : Matrix (Fin b) (Fin b) R)
    (x y : Matrix (Fin a) (Fin b) R) (hH : cT σ x * S * x + ϖ ^ k • H = T) :
    red ϖ (k + 1) (cT σ (x + ϖ ^ k • y) * S * (x + ϖ ^ k • y)) = red ϖ (k + 1) T ↔
      red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 H := by
  have hc : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hf]
  have hq : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = 0 := by
    have : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = red ϖ (k + 1) 0 := by
      refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • (cT σ y * S * y), ?_⟩
      rw [smul_smul, zero_add, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [this]
    ext i j; simp [red]
  rw [gram_expand σ hc, red_add, hq, add_zero, ← hH, red_add, red_add]
  rw [add_right_inj, red_smul_iff hr]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
