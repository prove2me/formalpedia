-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:36.33326+00:00
-- url     : https://prove2.me/submissions/0bc2b3b4-e92d-4847-9850-f776fda8e7ff

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProd
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_mul__dbb4c9edd927
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_cT_one__83e0e0ceab0f
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_mul__06396bb29280
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_red_one__e5dbbbbc4a56
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_NuDiag_card_range_vecMul_diagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag
private theorem card_range_vecMul_mul_mul_eq_of_mul_eq_one {Q : Type} [CommRing Q] {n : ℕ}
    (H P P' G G' : Matrix (Fin n) (Fin n) Q) (hP : P' * P = 1) (hG : G * G' = 1) :
    Nat.card (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      Nat.card (Set.range fun x : Fin n → Q => Matrix.vecMul x H) := by
  have hinj : Function.Injective fun y : Fin n → Q => Matrix.vecMul y G := by
    intro y₁ y₂ hy
    have h := congrArg (fun v => Matrix.vecMul v G') hy
    simpa only [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one] using h
  have hrange : (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      (fun y => Matrix.vecMul y G) '' Set.range fun x : Fin n → Q => Matrix.vecMul x H := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul z P) H, ⟨Matrix.vecMul z P, rfl⟩,
        by simp only [Matrix.vecMul_vecMul]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Matrix.vecMul x P', by
        simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
  rw [hrange, Nat.card_image_of_injective hinj]
end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
end

set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.NuDiag
namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  intro R _ σ ϖ _ _ k _ n h g g' d hgg' hg'g hdiag
  have hP : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g') *
      PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_mul', hgg',
      GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_one', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hG : PositivityTheory.PfSWUS.Loc.red ϖ k g * PositivityTheory.PfSWUS.Loc.red ϖ k g' = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hgg', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hD : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) * PositivityTheory.PfSWUS.Loc.red ϖ k h *
      PositivityTheory.PfSWUS.Loc.red ϖ k g =
        Matrix.diagonal fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i) := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hdiag]
    simp only [PositivityTheory.PfSWUS.Loc.red]
    exact Matrix.diagonal_map (map_zero _)
  unfold PositivityTheory.PfSWUS.Loc.nuAt
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
    (fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i)))
  rw [← hD]
  exact (card_range_vecMul_mul_mul_eq_of_mul_eq_one _ _ _ _ _ hP hG).symm
end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
