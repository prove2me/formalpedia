-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.solCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:22.133346+00:00
-- url     : https://prove2.me/submissions/c4d5a4b3-e4ed-407f-82b0-82c12039c638

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_one
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_one
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_cT_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gr_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_solCount_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T g h : Matrix (Fin n) (Fin n) R) (k : ℕ) (hgh : red ϖ k (g * h) = 1) (hhg : red ϖ k (h * g) = 1) :
    solCount σ ϖ S (cT σ g * T * g) k = solCount σ ϖ S T k := by
  have hc : red ϖ k (cT σ (g * h)) = 1 := by
    have h1 : red ϖ k (g * h) = red ϖ k 1 := by rw [hgh, red_one]
    rw [red_cT_congr hσ k h1, cT_one, red_one]
  have himg : sol σ ϖ S (cT σ g * T * g) k = (fun y => y * red ϖ k g) '' sol σ ϖ S T k := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨red ϖ k (x * h), ⟨x * h, ?_, rfl⟩, ?_⟩
      · have hx' : red ϖ k (gr σ S x) = red ϖ k (cT σ g * T * g) := hx
        show red ϖ k (gr σ S (x * h)) = red ϖ k T
        rw [gr_mul, red_mul, red_mul, hx', red_mul, red_mul]
        rw [cT_mul, red_mul] at hc
        rw [red_mul] at hgh
        calc red ϖ k (cT σ h) * (red ϖ k (cT σ g) * red ϖ k T * red ϖ k g) * red ϖ k h
            = (red ϖ k (cT σ h) * red ϖ k (cT σ g)) * red ϖ k T * (red ϖ k g * red ϖ k h) := by
              simp only [Matrix.mul_assoc]
          _ = red ϖ k T := by rw [hc, hgh, Matrix.one_mul, Matrix.mul_one]
      · show red ϖ k (x * h) * red ϖ k g = red ϖ k x
        rw [red_mul, Matrix.mul_assoc, ← red_mul ϖ k h g, hhg, Matrix.mul_one]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : red ϖ k (gr σ S x) = red ϖ k T := hx
      refine ⟨x * g, ?_, red_mul _ _ _ _⟩
      show red ϖ k (gr σ S (x * g)) = red ϖ k (cT σ g * T * g)
      rw [gr_mul, red_mul, red_mul, hx', red_mul, red_mul]
  have hinj : Function.Injective (fun y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k) => y * red ϖ k g) := by
    intro y y' hyy
    have h2 : y * red ϖ k g * red ϖ k h = y' * red ϖ k g * red ϖ k h := by
      simp only at hyy
      rw [hyy]
    rw [red_mul] at hgh
    simpa [Matrix.mul_assoc, hgh] using h2
  rw [solCount_eq, solCount_eq, himg]
  exact Nat.card_image_of_injective hinj _
end GlobalTheory.CompanionTheory.LocalDens
