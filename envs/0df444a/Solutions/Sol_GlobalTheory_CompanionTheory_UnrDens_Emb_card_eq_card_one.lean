-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Emb.card_eq_card_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:24.393441+00:00
-- url     : https://prove2.me/submissions/fe43915a-912a-4b57-bdf5-179a20901541

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_cT_mul_rect
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Emb_cT_one_sq

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
theorem _root_.solution {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (T g : Matrix (Fin n) (Fin n) E)
    (hg : IsUnit g.det) (hgT : cT τ g * T * g = 1) :
    Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} =
      Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} := by
  have hgh : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have hhg : cT τ g⁻¹ * cT τ g = 1 := by rw [← cT_mul_rect, hgh, cT_one_sq]
  have hT : T = cT τ g⁻¹ * g⁻¹ := by
    calc T = (cT τ g⁻¹ * cT τ g) * T * (g * g⁻¹) := by rw [hhg, hgh, Matrix.one_mul, Matrix.mul_one]
      _ = cT τ g⁻¹ * (cT τ g * T * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = cT τ g⁻¹ * g⁻¹ := by rw [hgT, Matrix.mul_one]
  refine Nat.card_congr ⟨fun x => ⟨x.1 * g, ?_⟩, fun y => ⟨y.1 * g⁻¹, ?_⟩, ?_, ?_⟩
  · rw [cT_mul_rect]
    calc cT τ g * cT τ x.1 * S * (x.1 * g) = cT τ g * (cT τ x.1 * S * x.1) * g := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [x.2, hgT]
  · rw [cT_mul_rect]
    calc cT τ g⁻¹ * cT τ y.1 * S * (y.1 * g⁻¹) = cT τ g⁻¹ * (cT τ y.1 * S * y.1) * g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [y.2, Matrix.mul_one, ← hT]
  · intro x
    apply Subtype.ext
    show x.1 * g * g⁻¹ = x.1
    rw [Matrix.mul_assoc, hgh, Matrix.mul_one]
  · intro y
    apply Subtype.ext
    show y.1 * g⁻¹ * g = y.1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.mul_one]
end GlobalTheory.CompanionTheory.UnrDens.Emb
