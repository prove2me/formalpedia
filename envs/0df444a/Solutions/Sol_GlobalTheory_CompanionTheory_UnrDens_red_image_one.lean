-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.red_image_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:17:04.385214+00:00
-- url     : https://prove2.me/submissions/97288efb-0d74-497e-9c30-06fc7e1bd201

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardUnimodularHermitianRepsLevelOne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_cT_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_mul_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_surj_one

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
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ 1 '' {x : Matrix (Fin m) (Fin n) R | red ϖ 1 (cT σ x * S * x) = red ϖ 1 T} =
      {y | cT (barσ σ ϖ h 1) y * red ϖ 1 S * y = red ϖ 1 T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h] at hx
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj_one ϖ y
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨x, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h]
    exact hy
end GlobalTheory.CompanionTheory.UnrDens
