-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.fibre_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:23.142097+00:00
-- url     : https://prove2.me/submissions/b44f470f-4182-43c7-8c98-6fa119472e04

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_card_eq_of_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_add
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_smul_cancel
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_smul_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_lift_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_diff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_cT_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_card_fibre_gram_differential
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_resAlg_of_isUnrQuad
import Theorems.Thm_GlobalTheory_GramCount_Prim_map


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
variable {σ : R →+* R} {ϖ : R}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {m n : ℕ} (hnm : n ≤ m)
    {S : Matrix (Fin m) (Fin m) R} {T : Matrix (Fin n) (Fin n) R} (hS : IsUnimod σ S)
    (hT : IsUnimod σ T) {k : ℕ} (hk : 1 ≤ k) {x : Matrix (Fin m) (Fin n) R}
    (hx : x ∈ solSet σ ϖ S T k) (s : red ϖ k '' solSet σ ϖ S T k) (hs : s.1 = red ϖ k x) :
    Nat.card {t // down σ ϖ S T k t = s} = q ^ (2 * m * n - n ^ 2) := by
  obtain ⟨D, hD⟩ := (red_eq_iff _ _ _ _).1 hx
  have hH : cT σ x * S * x + ϖ ^ k • (-D) = T := by
    rw [hD, smul_neg]; abel
  have hG : cT σ (cT σ x * S * x) = cT σ x * S * x := by
    rw [cT_mul, cT_mul, cT_cT σ h.inv, hS.1, Matrix.mul_assoc]
  have hherm : cT σ (-D) = -D := by
    apply smul_cancel h.reg k
    have h1 := congrArg (cT σ) hH
    rw [cT_add, cT_smul, map_pow, h.fix_ϖ, hG, hT.1] at h1
    exact add_left_cancel (h1.trans hH.symm)
  have hf := h.fix_ϖ
  have hgram : cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 x = red ϖ 1 T := by
    rw [← red_cT σ ϖ hf, ← red_mul, ← red_mul]
    refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • D, ?_⟩
    rw [hD, smul_smul, ← pow_add]
    congr 3
    omega
  have hdet : IsUnit (red ϖ 1 T).det := by
    have h1 := hT.2.map (Ideal.Quotient.mk (lev ϖ 1))
    rw [RingHom.map_det] at h1
    exact h1
  have hcard := GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential _ (barσ σ ϖ hf 1) q ε (GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad R σ ϖ q ε h) m n hnm
    (red ϖ 1 S) (red ϖ 1 T) (red ϖ 1 x) (red ϖ 1 (-D))
    (by rw [← red_cT σ ϖ hf, hS.1]) (by rw [← red_cT σ ϖ hf, hT.1]) hdet hgram
    (by rw [← red_cT σ ϖ hf, hherm])
  rw [← hcard]
  symm
  let W := {y : Matrix (Fin m) (Fin n) R //
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 (-D)}
  refine card_eq_of_surj (W := W)
    (fun w => ⟨red ϖ 1 w.1, by rw [← red_diff hf]; exact w.2⟩)
    (fun w => ⟨⟨red ϖ (k + 1) (x + ϖ ^ k • w.1), x + ϖ ^ k • w.1,
        (lift_iff hf h.reg hk S T (-D) x w.1 hH).2 w.2, rfl⟩, Subtype.ext (by
          show proj ϖ k (red ϖ (k + 1) (x + ϖ ^ k • w.1)) = s.1
          rw [proj_red, hs]
          exact (red_eq_iff _ _ _ _).2 ⟨w.1, rfl⟩)⟩) ?_ ?_ ?_
  · rintro ⟨ybar, hy⟩
    obtain ⟨y, rfl⟩ := red_surjective ϖ 1 ybar
    exact ⟨⟨y, by rw [red_diff hf]; exact hy⟩, rfl⟩
  · rintro ⟨⟨t, x', hx', rfl⟩, ht⟩
    have h1 : red ϖ k x' = red ϖ k x := by
      have h2 : proj ϖ k (red ϖ (k + 1) x') = s.1 := congrArg Subtype.val ht
      rwa [proj_red, hs] at h2
    obtain ⟨y, rfl⟩ := (red_eq_iff _ _ _ _).1 h1
    exact ⟨⟨y, (lift_iff hf h.reg hk S T (-D) x y hH).1 hx'⟩, rfl⟩
  · intro w w'
    rw [Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
    show red ϖ 1 w.1 = red ϖ 1 w'.1 ↔
      red ϖ (k + 1) (x + ϖ ^ k • w.1) = red ϖ (k + 1) (x + ϖ ^ k • w'.1)
    rw [red_add, red_add, add_right_inj, red_smul_iff h.reg]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
