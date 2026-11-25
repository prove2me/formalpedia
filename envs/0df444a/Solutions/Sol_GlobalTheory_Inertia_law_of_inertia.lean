-- Prove2me | solution 1 for GlobalTheory.Inertia.law_of_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:19.788056+00:00
-- url     : https://prove2.me/submissions/fd0bccc3-0c61-46d4-bdca-eed06d73e0a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg_eq_sub
import Theorems.Thm_GlobalTheory_Inertia_posIndex_fromBlocks
import Theorems.Thm_GlobalTheory_Inertia_congr_sgn_iff
import Theorems.Thm_GlobalTheory_Inertia_existsUnique_congr_sgn
import Theorems.Thm_GlobalTheory_Inertia_posIndex_reindex_fromBlocks
import Theorems.Thm_GlobalTheory_Inertia_gram_eq_sgn_iff
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_conjugate
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_data
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
open NumberField
namespace GlobalTheory.Inertia
theorem _root_.solution :
    (∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ), G.IsHermitian → G.det ≠ 0 →
      (∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ∧
      (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
          p = posIndex G) ∧
      (∀ (P : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ), P.det ≠ 0 →
        Pᵀ * G * P.map conj = diagonal d →
          posIndex G = (Finset.univ.filter fun k => 0 < (d k).re).card) ∧
      IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G *ᵥ star x).re} (posIndex G) ∧
      (∀ (s : ℕ) (H : Matrix (Fin s) (Fin s) ℂ), H.IsHermitian →
        posIndex (fromBlocks G 0 0 H) = posIndex G + posIndex H ∧
        posIndex (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G 0 0 H)) =
          posIndex G + posIndex H) ∧
      posIndex (-G) = r - posIndex G) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ),
      (∀ (G : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 →
        ∀ τ : E →+* ℂ,
          (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
            FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
              p = posIndex (G.map τ)) ∧
          posIndex (G.map (ComplexEmbedding.conjugate τ)) = posIndex (G.map τ)) ∧
      ∀ (X : FD.Data E r) (τ : E →+* ℂ), posIndex (X.Gm.map τ) = X.p0 :=
  ⟨fun _ G hG hG0 => ⟨existsUnique_congr_sgn hG hG0, congr_sgn_iff hG hG0,
      fun _ _ hP hd => posIndex_eq_card_of_congr_diagonal hP hd, isGreatest_posIndex G,
      fun _ _ hH => ⟨posIndex_fromBlocks hG hH, posIndex_reindex_fromBlocks hG hH⟩,
      by simpa only [Fintype.card_fin] using posIndex_neg_eq_sub hG hG0⟩,
    fun _ _ _ _ _ => ⟨fun _ hG hG0 τ => ⟨gram_eq_sgn_iff τ hG hG0, posIndex_map_conjugate τ hG⟩,
      posIndex_map_data⟩⟩
end GlobalTheory.Inertia
