-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeNorm.wedge_fromCols_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:55.487144+00:00
-- url     : https://prove2.me/submissions/0023c275-d718-48fa-9b70-eb67e6cf8106

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeSubspaceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeNorm
namespace GlobalTheory.CompanionTheory.WedgeNorm
theorem _root_.solution {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by
  by_cases hX : LinearIndependent K Xᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ X hX
    obtain ⟨h1, h2, -⟩ := hY κ' Z
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)
  · have h0 : N (κ ⊕ κ') (fromCols X Z) = 0 := by
      by_contra hne
      have hli := (h.ne_zero _ _).1 hne
      apply hX
      have hc := hli.comp Sum.inl Sum.inl_injective
      have he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K) := by
        funext i j
        rfl
      rwa [he] at hc
    rw [h0]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)
end GlobalTheory.CompanionTheory.WedgeNorm
