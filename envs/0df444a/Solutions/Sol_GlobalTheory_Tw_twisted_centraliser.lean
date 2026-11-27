-- Prove2me | solution 1 for GlobalTheory.Tw.twisted_centraliser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:23.424723+00:00
-- url     : https://prove2.me/submissions/2e0da457-b261-4bb9-a6f9-aed971f2225b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_mem_adjoin_of_commute
import Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_semi
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_nrm
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_commute_of_mem
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_adj_adjoin
import Theorems.Thm_GlobalTheory_Tw_CentralizerAdjoin_cent_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory.Tw.CentralizerAdjoin
namespace GlobalTheory.Tw
theorem _root_.solution :
    ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R] [IsArtinianRing R] [IsReduced R] (δ : Matrix (Fin n) (Fin n) R),
      Reg δ → (∀ g h, adj δ (g * h) = adj δ h * adj δ g) ∧ (∀ (c : R) g h, adj δ (c • g + h) = star c • adj δ g + adj δ h) ∧
        adj δ (nrm δ) = (nrm δ)⁻¹ ∧
        (∀ g ∈ Algebra.adjoin R {nrm δ}, adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g) ∧
        (∀ g, g * nrm δ = nrm δ * g ↔ g ∈ Algebra.adjoin R {nrm δ}) ∧
        cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  intro n R _ _ _ _ δ hδ
  exact ⟨adj_mul' hδ.1, adj_semi δ, adj_nrm hδ.1, adj_adjoin hδ.1,
    fun g => ⟨mem_adjoin_of_commute _ g hδ.2, commute_of_mem _ g⟩, cent_eq hδ⟩
end GlobalTheory.Tw
