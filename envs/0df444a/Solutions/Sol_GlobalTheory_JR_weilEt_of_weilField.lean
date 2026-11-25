-- Prove2me | solution 1 for GlobalTheory.JR.weilEt_of_weilField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:19.947177+00:00
-- url     : https://prove2.me/submissions/4b1027d7-efc4-4520-a3d0-d27bcca4b34c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepresentationHyperbolicSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationExistsEtaleOfSubsingletonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaKEqNegOneOfNotNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmallerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationEtaleOfQuadraticField
import Theorems.Thm_GlobalTheory_JR_WeilEtProof_weilAt_of_isField
import Theorems.Thm_GlobalTheory_T_exists_etaleInvolutiveAlgebraSplitting_smaller
import Theorems.Thm_GlobalTheory_T_exists_weilRepresentation_hyperbolic_split
import Theorems.Thm_GlobalTheory_T_weilRepresentationExistsEtale_of_subsingleton
import Theorems.Thm_GlobalTheory_T_weil_condition_product_splitting


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory.JR.WeilEtProof
namespace GlobalTheory.JR
theorem _root_.solution : WeilField → WeilEt := by
  intro hF F E _ _ _ _ _ A ψ hψ x μ hμ
  suffices h : ∀ (n : ℕ) (A : Et F E), Module.finrank F A.K = n → WeilAt A from h _ A rfl ψ hψ x μ hμ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn
    rcases subsingleton_or_nontrivial A.K with hs | hnt
    · exact GlobalTheory.T.weilRepresentationExistsEtale_of_subsingleton F E A hs
    by_cases hK : IsField A.K
    · by_cases hL : IsField A.L
      · exact weilAt_of_isField hF F E A hK hL
      · intro ψ hψ x μ hμ
        obtain ⟨W, hW⟩ := GlobalTheory.T.exists_weilRepresentation_hyperbolic_split F E A ψ hψ hK hL x μ hμ
        exact ⟨1, W, hW⟩
    · obtain ⟨A₁, A₂, eK, eL, hs, h₁, h₂⟩ := GlobalTheory.T.exists_etaleInvolutiveAlgebraSplitting_smaller F E A hnt hK
      exact GlobalTheory.T.weil_condition_product_splitting F E A A₁ A₂ eK eL hs (ih _ (hn ▸ h₁) A₁ rfl) (ih _ (hn ▸ h₂) A₂ rfl)
end GlobalTheory.JR
