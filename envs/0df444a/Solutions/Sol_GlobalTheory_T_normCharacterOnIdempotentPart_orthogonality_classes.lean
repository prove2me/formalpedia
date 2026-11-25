-- Prove2me | solution 1 for GlobalTheory.T.normCharacterOnIdempotentPart_orthogonality_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:32.430291+00:00
-- url     : https://prove2.me/submissions/ca8ecfe2-76f5-46c8-a1db-9fb1a4718772

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartOrthogonalityClasse
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartOrthogonalityClasseStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_chi_ell_cl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ), (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) = (chi B e I x : ℝ) * h I) → ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  first | exact @GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl | exact GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl | (intros; apply GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl <;> assumption)
end _root_.GlobalTheory.T
