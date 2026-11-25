-- Prove2me | solution 1 for GlobalTheory.T.exists_weil_representation_of_lattice_vacua
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:39.640875+00:00
-- url     : https://prove2.me/submissions/1cef1438-c7a0-48d1-93fd-b434ab9b3a95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacua
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsWeilRepresentationOfLatticeVacuaStatement
import Theorems.Thm_GlobalTheory_FinWeil_exists_weil_rep_of_vacua


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) → (∀ g, idx A (A.map (ρ g)) ≠ 0) → ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧ ∀ g, SelfDual γ (A.map (ρ g)) ∧ ∀ e, Fixes W A e → Om g e = normOp lam W A (A.map (ρ g)) e := by
  first | exact @GlobalTheory.FinWeil.exists_weil_rep_of_vacua | exact GlobalTheory.FinWeil.exists_weil_rep_of_vacua | (intros; apply GlobalTheory.FinWeil.exists_weil_rep_of_vacua <;> assumption)
end _root_.GlobalTheory.T
